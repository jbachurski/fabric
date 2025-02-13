open Core
open Lang.Sym
open Sup

type fabric_arrow = { records : Lang.Fabric.Type.dir Label.Map.t }

module FabricTypeSystem :
  TypeSystem
    with type 'a typ = 'a Lang.Fabric.Type.typ
     and type arrow = fabric_arrow = struct
  open Lang.Fabric.Type

  type nonrec 'a typ = 'a typ [@@deriving sexp, equal, compare]
  type simple = t
  type arrow = fabric_arrow

  let pretty = pretty'
  let map = map
  let unwrap (T t) = t

  let field_decompose sexp ((lower, upper) : 'a Field.t * 'a Field.t) :
      ('a * 'a) list Or_error.t =
    match (lower, upper) with
    | Bot, _ | _, Top | Absent, Absent -> Ok []
    | Present t, Present t' -> Ok [ (t, t') ]
    | (Absent | Top), Present _
    | (Present _ | Top), Absent
    | (Absent | Present _ | Top), Bot ->
        let lower = Field.sexp_of_t sexp lower
        and upper = Field.sexp_of_t sexp upper in
        error_s
          [%message
            "Incompatible record fields" (lower : Sexp.t) (upper : Sexp.t)]

  let field_combine ~tops ~bots ~unrelated f (fd : 'a Field.t)
      (fd' : 'a Field.t) : 'a Field.t =
    match (fd, fd') with
    | Top, t | t, Top -> tops t
    | Bot, t | t, Bot -> bots t
    | Absent, Absent -> Absent
    | Present t, Present t' -> Present (f t t')
    | _ -> unrelated

  let field_join f fd fd' =
    field_combine
      ~tops:(fun _ -> Top)
      ~bots:(fun t -> t)
      ~unrelated:Top f fd fd'

  let field_meet f fd fd' =
    field_combine
      ~tops:(fun t -> t)
      ~bots:(fun _ -> Bot)
      ~unrelated:Bot f fd fd'

  let decompose sexp ((lower : 'a typ), (upper : 'a typ)) :
      ('a * 'a) list Or_error.t =
    match (lower, upper) with
    | _, Top | Bot, _ | Int, Int | Float, Float -> Ok []
    | Tuple ts, Tuple ts' -> (
        match List.zip ts ts' with
        | Ok ts'' -> Ok ts''
        | Unequal_lengths -> error_s [%message "Tuples of different arities"])
    | Function (s, t), Function (s', t') -> Ok [ (t, t'); (s', s) ]
    | Array t, Array t' -> Ok [ (t, t') ]
    | Record fs, Record fs' ->
        Fields.subs fs fs' |> Map.to_alist
        |> List.map ~f:(fun (_, (f, f')) -> field_decompose sexp (f, f'))
        |> Or_error.all
        |> Or_error.map ~f:List.concat
    | _ ->
        let lower = sexp_of_typ sexp lower and upper = sexp_of_typ sexp upper in
        error_s
          [%message "Incompatible types" (lower : Sexp.t) (upper : Sexp.t)]

  let is_top sexp (t : 'a typ) =
    match t with
    | Top -> Ok []
    | _ ->
        let t = sexp_of_typ sexp t in
        error_s [%message "Expected top type" (t : Sexp.t)]

  let is_bot sexp (t : 'a typ) =
    match t with
    | Bot -> Ok []
    | _ ->
        let t = sexp_of_typ sexp t in
        error_s [%message "Expected bottom type" (t : Sexp.t)]

  let top = Top
  let bot = Bot

  let combine ~tops ~bots ~unrelated f f' f_fd (t : 'a typ) (t' : 'a typ) :
      'a typ =
    match (t, t') with
    | Top, t | t, Top -> tops t
    | Bot, t | t, Bot -> bots t
    | Int, Int -> Int
    | Float, Float -> Float
    | Tuple ts, Tuple ts' when List.length ts = List.length ts' ->
        Tuple (List.map2_exn ~f ts ts')
    | Function (t1, t1'), Function (t2, t2') -> Function (f' t1 t2, f t1' t2')
    (* FIXME: array covariance? *)
    | Array t, Array t' -> Array (f t t')
    | Record fs, Record fs' -> Record (Fields.lift f_fd fs fs')
    | _ -> unrelated

  let join f t t' =
    combine
      ~tops:(fun _ -> Top)
      ~bots:(fun t -> t)
      ~unrelated:Top f.join f.meet (field_join f.join) t t'

  let meet f t t' =
    combine
      ~tops:(fun t -> t)
      ~bots:(fun _ -> Bot)
      ~unrelated:Bot f.meet f.join (field_meet f.meet) t t'

  let%expect_test "Fabric type lattice" =
    let rec meet' (T t) (T t') = T (meet lattice t t')
    and join' (T t) (T t') = T (join lattice t t')
    and lattice = { meet = meet'; join = join' } in
    let join = join lattice and meet = meet lattice in
    let print t = print_s (Lang.Fabric.Type.pretty t) in
    print (T Int);
    [%expect {| int |}];
    print (T (join Int Float));
    [%expect {| top |}];
    let rcd k v = Record (Fields.open_ Label.(Map.singleton (of_string k) v)) in
    print (T (meet (rcd "foo" (Present (T Int))) (rcd "bar" (Present (T Int)))));
    [%expect {| ({ (bar int) (foo int) | ? }) |}];
    print
      (T
         (meet
            (Record
               (Label.Map.of_alist_exn
                  [
                    (Label.of_string "foo", Field.Top);
                    (Label.of_string "bar", Present (T Int));
                  ]
               |> Fields.closed))
            (rcd "foo" (Present (T Int)))));
    [%expect {| ({ (bar int) (foo int) }) |}];
    ()

  module Arrow = struct
    open Lang.Fabric.Type

    type t = fabric_arrow = { records : dir Label.Map.t }
    [@@deriving sexp, equal, compare]

    let pretty { records } =
      let drops, lifts =
        Map.partition_map records ~f:(function
          | Top -> First ()
          | Bot -> Second ())
      in

      Sexp.List
        (List.concat
           [
             (if Map.is_empty drops then []
              else
                [ Sexp.Atom "drop"; Label.Set.(of_map_keys drops |> sexp_of_t) ]);
             (if Map.is_empty lifts then []
              else [ Atom "lift"; Label.Set.(of_map_keys lifts |> sexp_of_t) ]);
           ])

    let id = { records = Label.Map.empty }
    let is_id { records } = Map.is_empty records

    let compose { records } { records = records' } =
      {
        records =
          Map.merge records records' ~f:(fun ~key:_ -> function
            | `Left t | `Right t | `Both (t, _) -> Some t);
      }

    let apply { records } = function
      | Record fs ->
          Record
            (Map.fold records ~init:fs ~f:(fun ~key:l ~data fs ->
                 Fields.update fs l (match data with Top -> Top | Bot -> Bot)))
      | t -> t

    let left_adjoint { records } =
      {
        records =
          Map.map records ~f:(function
            | Top -> (Bot : dir)
            | Bot -> failwith "No left adjoint for field morphism to Bot");
      }

    let right_adjoint { records } =
      {
        records =
          Map.map records ~f:(function
            | Bot -> (Top : dir)
            | Top -> failwith "No right adjoint for field morphism to Top");
      }
  end
end

module FabricTypeSystem1 :
  TypeSystem1
    with type 'a typ = 'a Lang.Fabric.Type.typ
     and type arrow = fabric_arrow = struct
  include FabricTypeSystem

  let join_token = "|"
  and meet_token = "&"
end

module FabricCNF = CNF (FabricTypeSystem1)
module FabricDNF = DNF (FabricTypeSystem1)

let fabric_cnf_to_dnf t =
  let open FabricDNF in
  FabricCNF.interpret ~top ~bot ~typ ~var ~join ~meet ~negate ~apply t

let fabric_dnf_to_cnf t =
  let open FabricCNF in
  FabricDNF.interpret ~top ~bot ~typ ~var ~join ~meet ~negate ~apply t

let%expect_test "DNF" =
  let open FabricDNF in
  let var x = var (Type_var.of_string x) in
  let ( + ) = join and ( * ) = meet and ( ! ) = negate in
  let sexp_of_t = pretty in
  let a = var "a" and b = var "b" and c = var "c" in
  print_s [%message (a : t)];
  [%expect {| (a a) |}];
  print_s [%message (a |> negate : t)];
  [%expect {| ("a |> negate" (~ a)) |}];
  print_s [%message (!(a + b) : t)];
  [%expect {| ("!(a + b)" (& (~ a) (~ b))) |}];
  print_s [%message (!(a + top) : t)];
  [%expect {| ("!(a + top)" bot) |}];
  print_s [%message ((a + b) * (b + c) * (c + a) : t)];
  print_s [%message ((a * b) + (b * c) + (c * a) : t)];
  [%expect
    {|
  ("((a + b) * (b + c)) * (c + a)" (| (& a b) (& a c) (& b c)))
  ("((a * b) + (b * c)) + (c * a)" (| (& a b) (& a c) (& b c)))
  |}];
  print_s [%message (meet (typ Int) (typ Float) : t)];
  [%expect {| ("meet (typ Int) (typ Float)" bot) |}];
  print_s [%message (join (typ Int) (typ Float) : t)];
  [%expect {| ("join (typ Int) (typ Float)" top) |}];
  let rcd ?(closed = false) kvs =
    typ
      Lang.Fabric.Type.(
        Record
          (List.map kvs ~f:(fun (k, v) -> (Label.of_string k, v))
          |> Label.Map.of_alist_exn
          |> if closed then Fields.closed else Fields.open_))
  in
  print_s
    [%sexp
      (meet
         (rcd [ ("foo", Present (typ Int)) ])
         (rcd ~closed:true [ ("foo", Top); ("bar", Present (typ Int)) ])
        : t)];
  [%expect {| ({ (bar int) (foo int) }) |}]

let%expect_test "CNF" =
  let open FabricCNF in
  let var x = var (Type_var.of_string x) in
  let ( + ) = join and ( * ) = meet and ( ! ) = negate in
  let sexp_of_t = pretty in
  let a = var "a" and b = var "b" and c = var "c" in
  print_s [%message (a : t)];
  [%expect {| (a a) |}];
  print_s [%message (a |> negate : t)];
  [%expect {| ("a |> negate" (~ a)) |}];
  print_s [%message (!(a + b) : t)];
  [%expect {| ("!(a + b)" (& (~ a) (~ b))) |}];
  print_s [%message (!(a + top) : t)];
  [%expect {| ("!(a + top)" bot) |}];
  print_s [%message ((a + b) * (b + c) * (c + a) : t)];
  print_s [%message ((a * b) + (b * c) + (c * a) : t)];
  [%expect
    {|
    ("((a + b) * (b + c)) * (c + a)" (& (| a b) (| a c) (| b c)))
    ("((a * b) + (b * c)) + (c * a)" (& (| a b) (| a c) (| b c)))
    |}];
  print_s [%message (meet (typ Int) (typ Float) : t)];
  [%expect {| ("meet (typ Int) (typ Float)" bot) |}];
  print_s [%message (join (typ Int) (typ Float) : t)];
  [%expect {| ("join (typ Int) (typ Float)" top) |}];
  let rcd ?(closed = false) kvs =
    typ
      Lang.Fabric.Type.(
        Record
          (List.map kvs ~f:(fun (k, v) -> (Label.of_string k, v))
          |> Label.Map.of_alist_exn
          |> if closed then Fields.closed else Fields.open_))
  in
  print_s
    [%sexp
      (meet
         (rcd [ ("foo", Present (typ Int)) ])
         (rcd ~closed:true [ ("foo", Top); ("bar", Present (typ Int)) ])
        : t)];
  [%expect {| ({ (bar int) (foo int) }) |}];
  print_s
    [%sexp
      (FabricDNF.meet
         (rcd [ ("foo", Present (typ Int)) ] |> fabric_cnf_to_dnf)
         (rcd ~closed:true [ ("foo", Top); ("bar", Present (typ Int)) ]
         |> fabric_cnf_to_dnf)
       |> fabric_dnf_to_cnf
        : t)];
  [%expect {| ({ (bar int) (foo int) }) |}]

let%expect_test "NF duality" =
  let var x = FabricDNF.var (Type_var.of_string x) in
  let xor t t' = FabricDNF.(join (meet t (negate t')) (meet (negate t) t')) in
  let test t =
    print_s (t |> FabricDNF.pretty);
    print_s (fabric_dnf_to_cnf t |> FabricCNF.pretty);
    print_s (fabric_cnf_to_dnf (fabric_dnf_to_cnf t) |> FabricDNF.pretty)
  in
  test (xor (var "x") (xor (var "y") (var "z")));
  [%expect
    {|
    (| (& x y z) (& x (~ y) (~ z)) (& (~ x) y (~ z)) (& (~ x) (~ y) z))
    (& (| x y z) (| x (~ y) (~ z)) (| (~ x) y (~ z)) (| (~ x) (~ y) z))
    (| (& x y z) (& x (~ y) (~ z)) (& (~ x) y (~ z)) (& (~ x) (~ y) z))
    |}];
  test
    (xor
       (FabricDNF.join (var "x") (var "y"))
       (FabricDNF.meet (var "y") (var "z")));
  [%expect
    {|
    (| (& x (~ y)) (& x (~ z)) (& y (~ z)))
    (& (| x y) (| x (~ z)) (| (~ y) (~ z)))
    (| (& x (~ y)) (& x (~ z)) (& y (~ z)))
    |}]

module FabricTyper = struct
  module Type = Type (FabricTypeSystem)
  module Constrained = Constrained (FabricTypeSystem)
  module Field = Lang.Fabric.Type.Field
  module Fields = Lang.Fabric.Type.Fields
  module Solver = Solver (FabricTypeSystem)
  open Lang.Fabric.Expr
  open Type

  let all_in_field (fd : _ Lang.Fabric.Type.Field.t) =
    match fd with
    | Top -> Constrained.wrap (Field.Top, Constraint.truth)
    | Bot -> Constrained.wrap (Field.Bot, Constraint.truth)
    | Absent -> Constrained.wrap (Field.Absent, Constraint.truth)
    | Present t ->
        let t, c = Constrained.unwrap t in
        Constrained.wrap (Field.Present t, c)

  let rec alg_of_typ (Lang.Fabric.Type.T t) =
    typ (Lang.Fabric.Type.map ~f:alg_of_typ t)

  let rec pat : pattern -> ((Var.t * Alg.t) list * Alg.t) Constrained.t =
    let open Constrained in
    function
    | Atom (x, t) ->
        let$ x_ = () in
        let* () = x_ <: alg_of_typ t in
        return ([ (Var.of_string x, x_) ], x_)
    | List ps ->
        let* rs = all (List.map ~f:pat ps) in
        let xs = List.concat_map ~f:fst rs in
        let ps = List.map ~f:snd rs in
        return (xs, typ (Tuple ps))

  let push xs (env : _ Var.Map.t) =
    List.fold xs ~init:env ~f:(fun env (x, x_) ->
        Map.add_exn ~key:x ~data:x_ env)

  let rec go (env : Alg.t Var.Map.t) : t -> Alg.t Constrained.t =
    let open Constrained in
    let return_typ (t : Alg.t Lang.Fabric.Type.typ) = return (typ t) in
    let field_drop l =
      { records = Label.Map.singleton l (Top : Lang.Fabric.Type.dir) }
    in
    function
    | Var (x, _) -> return (Map.find_exn env (Var.of_string x))
    | Lit _ -> return_typ Int
    | Let (p, e, e') ->
        let* xs, t = pat p in
        let* e = go env e in
        let* () = e <: t in
        go (push xs env) e'
    | Fun (p, e) ->
        let* xs, t = pat p in
        let* e = go (push xs env) e in
        return_typ (Function (t, e))
    | Tuple ts ->
        let* ts = all (List.map ~f:(go env) ts) in
        return_typ (Tuple ts)
    | Cons fs ->
        let* fs =
          all_in_map
            (fs
            |> List.map ~f:(fun (l, e) -> (Label.of_string l, e))
            |> Label.Map.of_alist_exn
            |> Map.map ~f:(fun e -> Field.Present (go env e))
            |> Map.map ~f:all_in_field)
        in
        return_typ (Record (Lang.Fabric.Type.Fields.closed fs))
    | Proj (e, f) ->
        let$ f_ = () in
        let* e = go env e in
        let* () =
          e
          <: typ
               (Record
                  (Label.Map.singleton (Label.of_string f) (Field.Present f_)
                  |> Fields.open_))
        in
        return f_
    | Restrict (e, f) ->
        let f = Label.of_string f in
        let$ r = () in
        let* e = go env e in
        let field fd = Label.Map.singleton f fd in
        let* () = r <: apply (field_drop f) e
        and* () = r <: typ (Record (field Field.Absent |> Fields.open_)) in
        return r
    | Extend (f, e, e') ->
        let f = Label.of_string f in
        let$ r = () in
        let* e = go env e and* e' = go env e' in
        let field fd = Label.Map.singleton f fd in
        let* () = e' <: typ (Record (field Field.Absent |> Fields.open_))
        and* () = r <: apply (field_drop f) e'
        and* () = r <: typ (Record (field (Field.Present e) |> Fields.open_)) in
        return r
    | Op (e, "", e') ->
        let$ arg = () in
        let$ res = () in
        let* e = go env e and* e' = go env e' in
        let* () = e <: typ (Function (arg, res)) and* () = e' <: arg in
        return res
    | Op (e, ("+" | "-" | "*" | "/"), e') ->
        let* e = go env e in
        let* e' = go env e' in
        let* () = e <: typ Int and* () = e' <: typ Int in
        return_typ Int
    | Array _ -> failwith "TypeExpr.go: Array"
    | Idx _ -> failwith "TypeExpr.go: Idx"
    | Shape _ -> failwith "TypeExpr.go: Shape"
    | Intrinsic _ -> failwith "TypeExpr.go: Intrinsic"
    | Closure _ -> failwith "TypeExpr.go: Closure"
    | Op (_, o, _) -> failwith ("TypeExpr.go: Op " ^ o)
end

let%expect_test "" =
  let test e =
    let open FabricTyper in
    let t, c = Constrained.unwrap (go Var.Map.empty e) in
    let c = Constraint.simp c in
    print_s [%message (t : Type.Alg.t)];
    print_s [%message (c : Type.Alg.t Constraint.t)];
    let bounds = Solver.run c in
    let prettify =
      Or_error.map
        ~f:
          (Map.map ~f:(fun (lower, upper) ->
               (Type.DNF.pretty lower, Type.CNF.pretty upper)))
    in
    print_s
      [%message (prettify bounds : (Sexp.t * Sexp.t) Type_var.Map.t Or_error.t)]
  in
  test (Proj (Cons [ ("foo", Lit 5); ("bar", Tuple [ Lit 1; Lit 2 ]) ], "foo"));
  [%expect
    {|
    (t (Var $1))
    (c
     (With $1
      (Flow
       (sub
        (Typ
         (Record
          ((m
            ((bar (Present (Typ (Tuple ((Typ Int) (Typ Int))))))
             (foo (Present (Typ Int)))))
           (rest Absent)))))
       (sup (Typ (Record ((m ((foo (Present (Var $1))))) (rest Top))))))))
    ("prettify bounds" (Ok (($1 (int top)))))
    |}];
  test
    (Fun
       ( Atom ("x", T Top),
         Fun (Atom ("y", T Top), Op (Var ("x", T Top), "+", Var ("y", T Top)))
       ));
  [%expect
    {|
    (t (Typ (Function (Var $2) (Typ (Function (Var $3) (Typ Int))))))
    (c
     (All
      ((With $2 (Flow (sub (Var $2)) (sup (Typ Top))))
       (With $3 (Flow (sub (Var $3)) (sup (Typ Top))))
       (Flow (sub (Var $2)) (sup (Typ Int)))
       (Flow (sub (Var $3)) (sup (Typ Int))))))
    ("prettify bounds" (Ok (($2 (bot int)) ($3 (bot int)))))
    |}];
  test
    (Fun
       ( Atom ("x", T Top),
         Fun (Atom ("y", T Top), Proj (Proj (Var ("x", T Top), "foo"), "bar"))
       ));
  [%expect
    {|
    (t (Typ (Function (Var $4) (Typ (Function (Var $5) (Var $6))))))
    (c
     (All
      ((With $4 (Flow (sub (Var $4)) (sup (Typ Top))))
       (With $5 (Flow (sub (Var $5)) (sup (Typ Top))))
       (With $6
        (All
         ((With $7
           (Flow (sub (Var $4))
            (sup (Typ (Record ((m ((foo (Present (Var $7))))) (rest Top)))))))
          (Flow (sub (Var $7))
           (sup (Typ (Record ((m ((bar (Present (Var $6))))) (rest Top))))))))))))
    ("prettify bounds"
     (Ok (($4 (bot ({ (foo $7) | ? }))) ($7 (bot ({ (bar $6) | ? }))))))
    |}];
  test (Extend ("foo", Lit 0, Cons [ ("foo", Lit 1) ]));
  [%expect
    {|
    (t (Var $8))
    (c
     (With $8
      (All
       ((Flow
         (sub (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Absent)))))
         (sup (Typ (Record ((m ((foo Absent))) (rest Top))))))
        (Flow (sub (Var $8))
         (sup
          (Apply ((records ((foo Top))))
           (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Absent)))))))
        (Flow (sub (Var $8))
         (sup (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Top))))))))))
    ("prettify bounds"
     (Error
      ("Incompatible record fields"
       (lower (Present (((vars ()) (pos_typ Int) (neg_typ Bot)))))
       (upper Absent))))
    |}];
  test (Extend ("foo", Lit 0, Cons [ ("bar", Lit 1) ]));
  [%expect
    {|
    (t (Var $9))
    (c
     (With $9
      (All
       ((Flow
         (sub (Typ (Record ((m ((bar (Present (Typ Int))))) (rest Absent)))))
         (sup (Typ (Record ((m ((foo Absent))) (rest Top))))))
        (Flow (sub (Var $9))
         (sup
          (Apply ((records ((foo Top))))
           (Typ (Record ((m ((bar (Present (Typ Int))))) (rest Absent)))))))
        (Flow (sub (Var $9))
         (sup (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Top))))))))))
    ("prettify bounds" (Ok (($9 (bot ({ (bar int) (foo int) }))))))
    |}];
  test (Fun (Atom ("x", T Top), Extend ("foo", Lit 0, Var ("x", T Top))));
  [%expect
    {|
    (t (Typ (Function (Var $10) (Var $11))))
    (c
     (All
      ((With $10 (Flow (sub (Var $10)) (sup (Typ Top))))
       (With $11
        (All
         ((Flow (sub (Var $10))
           (sup (Typ (Record ((m ((foo Absent))) (rest Top))))))
          (Flow (sub (Var $11)) (sup (Apply ((records ((foo Top)))) (Var $10))))
          (Flow (sub (Var $11))
           (sup (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Top))))))))))))
    ("prettify bounds"
     (Ok
      (($10 (((lift (foo)) $11) ({ (foo _) | ? })))
       ($11 (bot (& ({ (foo int) | ? }) ((drop (foo)) $10)))))))
    |}];
  test ("r => {b: r.b.not() | r \\ b}" |> Syntax.parse_exn);
  [%expect
    {|
    (t (Typ (Function (Var $12) (Var $13))))
    (c
     (All
      ((With $12 (Flow (sub (Var $12)) (sup (Typ Top))))
       (With $13
        (All
         ((With $14
           (With $15
            (All
             ((With $16
               (All
                ((With $17
                  (Flow (sub (Var $12))
                   (sup
                    (Typ (Record ((m ((b (Present (Var $17))))) (rest Top)))))))
                 (Flow (sub (Var $17))
                  (sup
                   (Typ (Record ((m ((not (Present (Var $16))))) (rest Top)))))))))
              (Flow (sub (Var $16)) (sup (Typ (Function (Var $14) (Var $15)))))
              (Flow (sub (Typ (Tuple ()))) (sup (Var $14)))))))
          (With $18
           (All
            ((Flow (sub (Var $18)) (sup (Apply ((records ((b Top)))) (Var $12))))
             (Flow (sub (Var $18))
              (sup (Typ (Record ((m ((b Absent))) (rest Top)))))))))
          (Flow (sub (Var $18))
           (sup (Typ (Record ((m ((b Absent))) (rest Top))))))
          (Flow (sub (Var $13)) (sup (Apply ((records ((b Top)))) (Var $18))))
          (Flow (sub (Var $13))
           (sup (Typ (Record ((m ((b (Present (Var $15))))) (rest Top))))))))))))
    ("prettify bounds"
     (Ok
      (($12 ((| ((lift (b)) $13) ((lift (b)) $18)) ({ (b $17) | ? })))
       ($13 (bot (& ({ (b $15) | ? }) ((drop (b)) $12) ((drop (b)) $18))))
       ($14 (() top)) ($16 (bot ($14 -> $15))) ($17 (bot ({ (not $16) | ? })))
       ($18 (((lift (b)) $13) (& ({ (b _) | ? }) ((drop (b)) $12)))))))
    |}];
  test ("f => let z = x => f (v => x x v) in z z" |> Syntax.parse_exn);
  [%expect
    {|
    (t (Typ (Function (Var $19) (Var $30))))
    (c
     (All
      ((With $19 (Flow (sub (Var $19)) (sup (Typ Top))))
       (With $20 (Flow (sub (Var $20)) (sup (Typ Top))))
       (With $21 (Flow (sub (Var $21)) (sup (Typ Top))))
       (With $22
        (With $23
         (All
          ((With $24 (Flow (sub (Var $24)) (sup (Typ Top))))
           (With $25
            (With $26
             (All
              ((With $27
                (With $28
                 (All
                  ((Flow (sub (Var $21))
                    (sup (Typ (Function (Var $27) (Var $28)))))
                   (Flow (sub (Var $21)) (sup (Var $27)))))))
               (Flow (sub (Var $28)) (sup (Typ (Function (Var $25) (Var $26)))))
               (Flow (sub (Var $24)) (sup (Var $25)))))))
           (Flow (sub (Var $19)) (sup (Typ (Function (Var $22) (Var $23)))))
           (Flow (sub (Typ (Function (Var $24) (Var $26)))) (sup (Var $22)))))))
       (Flow (sub (Typ (Function (Var $21) (Var $23)))) (sup (Var $20)))
       (With $29
        (With $30
         (All
          ((Flow (sub (Var $20)) (sup (Typ (Function (Var $29) (Var $30)))))
           (Flow (sub (Var $20)) (sup (Var $29))))))))))
    ("prettify bounds"
     (Ok
      (($19 (bot ($22 -> $23)))
       ($20 (($21 -> $23) (& ((& $27 $29) -> (| $28 $30)) $21 $27 $29)))
       ($21 ((| ($21 -> $23) $20 $21 $27 $29) (& ($27 -> $28) $21 $27)))
       ($22 (($24 -> $26) top)) ($23 (bot (& ($25 -> $26) $28 $30)))
       ($24 (bot $25)) ($25 ($24 top))
       ($27 ((| ($21 -> $23) $20 $21 $27 $29) (& ($27 -> $28) $21 $27)))
       ($28 ($23 ($25 -> $26)))
       ($29 ((| ($21 -> $23) $20) (& ($27 -> $28) $21 $27))) ($30 ($23 top)))))
    |}];
  test ("{} + {}" |> Syntax.parse_exn);
  [%expect
    {|
    (t (Typ Int))
    (c
     (All
      ((Flow (sub (Typ (Record ((m ()) (rest Absent))))) (sup (Typ Int)))
       (Flow (sub (Typ (Record ((m ()) (rest Absent))))) (sup (Typ Int))))))
    ("prettify bounds"
     (Error
      (("Incompatible types" (lower (Record ((m ()) (rest Absent)))) (upper Int))
       ("Incompatible types" (lower (Record ((m ()) (rest Absent)))) (upper Int)))))
    |}];
  test ("(1 + 2).foo" |> Syntax.parse_exn);
  [%expect
    {|
    (t (Var $31))
    (c
     (With $31
      (All
       ((Flow (sub (Typ Int)) (sup (Typ Int)))
        (Flow (sub (Typ Int)) (sup (Typ Int)))
        (Flow (sub (Typ Int))
         (sup (Typ (Record ((m ((foo (Present (Var $31))))) (rest Top))))))))))
    ("prettify bounds"
     (Error
      ("Incompatible types" (lower Int)
       (upper
        (Record
         ((m
           ((foo
             (Present
              (((vars (((var $31) (neg false) (app ((records ()))))))
                (pos_typ Top) (neg_typ Bot)))))))
          (rest Top)))))))
    |}];
  test ("({foo : 42}).bar" |> Syntax.parse_exn);
  [%expect
    {|
    (t (Var $32))
    (c
     (With $32
      (Flow (sub (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Absent)))))
       (sup (Typ (Record ((m ((bar (Present (Var $32))))) (rest Top))))))))
    ("prettify bounds"
     (Error
      ("Incompatible record fields" (lower Absent)
       (upper
        (Present
         (((vars (((var $32) (neg false) (app ((records ())))))) (pos_typ Top)
           (neg_typ Bot))))))))
    |}]
