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
  let polar_map = polar_map
  let map = map
  let unwrap (T t) = t

  let components =
    let open Polar in
    function
    | Top -> { pos = []; neg = [] }
    | Bot -> { pos = []; neg = [] }
    | Int -> { pos = []; neg = [] }
    | Float -> { pos = []; neg = [] }
    | Tuple ts -> { pos = ts; neg = [] }
    | Function (t, t') -> { pos = [ t' ]; neg = [ t ] }
    | Array t -> { pos = [ t ]; neg = [] }
    | Record fs -> { pos = Fields.components fs; neg = [] }

  let field_decompose sexp ((lower, upper) : 'a Field.t * 'a Field.t) :
      ('a * 'a) list Or_error.t =
    match (lower, upper) with
    | Bot, _ | _, Top | Absent, Absent -> Ok []
    | Present t, Present t' -> Ok [ (t, t') ]
    | (Absent | Top), Present _
    | (Present _ | Top), Absent
    | (Absent | Present _ | Top), Bot ->
        let lower = Field.pretty sexp lower
        and upper = Field.pretty sexp upper in
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
        let lower = pretty sexp lower and upper = pretty sexp upper in
        error_s
          [%message "Incompatible types" (lower : Sexp.t) (upper : Sexp.t)]

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

    let apply _ { records } = function
      | Record fs ->
          Record
            (Map.fold records ~init:fs ~f:(fun ~key:l ~data fs ->
                 Fields.update fs l (match data with Top -> Top | Bot -> Bot)))
      | t -> t

    let swap_left typ { records } =
      ( {
          records =
            Map.filter_map records ~f:(function
              | Top -> Some (Bot : dir)
              | Bot -> None);
        },
        typ
          (if Map.is_empty records then top
           else
             Record
               Fields.
                 {
                   m =
                     Map.filter_map records ~f:(function
                       | Top -> None
                       | Bot -> Some Field.Bot);
                   rest = `Top;
                 }) )

    let swap_right typ { records } =
      ( {
          records =
            Map.filter_map records ~f:(function
              | Bot -> Some (Top : dir)
              | Top -> None);
        },
        typ
          (if Map.is_empty records then bot
           else
             Record
               Fields.
                 {
                   m =
                     Map.filter_map records ~f:(function
                       | Top -> Some Field.Top
                       | Bot -> None);
                   rest = `Bot;
                 }) )
  end
end

module FabricCNF = CNF (FabricTypeSystem)
module FabricDNF = DNF (FabricTypeSystem)

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
  [%expect {| ({ (bar int) (foo int) }) |}];
  print_s
    [%sexp
      (meet
         (typ (Lang.Fabric.Type.Function (typ Top, typ Int)))
         (typ (Lang.Fabric.Type.Function (typ Int, typ Bot)))
        : t)];
  [%expect {| (top -> bot) |}];
  print_s
    [%sexp
      (meet
         (typ
            (Lang.Fabric.Type.Function
               (typ (Lang.Fabric.Type.Function (typ Top, typ Top)), typ Int)))
         (typ
            (Lang.Fabric.Type.Function
               (typ (Lang.Fabric.Type.Function (typ Int, typ Int)), typ Bot)))
        : t)];
  [%expect {| ((int -> top) -> bot) |}];
  print_s
    [%sexp
      (FabricDNF.meet
         (typ (Lang.Fabric.Type.Function (typ Top, typ Int))
         |> fabric_cnf_to_dnf)
         (typ (Lang.Fabric.Type.Function (typ Int, typ Bot))
         |> fabric_cnf_to_dnf)
       |> fabric_dnf_to_cnf
        : t)];
  [%expect {| (top -> bot) |}]

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
  module Sig = Sig.Make (FabricTypeSystem)
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
    let var x = Map.find_exn env (Var.of_string x) in
    function
    | Var (x, _) -> return (var x)
    | Lit _ -> return_typ Int
    | Unify (x, x', e) ->
        let t = var x and t' = var x' in
        let* () = t <: t' and* () = t' <: t in
        go env e
    | Let (p, e, e') ->
        let* xs, t = pat p in
        let* e = go (push xs env) e in
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
        let* e = go env e in
        let field fd = Label.Map.singleton f fd in
        return
          (Alg.meet
             (apply (field_drop f) e)
             (typ (Record (field Field.Absent |> Fields.open_))))
    | Extend (f, e, e') ->
        let f = Label.of_string f in
        let* e = go env e and* e' = go env e' in
        let field fd = Label.Map.singleton f fd in
        let* () = e' <: typ (Record (field Field.Absent |> Fields.open_)) in
        return
          (Alg.meet
             (apply (field_drop f) e')
             (typ (Record (field (Field.Present e) |> Fields.open_))))
    | Op (e, "", e') ->
        let$ res = () in
        let* e = go env e and* e' = go env e' in
        let* () = e <: typ (Function (e', res)) in
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
    curr_type_var := 0;
    let t, c = Constrained.unwrap (go Var.Map.empty e) in
    let c = Constraint.simp c in
    (* print_s [%message (c : Type.Alg.t Constraint.t)]; *)
    match Solver.run c with
    | Ok bounds ->
        let s = Sig.t bounds (Type.dnf t) in
        print_s [%message (Sig.pretty s : Sexp.t)]
    | Error err -> print_s [%message (err : Error.t)]
  in
  test (Proj (Cons [ ("foo", Lit 5); ("bar", Tuple [ Lit 1; Lit 2 ]) ], "foo"));
  [%expect {| ("Sig.pretty s" int) |}];
  test
    (Fun
       ( Atom ("x", T Top),
         Fun (Atom ("y", T Top), Op (Var ("x", T Top), "+", Var ("y", T Top)))
       ));
  [%expect {| ("Sig.pretty s" (int -> (int -> int))) |}];
  test
    (Fun
       ( Atom ("x", T Top),
         Fun (Atom ("y", T Top), Proj (Proj (Var ("x", T Top), "foo"), "bar"))
       ));
  [%expect
    {| ("Sig.pretty s" (({ (foo ({ (bar $3) | ? })) | ? }) -> (top -> $3))) |}];
  test (Extend ("foo", Lit 0, Cons [ ("foo", Lit 1) ]));
  [%expect {| (err ("Incompatible record fields" (lower int) (upper _))) |}];
  test (Extend ("foo", Lit 0, Cons [ ("bar", Lit 1) ]));
  [%expect {| ("Sig.pretty s" ({ (bar int) (foo int) })) |}];
  test (Fun (Atom ("x", T Top), Extend ("foo", Lit 0, Var ("x", T Top))));
  [%expect
    {|
    ("Sig.pretty s"
     ((& $1 ({ (foo _) | ? })) -> (& ((drop (foo)) $1) ({ (foo int) | ? }))))
    |}];
  test ("r => {b: r.b.not() | r \\ b}" |> Syntax.parse_exn);
  [%expect
    {|
    ("Sig.pretty s"
     ((& $1 ({ (b ({ (not (() -> $2)) | ? })) | ? })) ->
      (& ((drop (b)) $1) ({ (b $2) | ? }))))
    |}];
  test ("f => let z = x => f (v => x x v) in z z" |> Syntax.parse_exn);
  [%expect
    {| ("Sig.pretty s" ((($5 -> $6) -> (& $4 $8 ($5 -> $6))) -> (| $4 $8))) |}];
  test
    ("let y = f => let z = x => f (v => x x v) in z z in \n\n\
      y (f => n => n * (f (n - 1)))" |> Syntax.parse_exn);
  [%expect {| ("Sig.pretty s" (int -> int)) |}];
  test ("let f = x => f (x + 1) in f" |> Syntax.parse_exn);
  [%expect {| ("Sig.pretty s" (int -> bot)) |}];
  test ("let f = r => r.foo.bar in f" |> Syntax.parse_exn);
  [%expect {| ("Sig.pretty s" (({ (foo ({ (bar $3) | ? })) | ? }) -> $3)) |}];
  test ("{} + {}" |> Syntax.parse_exn);
  [%expect
    {|
    (err
     (("Incompatible types" (lower ({ })) (upper int))
      ("Incompatible types" (lower ({ })) (upper int))))
    |}];
  test ("(1 + 2).foo" |> Syntax.parse_exn);
  [%expect
    {| (err ("Incompatible types" (lower int) (upper ({ (foo $1) | ? })))) |}];
  test ("{foo : 42}.bar" |> Syntax.parse_exn);
  [%expect {| (err ("Incompatible record fields" (lower _) (upper $1))) |}];
  test ("let f = g => f (g 0) in f" |> Syntax.parse_exn);
  [%expect
    {|
    ("Sig.pretty s"
     (($2 -> bot) where (($2 <= (int -> $4)) ($4 <= (& $2 (int -> $4))))))
    |}];
  test ("r => { foo: 42 | r }" |> Syntax.parse_exn);
  [%expect
    {|
    ("Sig.pretty s"
     ((& $1 ({ (foo _) | ? })) -> (& ((drop (foo)) $1) ({ (foo int) | ? }))))
    |}];
  test ("r => { self: r | r }" |> Syntax.parse_exn);
  [%expect
    {|
    ("Sig.pretty s"
     ((& $1 ({ (self _) | ? })) -> (& ((drop (self)) $1) ({ (self $1) | ? }))))
    |}];
  test ("(a, b) => a.foo + b.bar" |> Syntax.parse_exn);
  [%expect
    {| ("Sig.pretty s" ((({ (foo int) | ? }) ({ (bar int) | ? })) -> int)) |}];
  test ("(x, y, z) => x.div (z.add (x.mul x y) z) x" |> Syntax.parse_exn);
  [%expect
    {|
    ("Sig.pretty s"
     (((& $1 ({ (div ($7 -> ($1 -> $4))) (mul ($1 -> ($2 -> $10))) | ? })) $2
       (& $3 ({ (add ($10 -> ($3 -> $7))) | ? })))
      -> $4))
    |}];
  (* Experimenting with closed operations *)
  test ("(a, b) => let a ~ b in (a, b)" |> Syntax.parse_exn);
  [%expect {| ("Sig.pretty s" (($1 $1) -> ($1 $1))) |}];
  test ("let add = x => y => x.add x y in add" |> Syntax.parse_exn);
  [%expect
    {| ("Sig.pretty s" ((& $2 ({ (add ($2 -> ($3 -> $4))) | ? })) -> ($3 -> $4))) |}];
  [%expect {| |}];
  test
    ("let add = x => y => (let x ~ y in x.add x y) in add" |> Syntax.parse_exn);
  [%expect
    {|
    ("Sig.pretty s"
     ((& $2 ({ (add ($2 -> ($2 -> $4))) | ? })) ->
      ((& $2 ({ (add ($2 -> ($2 -> $4))) | ? })) -> $4)))
    |}];
  test
    ("let add = x => y => (let z = x.add x y in let x ~ y in let x ~ z in z) \
      in add" |> Syntax.parse_exn);
  (* TODO: 'a -> 'a -> 'a where 'a <= { add: 'a -> 'a -> 'a } *)
  [%expect
    {|
    ("Sig.pretty s"
     (($2 -> ($2 -> (| $2 $5))) where
      (($2 <= ({ (add $7) | ? }))
       ($7 <= ((| $2 $5) -> ((| $2 $5) -> (& $2 $5 ({ (add $7) | ? }))))))))
    |}];
  (* TODO: This should simplify to 
      ('a, 'a, 'a) -> 'a where 'a <= { add: 'a -> 'a -> 'a }
      The previous two should be good partial steps. *)
  test
    ("let add = x => y => (let z = x.add x y in let x ~ y in let x ~ z in z) \
      in (x, y, z) => add (add x y) z" |> Syntax.parse_exn);
  [%expect
    {|
    ("Sig.pretty s"
     ((((& $11 $13 $8 ({ (add $7) | ? })) (& $11 $13 $9 ({ (add $7) | ? }))
        (& $10 $11 $13 ({ (add $7) | ? })))
       -> (| $10 $11 $13 $5 $8 $9))
      where
      (($7 <=
        ((| $10 $13 $5 $8 $9) ->
         ((| $10 $13 $5 $8 $9) -> (& $11 $13 $5 ({ (add $7) | ? }))))))))
    |}]
