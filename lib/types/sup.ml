open Core
open Lang.Sym

let next_type_var =
  let cnt = ref 0 in
  fun () ->
    cnt := !cnt + 1;
    Type_var.of_string ("$" ^ string_of_int !cnt)

type ('a, 'args) massage = ('a -> Sexp.t) -> 'args -> ('a * 'a) list Or_error.t

module type TypeSystem = sig
  type 'a typ [@@deriving sexp, equal, compare]
  type simple
  type arrow

  val map : f:('a -> 'b) -> 'a typ -> 'b typ
  val unwrap : simple -> simple typ
  val decompose : ('a, 'a typ * 'a typ) massage
  val is_top : ('a, 'a typ) massage
  val is_bot : ('a, 'a typ) massage
  val join : 'a typ -> 'a typ -> 'a typ
  val meet : 'a typ -> 'a typ -> 'a typ

  module Arrow : sig
    type t = arrow [@@deriving sexp, equal, compare]

    val id : t
    val compose : t -> t -> t
    val apply : t -> 'a typ -> 'a typ
    val left_adjoint : t -> t
    val right_adjoint : t -> t
  end
end

type fabric_arrow = Drop of Label.Set.t

module FabricTypeSystem :
  TypeSystem
    with type 'a typ = 'a Lang.Fabric.Type.typ
     and type arrow = fabric_arrow = struct
  open Lang.Fabric.Type

  type nonrec 'a typ = 'a typ [@@deriving sexp, equal, compare]
  type simple = t
  type arrow = fabric_arrow

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

  let decompose sexp ((lower : 'a typ), (upper : 'a typ)) :
      ('a * 'a) list Or_error.t =
    match (lower, upper) with
    | _, Top -> Ok []
    | Bot, _ -> Ok []
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

  let join (_ : 'a typ) (_ : 'a typ) : 'a typ = failwith "unimplemented: join"
  let meet (_ : 'a typ) (_ : 'a typ) : 'a typ = failwith "unimplemented: meet"

  module Arrow = struct
    open Lang.Fabric.Type

    type t = fabric_arrow = Drop of Label.Set.t
    [@@deriving sexp, equal, compare]

    let id = Drop Label.Set.empty
    let compose (Drop ls) (Drop ls') = Drop (Set.union ls ls')

    let apply (Drop ls) = function
      | Record fs ->
          Record (Set.fold ls ~init:fs ~f:(fun fs l -> Fields.update fs l Top))
      | t -> t

    let left_adjoint = function Drop _ -> failwith "Arrow.left_adjoint: Drop"

    let right_adjoint = function
      | Drop _ -> failwith "Arrow.right_adjoint: Drop"
  end
end

module Type (M : TypeSystem) = struct
  open M
  open Lang.Sym

  module Normal = struct
    module Var = struct
      module T = struct
        type t = { var : Type_var.t; neg : bool; app : Arrow.t }
        [@@deriving sexp, equal, compare]
      end

      include T

      let var x = { var = x; neg = false; app = Arrow.id }
      let negate t = { t with neg = not t.neg }
      let apply a t = { t with app = Arrow.compose a t.app }

      module Set = Set.Make (T)
    end

    type clause = { vars : Var.Set.t; typ : (bool * t M.typ) option }
    and t = clause list [@@deriving sexp, equal, compare]

    let rec simple t : t =
      [
        {
          vars = Var.Set.empty;
          typ = Some (false, M.map ~f:(fun t -> simple t) (M.unwrap t));
        };
      ]

    let bot : t = []
    let top : t = [ { vars = Var.Set.empty; typ = None } ]
    let typ t : t = [ { vars = Var.Set.empty; typ = Some t } ]
    let var x = [ { vars = Var.Set.singleton (Var.var x); typ = None } ]

    let apply a t =
      List.map t ~f:(fun { vars; typ } ->
          {
            vars = Var.Set.map vars ~f:(fun x -> Var.apply a x);
            typ = Option.map ~f:(fun (n, t) -> (n, M.Arrow.apply a t)) typ;
          })
  end

  module Alg = struct
    type dir = Bot | Top [@@deriving sexp, equal, compare]

    type t =
      | Var of Type_var.t
      | Typ of t typ
      | Apply of M.Arrow.t * t
      | Extreme of dir
      | Combine of dir * t * t
      | Complement of t
    [@@deriving sexp, equal, compare]
  end

  let var x = Alg.Var x
  let typ t = Alg.Typ t
  let apply a t = Alg.Apply (a, t)
end

module Constraint = struct
  type 'alg t =
    | With of Type_var.t * 'alg t
    | Flow of { sub : 'alg; sup : 'alg }
    | All of 'alg t list
  [@@deriving sexp]

  let truth = All []

  let rec simp = function
    | With (x, c) -> ( match With (x, simp c) with All [] -> All [] | c -> c)
    | Flow f -> Flow f
    | All cs -> (
        let cs = List.map cs ~f:simp in
        let cs =
          List.concat_map cs ~f:(function All cs' -> cs' | c -> [ c ])
        in
        match cs with [ c ] -> c | cs -> All cs)
end

module Constrained (M : TypeSystem) : sig
  type 'a t

  val wrap : 'a * Type(M).Alg.t Constraint.t -> 'a t
  val unwrap : 'a t -> 'a * Type(M).Alg.t Constraint.t
  val return : 'a -> 'a t
  val all : 'a t list -> 'a list t
  val all_in_map : ('key, 'a t, 'cmp) Map.t -> ('key, 'a, 'cmp) Map.t t
  val ( <: ) : Type(M).Alg.t -> Type(M).Alg.t -> unit t
  val ( let$ ) : unit -> (Type(M).Alg.t -> 'a t) -> 'a t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( and* ) : 'a t -> 'b t -> ('a * 'b) t
end = struct
  open Constraint
  open Type (M)

  type nonrec 'a t = 'a * Alg.t t

  let wrap = Fn.id
  let unwrap = Fn.id
  let return t = (t, truth)

  let all ts =
    ( List.map ts ~f:(fun (t, _) -> t),
      List.fold ts ~init:truth ~f:(fun c (_, c') -> All [ c; c' ]) )

  let all_in_map m =
    ( Map.map m ~f:(fun (t, _) -> t),
      Map.fold m ~init:truth ~f:(fun ~key:_ ~data:(_, c') c -> All [ c; c' ]) )

  let ( <: ) sub sup = ((), Flow { sub; sup })

  let ( let$ ) () f =
    let x = next_type_var () in
    let t, c = f (var x) in
    (t, With (x, c))

  let ( let* ) (t, c) f =
    let t', c' = f t in
    (t', All [ c; c' ])

  let ( and* ) (t, c) (t', c') : _ t = ((t, t'), All [ c; c' ])
end

module Solver (M : TypeSystem) = struct
  open Type (M)

  type bound =
    | Lower of Alg.t * Type_var.t
    | Upper of Type_var.t * Alg.t
    | Fail of string * Alg.t list
  [@@deriving sexp]

  type dir = Alg.dir = Bot | Top

  let concat_map_or_error xs ~f =
    List.map xs ~f |> Or_error.all |> Or_error.map ~f:List.concat

  let inv = function Top -> Bot | Bot -> Top

  (* Lift back to general form *)
  let un t : Alg.t =
    match t with
    | `Extreme dir -> Extreme dir
    | `Var x -> Var x
    | `Typ t -> Typ t
    | `Combine (dir, t, t') -> Combine (dir, t, t')
    | `Complement (`Var x) -> Complement (Var x)
    | `Complement (`Typ t) -> Complement (Typ t)
    | `Apply (a, `Var x) -> Apply (a, Var x)
    | `Apply (a, `VarComplement x) -> Apply (a, Complement (Var x))

  (* Simplify to reduce the number of possible cases, 
     mainly for complements and arrows *)
  let rec simp (t : Alg.t) =
    match t with
    | Extreme dir -> `Extreme dir
    | Var x -> `Var x
    | Typ t -> `Typ t
    | Combine (dir, t, t') -> `Combine (dir, t, t')
    (* Complements *)
    | Complement (Complement t) -> simp t
    | Complement (Combine (dir, t, t')) ->
        `Combine (inv dir, Complement t, Complement t')
    | Complement (Extreme dir) -> `Extreme (inv dir)
    | Complement (Var x) -> `Complement (`Var x)
    | Complement (Typ t) -> `Complement (`Typ t)
    | Complement (Apply (a, t)) -> simp (Apply (a, Complement t))
    (* Arrows *)
    | Apply (_, Extreme dir) -> `Extreme dir
    | Apply (a, Apply (a', t)) -> simp (Apply (M.Arrow.compose a a', t))
    | Apply (a, Combine (dir, t, t')) ->
        `Combine (dir, Apply (a, t), Apply (a, t'))
    | Apply (a, Var x) -> `Apply (a, `Var x)
    | Apply (a, Typ t) -> simp (Typ (M.Arrow.apply a t))
    | Apply (a, Complement t) -> (
        match simp t with
        | `Complement (`Var x) -> `Apply (a, `VarComplement x)
        | `Complement (`Typ t) -> simp (Complement (Typ (M.Arrow.apply a t)))
        | t' -> simp (Apply (a, un t')))

  let unv x : Alg.t =
    match x with `Var x -> Var x | `VarComplement x -> Complement (Var x)

  let rec atomize ~lower ~upper : bound list Or_error.t =
    match (simp lower, simp upper) with
    (* Atomic bounds *)
    | `Var x, t2 -> Ok [ Upper (x, un t2) ]
    | t1, `Var x -> Ok [ Lower (un t1, x) ]
    (* Extremes *)
    | `Extreme Bot, _ -> Ok []
    | _, `Extreme Top -> Ok []
    | `Extreme Top, `Extreme Bot -> error_s [%message "top <= bot"]
    | `Typ t1, `Extreme Bot ->
        M.is_bot Alg.sexp_of_t t1 |> atomize_decomposition
    | `Extreme Top, `Typ t2 ->
        M.is_top Alg.sexp_of_t t2 |> atomize_decomposition
    (* Decompose inequality on type constructors *)
    | `Typ lower, `Typ upper ->
        M.decompose Alg.sexp_of_t (lower, upper) |> atomize_decomposition
    (* Joins and meets *)
    | `Combine (Top, t1, t1'), t2 -> (t1 *<=* un t2) @@ (t1' *<=* un t2)
    | t1, `Combine (Bot, t2, t2') -> (un t1 *<=* t2) @@ (un t1 *<=* t2')
    | `Combine (Bot, t1, t1'), t2 -> t1 *<=* Combine (Bot, Complement t1', un t2)
    | t1, `Combine (Top, t2, t2') ->
        Combine (Top, un t1, Complement t2) *<=* t2'
    (* Complements *)
    | `Complement t1, `Complement t2 -> un t2 *<=* un t1
    | `Complement (`Typ t1), `Typ t2 ->
        M.is_top Alg.sexp_of_t (M.join t1 t2) |> atomize_decomposition
    | `Typ t1, `Complement (`Typ t2) ->
        M.is_bot Alg.sexp_of_t (M.meet t1 t2) |> atomize_decomposition
    | t1, `Complement (`Var x) -> Var x *<=* Complement (un t1)
    | `Complement (`Var x), t2 -> Complement (un t2) *<=* Var x
    | `Extreme Top, `Complement t2 -> un t2 *<=* Extreme Bot
    | `Complement t1, `Extreme Bot -> Extreme Top *<=* un t1
    (* Arrows *)
    | `Extreme dir, `Apply (_, t2) -> Extreme dir *<=* unv t2
    | `Apply (_, t1), `Extreme dir -> unv t1 *<=* Extreme dir
    (* This case would trigger nondeterministically for both of the latter reductions,
       so we produce both the adjoint-equivalent bounds *)
    | `Apply (a1, t1), `Apply (a2, t2) ->
        Apply (M.Arrow.compose (M.Arrow.left_adjoint a2) a1, unv t1)
        *<=* unv t2
        @@ unv t1
           *<=* Apply (M.Arrow.compose (M.Arrow.right_adjoint a1) a2, unv t2)
    | t1, `Apply (a, x) -> Apply (M.Arrow.left_adjoint a, un t1) *<=* unv x
    | `Apply (a, x), t2 -> unv x *<=* Apply (M.Arrow.right_adjoint a, un t2)

  and atomize_decomposition =
    Or_error.bind ~f:(concat_map_or_error ~f:(fun (l, u) -> l *<=* u))

  and ( @@ ) a b = concat_map_or_error ~f:Fn.id [ a; b ]
  and ( *<=* ) lower upper = atomize ~lower ~upper

  let rec atomize_constraint : Alg.t Constraint.t -> bound list Or_error.t =
    function
    | With (_, c) -> atomize_constraint c
    | Flow { sub; sup } -> atomize ~lower:sub ~upper:sup
    | All cs -> concat_map_or_error cs ~f:atomize_constraint
end

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

  let rec go (env : Alg.t Var.Map.t) : t -> Alg.t Constrained.t =
    let open Constrained in
    let return_typ (t : Alg.t Lang.Fabric.Type.typ) = return (typ t) in
    function
    | Var (x, _) -> return (Map.find_exn env (Var.of_string x))
    | Lit _ -> return_typ Int
    | Let (Atom (x, _), e, e') ->
        let$ x_ = () in
        let* e = go env e in
        let* () = e <: x_ in
        go (Map.add_exn env ~key:(Var.of_string x) ~data:x_) e'
    | Fun (Atom (x, _), e) ->
        let$ x_ = () in
        let* e = go (Map.add_exn env ~key:(Var.of_string x) ~data:x_) e in
        return_typ (Function (x_, e))
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
    | Extend (f, e, e') ->
        let f = Label.of_string f in
        let$ r = () in
        let* e = go env e and* e' = go env e' in
        let field fd = Label.Map.singleton f fd in
        let* () = e' <: typ (Record (field Field.Absent |> Fields.open_))
        and* () = r <: apply (Drop (Label.Set.singleton f)) e'
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
    | Let _ -> failwith "TypeExpr.go: non-Atom Let"
    | Fun _ -> failwith "TypeExpr.go: non-Atom Fun"
    | Op (_, o, _) -> failwith ("TypeExpr.go: Op " ^ o)
end

let%expect_test "" =
  let test e =
    let t, c =
      FabricTyper.Constrained.unwrap (FabricTyper.go Var.Map.empty e)
    in
    let c = Constraint.simp c in
    print_s [%message (t : FabricTyper.Type.Alg.t)];
    print_s [%message (c : FabricTyper.Type.Alg.t Constraint.t)];
    print_s
      [%message
        (FabricTyper.Solver.atomize_constraint c
          : FabricTyper.Solver.bound list Or_error.t)]
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
    ("FabricTyper.Solver.atomize_constraint c" (Ok ((Lower (Typ Int) $1))))
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
     (With $2
      (With $3
       (All
        ((Flow (sub (Var $2)) (sup (Typ Int)))
         (Flow (sub (Var $3)) (sup (Typ Int))))))))
    ("FabricTyper.Solver.atomize_constraint c"
     (Ok ((Upper $2 (Typ Int)) (Upper $3 (Typ Int)))))
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
     (With $4
      (With $5
       (With $6
        (All
         ((With $7
           (Flow (sub (Var $4))
            (sup (Typ (Record ((m ((foo (Present (Var $7))))) (rest Top)))))))
          (Flow (sub (Var $7))
           (sup (Typ (Record ((m ((bar (Present (Var $6))))) (rest Top))))))))))))
    ("FabricTyper.Solver.atomize_constraint c"
     (Ok
      ((Upper $4 (Typ (Record ((m ((foo (Present (Var $7))))) (rest Top)))))
       (Upper $7 (Typ (Record ((m ((bar (Present (Var $6))))) (rest Top))))))))
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
          (Apply (Drop (foo))
           (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Absent)))))))
        (Flow (sub (Var $8))
         (sup (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Top))))))))))
    ("FabricTyper.Solver.atomize_constraint c"
     (Error
      ("Incompatible record fields" (lower (Present (Typ Int))) (upper Absent))))
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
          (Apply (Drop (foo))
           (Typ (Record ((m ((bar (Present (Typ Int))))) (rest Absent)))))))
        (Flow (sub (Var $9))
         (sup (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Top))))))))))
    ("FabricTyper.Solver.atomize_constraint c"
     (Ok
      ((Upper $9
        (Typ (Record ((m ((bar (Present (Typ Int))) (foo Top))) (rest Absent)))))
       (Upper $9 (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Top))))))))
    |}];
  test (Fun (Atom ("x", T Top), Extend ("foo", Lit 0, Var ("x", T Top))));
  [%expect
    {|
    (t (Typ (Function (Var $10) (Var $11))))
    (c
     (With $10
      (With $11
       (All
        ((Flow (sub (Var $10))
          (sup (Typ (Record ((m ((foo Absent))) (rest Top))))))
         (Flow (sub (Var $11)) (sup (Apply (Drop (foo)) (Var $10))))
         (Flow (sub (Var $11))
          (sup (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Top)))))))))))
    ("FabricTyper.Solver.atomize_constraint c"
     (Ok
      ((Upper $10 (Typ (Record ((m ((foo Absent))) (rest Top)))))
       (Upper $11 (Apply (Drop (foo)) (Var $10)))
       (Upper $11 (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Top))))))))
    |}]
