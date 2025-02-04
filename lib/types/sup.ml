open Core
open Lang.Sym

let next_type_var =
  let cnt = ref 0 in
  fun () ->
    cnt := !cnt + 1;
    Type_var.of_string ("$" ^ string_of_int !cnt)

module Type = struct
  include Lang.Fabric.Type

  type alg =
    | Extreme of dir
    | Var of Type_var.t
    | Typ of alg typ
    | Arrow of arrow * alg
    | Combine of dir * alg * alg
    | Complement of alg
  [@@deriving sexp]

  and arrow = Drop of Label.Set.t [@@deriving sexp]

  let rec alg_of_typ (T t) = map ~f:(fun t -> Typ (alg_of_typ t)) t
  let arrow_compose (Drop ls) (Drop ls') = Drop (Set.union ls ls')

  let arrow_apply (Drop ls) = function
    | Record fs ->
        Record (Set.fold ls ~init:fs ~f:(fun fs l -> Fields.update fs l Top))
    | t -> t

  let arrow_left_adjoint = function
    | Drop _ -> failwith "arrow_left_adjoint: Drop"

  let arrow_right_adjoint = function
    | Drop _ -> failwith "arrow_right_adjoint: Drop"
end

module Constraint = struct
  type t =
    | With of Type_var.t * t
    | Flow of { sub : Type.alg; sup : Type.alg }
    | All of t list
  [@@deriving sexp]

  let truth = All []

  let rec simp : t -> t = function
    | With (x, c) -> ( match With (x, simp c) with All [] -> All [] | c -> c)
    | Flow f -> Flow f
    | All cs -> (
        let cs = List.map cs ~f:simp in
        let cs =
          List.concat_map cs ~f:(function All cs' -> cs' | c -> [ c ])
        in
        match cs with [ c ] -> c | cs -> All cs)
end

module Constrained : sig
  type 'a t

  val unwrap : 'a t -> 'a * Constraint.t
  val return : 'a -> 'a t
  val all : 'a t list -> 'a list t

  val all_in_map :
    ('key, 'a t Type.Field.t, 'cmp) Map.t ->
    ('key, 'a Type.Field.t, 'cmp) Map.t t

  val ( <: ) : Type.alg -> Type.alg -> unit t
  val ( let$ ) : unit -> (Type.alg -> 'a t) -> 'a t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( and* ) : 'a t -> 'b t -> ('a * 'b) t
end = struct
  open Constraint

  type nonrec 'a t = 'a * t

  let unwrap = Fn.id
  let return t = (t, truth)

  let all ts =
    ( List.map ts ~f:(fun (t, _) -> t),
      List.fold ts ~init:truth ~f:(fun c (_, c') -> All [ c; c' ]) )

  let all_in_field (fd : _ t Type.Field.t) =
    match fd with Top | Bot | Absent -> truth | Present (_, c) -> c

  let all_in_map m =
    ( Map.map m ~f:(Type.Field.map ~f:(fun (t, _) -> t)),
      Map.fold m ~init:truth ~f:(fun ~key:_ ~data:c' c ->
          All [ c; all_in_field c' ]) )

  let ( <: ) sub sup = ((), Flow { sub; sup })

  let ( let$ ) () f =
    let x = next_type_var () in
    let t, c = f (Type.Var x) in
    (t, With (x, c))

  let ( let* ) (t, c) f =
    let t', c' = f t in
    (t', All [ c; c' ])

  let ( and* ) (t, c) (t', c') : _ t = ((t, t'), All [ c; c' ])
end

module Solver = struct
  open Type

  type bound =
    | Lower of alg * Type_var.t
    | Upper of Type_var.t * alg
    | Fail of string * Type.alg list
  [@@deriving sexp]

  let field_decompose ~(lower : alg Field.t) ~(upper : alg Field.t) :
      (alg * alg) list option =
    match (lower, upper) with
    | Bot, _ | _, Top | Absent, Absent -> Some []
    | Present t, Present t' -> Some [ (t, t') ]
    | (Absent | Top), Present _ -> None
    | (Present _ | Top), Absent -> None
    | (Absent | Present _ | Top), Bot -> None

  let decompose ~(lower : alg typ) ~(upper : alg typ) : (alg * alg) list option
      =
    match (lower, upper) with
    | _, Top -> Some []
    | Bot, _ -> Some []
    | Record fs, Record fs' ->
        Fields.subs fs fs' |> Map.to_alist
        |> List.map ~f:(fun (_, (f, f')) -> field_decompose ~lower:f ~upper:f')
        |> Option.all |> Option.map ~f:List.concat
    | _ -> None

  let is_top (t : 'a typ) : bound list =
    match t with Top -> [] | _ -> [ Fail ("not bot", [ Typ t ]) ]

  let is_bot (t : 'a typ) : bound list =
    match t with Bot -> [] | _ -> [ Fail ("not top", [ Typ t ]) ]

  let complement_sub (t : 'a typ) (t' : 'a typ) : bound list =
    [ Fail ("complement not a subtype", [ Complement (Typ t); Typ t' ]) ]

  let sub_complement (t : 'a typ) (t' : 'a typ) : bound list =
    [ Fail ("not a complement subtype", [ Typ t; Complement (Typ t') ]) ]

  (* Lift back to general form *)
  let un t =
    match t with
    | `Extreme dir -> Extreme dir
    | `Var x -> Var x
    | `Typ t -> Typ t
    | `Combine (dir, t, t') -> Combine (dir, t, t')
    | `Complement (`Var x) -> Complement (Var x)
    | `Complement (`Typ t) -> Complement (Typ t)
    | `Arrow (a, `Var x) -> Arrow (a, Var x)
    | `Arrow (a, `VarComplement x) -> Arrow (a, Complement (Var x))

  (* Simplify to reduce the number of possible cases, 
     mainly for complements and arrows *)
  let rec simp (t : alg) =
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
    | Complement (Arrow (a, t)) -> simp (Arrow (a, Complement t))
    (* Arrows *)
    | Arrow (_, Extreme dir) -> `Extreme dir
    | Arrow (a, Arrow (a', t)) -> simp (Arrow (arrow_compose a a', t))
    | Arrow (a, Combine (dir, t, t')) ->
        `Combine (dir, Arrow (a, t), Arrow (a, t'))
    | Arrow (a, Var x) -> `Arrow (a, `Var x)
    | Arrow (a, Typ t) -> simp (Typ (arrow_apply a t))
    | Arrow (a, Complement t) -> (
        match simp t with
        | `Complement (`Var x) -> `Arrow (a, `VarComplement x)
        | `Complement (`Typ t) -> simp (Complement (Typ (arrow_apply a t)))
        | t' -> simp (Arrow (a, un t')))

  let unv x =
    match x with `Var x -> Var x | `VarComplement x -> Complement (Var x)

  let rec atomize ~lower ~upper =
    match (simp lower, simp upper) with
    (* Atomic bounds *)
    | `Var x, t2 -> [ Upper (x, un t2) ]
    | t1, `Var x -> [ Lower (un t1, x) ]
    (* Extremes *)
    | `Extreme Bot, _ -> []
    | _, `Extreme Top -> []
    | `Extreme Top, `Extreme Bot -> [ Fail ("top <= bot", []) ]
    | `Typ t1, `Extreme Bot -> is_bot t1
    | `Extreme Top, `Typ t2 -> is_top t2
    (* Decompose inequality on type constructors *)
    | `Typ lower, `Typ upper -> (
        match decompose ~lower ~upper with
        | Some bs -> List.concat_map ~f:(fun (l, u) -> l *<=* u) bs
        | None -> [ Fail ("decompose", [ Typ lower; Typ upper ]) ])
    (* Joins and meets *)
    | `Combine (Top, t1, t1'), t2 -> (t1 *<=* un t2) @ (t1' *<=* un t2)
    | t1, `Combine (Bot, t2, t2') -> (un t1 *<=* t2) @ (un t1 *<=* t2')
    | `Combine (Bot, t1, t1'), t2 -> t1 *<=* Combine (Bot, Complement t1', un t2)
    | t1, `Combine (Top, t2, t2') ->
        Combine (Top, un t1, Complement t2) *<=* t2'
    (* Complements *)
    | `Complement t1, `Complement t2 -> un t2 *<=* un t1
    | `Complement (`Typ t1), `Typ t2 -> complement_sub t1 t2
    | `Typ t1, `Complement (`Typ t2) -> sub_complement t1 t2
    | t1, `Complement (`Var x) -> Var x *<=* Complement (un t1)
    | `Complement (`Var x), t2 -> Complement (un t2) *<=* Var x
    | `Extreme Top, `Complement t2 -> un t2 *<=* Extreme Bot
    | `Complement t1, `Extreme Bot -> Extreme Top *<=* un t1
    (* Arrows *)
    | `Extreme dir, `Arrow (_, t2) -> Extreme dir *<=* unv t2
    | `Arrow (_, t1), `Extreme dir -> unv t1 *<=* Extreme dir
    (* This case would trigger nondeterministically for both of the latter reductions,
       so we produce both the adjoint-equivalent bounds *)
    | `Arrow (a1, t1), `Arrow (a2, t2) ->
        (Arrow (arrow_compose (arrow_left_adjoint a2) a1, unv t1) *<=* unv t2)
        @ (unv t1 *<=* Arrow (arrow_compose (arrow_right_adjoint a1) a2, unv t2))
    | t1, `Arrow (a, x) -> Arrow (arrow_left_adjoint a, un t1) *<=* unv x
    | `Arrow (a, x), t2 -> unv x *<=* Arrow (arrow_right_adjoint a, un t2)

  and ( *<=* ) lower upper = atomize ~lower ~upper

  let rec atomize_constraint : Constraint.t -> bound list = function
    | With (_, c) -> atomize_constraint c
    | Flow { sub; sup } -> atomize ~lower:sub ~upper:sup
    | All cs -> List.concat_map ~f:atomize_constraint cs
end

module TypeExpr = struct
  open Lang.Fabric.Expr

  let rec go (env : Type.alg Var.Map.t) : t -> Type.alg Constrained.t =
    let open Constrained in
    let open Type in
    let return_typ t = return (Type.Typ t) in
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
            |> Map.map ~f:(fun e -> Field.Present (go env e)))
        in
        return_typ (Record (Fields.closed fs))
    | Proj (e, f) ->
        let$ f_ = () in
        let* e = go env e in
        let* () =
          e
          <: Typ
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
        let* () = e' <: Typ (Record (field Field.Absent |> Fields.open_))
        and* () = r <: Arrow (Drop (Label.Set.singleton f), e')
        and* () = r <: Typ (Record (field (Field.Present e) |> Fields.open_)) in
        return r
    | Op (e, "", e') ->
        let$ arg = () in
        let$ res = () in
        let* e = go env e and* e' = go env e' in
        let* () = e <: Typ (Function (arg, res)) and* () = e' <: arg in
        return res
    | Op (e, ("+" | "-" | "*" | "/"), e') ->
        let* e = go env e in
        let* e' = go env e' in
        let* () = e <: Typ Int and* () = e' <: Typ Int in
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
    let t, c = Constrained.unwrap (TypeExpr.go Var.Map.empty e) in
    let c = Constraint.simp c in
    print_s [%message (t : Type.alg)];
    print_s [%message (c : Constraint.t)];
    print_s [%message (Solver.atomize_constraint c : Solver.bound list)]
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
    ("Solver.atomize_constraint c" ((Lower (Typ Int) $1)))
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
    ("Solver.atomize_constraint c" ((Upper $2 (Typ Int)) (Upper $3 (Typ Int))))
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
    ("Solver.atomize_constraint c"
     ((Upper $4 (Typ (Record ((m ((foo (Present (Var $7))))) (rest Top)))))
      (Upper $7 (Typ (Record ((m ((bar (Present (Var $6))))) (rest Top)))))))
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
          (Arrow (Drop (foo))
           (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Absent)))))))
        (Flow (sub (Var $8))
         (sup (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Top))))))))))
    ("Solver.atomize_constraint c"
     ((Fail decompose
       ((Typ (Record ((m ((foo (Present (Typ Int))))) (rest Absent))))
        (Typ (Record ((m ((foo Absent))) (rest Top))))))
      (Upper $8 (Typ (Record ((m ((foo Top))) (rest Absent)))))
      (Upper $8 (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Top)))))))
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
          (Arrow (Drop (foo))
           (Typ (Record ((m ((bar (Present (Typ Int))))) (rest Absent)))))))
        (Flow (sub (Var $9))
         (sup (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Top))))))))))
    ("Solver.atomize_constraint c"
     ((Upper $9
       (Typ (Record ((m ((bar (Present (Typ Int))) (foo Top))) (rest Absent)))))
      (Upper $9 (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Top)))))))
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
         (Flow (sub (Var $11)) (sup (Arrow (Drop (foo)) (Var $10))))
         (Flow (sub (Var $11))
          (sup (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Top)))))))))))
    ("Solver.atomize_constraint c"
     ((Upper $10 (Typ (Record ((m ((foo Absent))) (rest Top)))))
      (Upper $11 (Arrow (Drop (foo)) (Var $10)))
      (Upper $11 (Typ (Record ((m ((foo (Present (Typ Int))))) (rest Top)))))))
    |}]
