open! Core

module Type_var =
  String_id.Make
    (struct
      let module_name = "Type_var"
    end)
    ()

module Var =
  String_id.Make
    (struct
      let module_name = "Var"
    end)
    ()

module Label =
  String_id.Make
    (struct
      let module_name = "Label"
    end)
    ()

let next_type_var =
  let cnt = ref 0 in
  fun () ->
    cnt := !cnt + 1;
    Type_var.of_string ("$" ^ string_of_int !cnt)

module Type = struct
  type dir = Top | Bot [@@deriving sexp]

  let inv = function Top -> Bot | Bot -> Top

  module Field = struct
    type 't t = Absent | Present of 't [@@deriving sexp]

    let map ~f = function Absent -> Absent | Present t -> Present (f t)
  end

  type 't t =
    | Top
    | Bot
    | Int
    | Tuple of 't list
    | Function of 't * 't
    | Record of 't Field.t Label.Map.t * [ `Unknowns | `Absents ]
  [@@deriving sexp]

  let map ~f = function
    | Top -> Top
    | Bot -> Bot
    | Int -> Int
    | Tuple ts -> Tuple (List.map ~f ts)
    | Function (t, t') -> Function (f t, f t')
    | Record (fs, c) -> Record (Map.map ~f:(Field.map ~f) fs, c)

  type typ = T of typ t [@@deriving sexp]
  type htyp = HVar of Type_var.t | HTyp of htyp t [@@deriving sexp]

  type alg =
    | Extreme of dir
    | Var of Type_var.t
    | Typ of alg t
    | Arrow of arrow * alg
    | Combine of dir * alg * alg
    | Complement of alg
  [@@deriving sexp]

  and arrow = RecordUpdate of alg Field.t Label.Map.t [@@deriving sexp]

  let record_update =
    Map.merge ~f:(fun ~key:_ -> function
      | `Both (t, _) -> Some t
      | `Left t | `Right t -> Some t)

  let arrow_compose a a' =
    match (a, a') with
    | RecordUpdate m, RecordUpdate m' -> RecordUpdate (record_update m m')

  let arrow_apply a t =
    match (a, t) with
    | RecordUpdate m, Record (m', c) -> Record (record_update m m', c)
    | RecordUpdate _, t -> t

  let arrow_left_adjoint = function
    | RecordUpdate _ -> failwith "arrow_left_adjoint: RecordUpdate"

  let arrow_right_adjoint = function
    | RecordUpdate _ -> failwith "arrow_right_adjoint: RecordUpdate"
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
    match fd with Absent -> truth | Present (_, c) -> c

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

  let rec alg_of_htyp = function
    | HTyp t -> Typ (map ~f:alg_of_htyp t)
    | HVar x -> Var x

  let field_decompose ~(lower : alg Field.t) ~(upper : alg Field.t) :
      (alg * alg) list option =
    match (lower, upper) with
    | Absent, Absent -> Some []
    | Present t, Present t' -> Some [ (t, t') ]
    | Absent, Present _ -> None
    | Present _, Absent -> None

  let decompose ~(lower : alg t) ~(upper : alg t) : (alg * alg) list option =
    match (lower, upper) with
    | _, Top -> Some []
    | Bot, _ -> Some []
    | Record (fs, c), Record (fs', c') -> (
        let open Option.Let_syntax in
        match (c, c') with
        | `Unknowns, `Absents -> None
        | `Absents, (`Absents | `Unknowns) ->
            Map.fold2 fs fs' ~init:(Some []) ~f:(fun ~key:_ ~data acc ->
                let%bind acc = acc in
                match data with
                | `Both (fd, fd') ->
                    let%bind ts = field_decompose ~lower:fd ~upper:fd' in
                    Some (acc @ ts)
                | `Left _ -> Some acc
                | `Right fd' ->
                    let%bind ts = field_decompose ~lower:Absent ~upper:fd' in
                    Some (acc @ ts))
        | `Unknowns, `Unknowns ->
            Map.fold2 fs fs' ~init:(Some []) ~f:(fun ~key:_ ~data acc ->
                let%bind acc = acc in
                match data with
                | `Both (fd, fd') ->
                    Option.bind (field_decompose ~lower:fd ~upper:fd')
                      ~f:(fun ts -> Some (acc @ ts))
                | `Left _ -> Some acc
                | `Right _ -> None))
    | _ -> None

  let is_top (t : 'a t) : bound list =
    match t with Top -> [] | _ -> [ Fail ("not bot", [ Typ t ]) ]

  let is_bot (t : 'a t) : bound list =
    match t with Bot -> [] | _ -> [ Fail ("not top", [ Typ t ]) ]

  let complement_sub (t : 'a t) (t' : 'a t) : bound list =
    [ Fail ("complement not a subtype", [ Complement (Typ t); Typ t' ]) ]

  let sub_complement (t : 'a t) (t' : 'a t) : bound list =
    [ Fail ("not a complement subtype", [ Typ t; Complement (Typ t') ]) ]

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
    | Arrow (_, Complement _) -> failwith "?"
    | Arrow (a, Var x) -> `Arrow (a, `Var x)
    | Arrow (a, Typ t) -> simp (Typ (arrow_apply a t))

  let un t =
    (* Lift back to general form *)
    match t with
    | `Extreme dir -> Extreme dir
    | `Var x -> Var x
    | `Typ t -> Typ t
    | `Combine (dir, t, t') -> Combine (dir, t, t')
    | `Complement (`Var x) -> Complement (Var x)
    | `Complement (`Typ t) -> Complement (Typ t)
    | `Arrow (a, `Var x) -> Arrow (a, Var x)

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
    | `Extreme dir, `Arrow (_, t2) -> Extreme dir *<=* un t2
    | `Arrow (_, t1), `Extreme dir -> un t1 *<=* Extreme dir
    (* This case would trigger nondeterministically for both of the latter reductions,
       so we produce both the adjoint-equivalent bounds *)
    | `Arrow (a1, `Var x1), `Arrow (a2, `Var x2) ->
        (Arrow (arrow_compose (arrow_left_adjoint a2) a1, Var x1) *<=* Var x2)
        @ (Var x1 *<=* Arrow (arrow_compose (arrow_right_adjoint a1) a2, Var x2))
    | t1, `Arrow (a, `Var x) -> Arrow (arrow_left_adjoint a, un t1) *<=* Var x
    | `Arrow (a, `Var x), t2 -> Var x *<=* Arrow (arrow_right_adjoint a, un t2)

  and ( *<=* ) lower upper = atomize ~lower ~upper

  let rec atomize_constraint : Constraint.t -> bound list = function
    | With (_, c) -> atomize_constraint c
    | Flow { sub; sup } -> atomize ~lower:sub ~upper:sup
    | All cs -> List.concat_map ~f:atomize_constraint cs
end

module TypeExpr = struct
  open Type

  type t =
    | Var of Var.t
    | Lit of int
    | Add of t * t
    | Let of Var.t * t * t
    | Tuple of t list
    | Function of Var.t * t
    | Apply of t * t
    | Construct of t Label.Map.t
    | Project of t * Label.t
    | Extend of Label.t * t * t

  let rec go (env : Type.alg Var.Map.t) : t -> Type.alg Constrained.t =
    let open Constrained in
    let return_typ t = return (Typ t) in
    function
    | Var x -> return (Map.find_exn env x)
    | Lit _ -> return_typ Int
    | Add (e, e') ->
        let* e = go env e in
        let* e' = go env e' in
        let* () = e <: Typ Int and* () = e' <: Typ Int in
        return_typ Int
    | Let (x, e, e') ->
        let$ x_ = () in
        let* e = go env e in
        let* () = e <: x_ in
        go (Map.add_exn env ~key:x ~data:x_) e'
    | Tuple ts ->
        let* ts = all (List.map ~f:(go env) ts) in
        return_typ (Tuple ts)
    | Function (x, e) ->
        let$ x_ = () in
        let* e = go (Map.add_exn env ~key:x ~data:x_) e in
        return_typ (Function (x_, e))
    | Apply (e, e') ->
        let$ arg = () in
        let$ res = () in
        let* e = go env e and* e' = go env e' in
        let* () = e <: Typ (Function (arg, res)) and* () = e' <: arg in
        return res
    | Construct fs ->
        let* fs =
          all_in_map (Map.map fs ~f:(fun e -> Field.Present (go env e)))
        in
        return_typ (Record (fs, `Absents))
    | Project (e, f) ->
        let$ f_ = () in
        let* e = go env e in
        let* () =
          e
          <: Typ (Record (Label.Map.singleton f (Field.Present f_), `Unknowns))
        in
        return f_
    | Extend (f, e, e') ->
        let$ r = () in
        let* e = go env e and* e' = go env e' in
        let* () =
          e' <: Typ (Record (Label.Map.singleton f Field.Absent, `Unknowns))
        and* () =
          r <: Arrow (RecordUpdate (Label.Map.singleton f (Field.Present e)), e')
        in
        return r
end

let%expect_test "" =
  let test e =
    let t, c = Constrained.unwrap (TypeExpr.go Var.Map.empty e) in
    let c = Constraint.simp c in
    print_s [%message (t : Type.alg)];
    print_s [%message (c : Constraint.t)];
    print_s [%message (Solver.atomize_constraint c : Solver.bound list)]
  in
  test
    TypeExpr.(
      Project
        ( Construct
            (Label.Map.of_alist_exn
               [
                 (Label.of_string "foo", Lit 5);
                 (Label.of_string "bar", Tuple [ Lit 1; Lit 2 ]);
               ]),
          Label.of_string "foo" ));
  [%expect
    {|
    (t (Var $1))
    (c
     (With $1
      (Flow
       (sub
        (Typ
         (Record
          ((bar (Present (Typ (Tuple ((Typ Int) (Typ Int))))))
           (foo (Present (Typ Int))))
          Absents)))
       (sup (Typ (Record ((foo (Present (Var $1)))) Unknowns))))))
    ("Solver.atomize_constraint c" ((Lower (Typ Int) $1)))
    |}];
  test
    TypeExpr.(
      Function
        ( Var.of_string "x",
          Function
            ( Var.of_string "y",
              Add (Var (Var.of_string "x"), Var (Var.of_string "y")) ) ));
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
    TypeExpr.(
      Function
        ( Var.of_string "x",
          Function
            ( Var.of_string "y",
              Project
                ( Project (Var (Var.of_string "x"), Label.of_string "foo"),
                  Label.of_string "bar" ) ) ));
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
            (sup (Typ (Record ((foo (Present (Var $7)))) Unknowns)))))
          (Flow (sub (Var $7))
           (sup (Typ (Record ((bar (Present (Var $6)))) Unknowns))))))))))
    ("Solver.atomize_constraint c"
     ((Upper $4 (Typ (Record ((foo (Present (Var $7)))) Unknowns)))
      (Upper $7 (Typ (Record ((bar (Present (Var $6)))) Unknowns)))))
    |}];
  test
    TypeExpr.(
      Extend
        ( Label.of_string "foo",
          Lit 0,
          Construct (Label.Map.singleton (Label.of_string "foo") (Lit 1)) ));
  [%expect
    {|
    (t (Var $8))
    (c
     (With $8
      (All
       ((Flow (sub (Typ (Record ((foo (Present (Typ Int)))) Absents)))
         (sup (Typ (Record ((foo Absent)) Unknowns))))
        (Flow (sub (Var $8))
         (sup
          (Arrow (RecordUpdate ((foo (Present (Typ Int)))))
           (Typ (Record ((foo (Present (Typ Int)))) Absents)))))))))
    ("Solver.atomize_constraint c"
     ((Fail decompose
       ((Typ (Record ((foo (Present (Typ Int)))) Absents))
        (Typ (Record ((foo Absent)) Unknowns))))
      (Upper $8 (Typ (Record ((foo (Present (Typ Int)))) Absents)))))
    |}];
  test
    TypeExpr.(
      Extend
        ( Label.of_string "foo",
          Lit 0,
          Construct (Label.Map.singleton (Label.of_string "bar") (Lit 1)) ));
  [%expect
    {|
    (t (Var $9))
    (c
     (With $9
      (All
       ((Flow (sub (Typ (Record ((bar (Present (Typ Int)))) Absents)))
         (sup (Typ (Record ((foo Absent)) Unknowns))))
        (Flow (sub (Var $9))
         (sup
          (Arrow (RecordUpdate ((foo (Present (Typ Int)))))
           (Typ (Record ((bar (Present (Typ Int)))) Absents)))))))))
    ("Solver.atomize_constraint c"
     ((Upper $9
       (Typ
        (Record ((bar (Present (Typ Int))) (foo (Present (Typ Int)))) Absents)))))
    |}];
  test
    TypeExpr.(
      Function
        ( Var.of_string "x",
          Extend (Label.of_string "foo", Lit 0, Var (Var.of_string "x")) ));
  [%expect
    {|
    (t (Typ (Function (Var $10) (Var $11))))
    (c
     (With $10
      (With $11
       (All
        ((Flow (sub (Var $10)) (sup (Typ (Record ((foo Absent)) Unknowns))))
         (Flow (sub (Var $11))
          (sup (Arrow (RecordUpdate ((foo (Present (Typ Int))))) (Var $10)))))))))
    ("Solver.atomize_constraint c"
     ((Upper $10 (Typ (Record ((foo Absent)) Unknowns)))
      (Upper $11 (Arrow (RecordUpdate ((foo (Present (Typ Int))))) (Var $10)))))
    |}]
