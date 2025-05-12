open Core
open Lang.Sym
open Sup

module Entry = struct
  type 'a t = Top | Present of 'a | Bot [@@deriving sexp, equal, compare]

  let polar_map Polar.{ pos; neg = _ } = function
    | Top -> Top
    | Bot -> Bot
    | Present a -> Present (pos a)

  let map ~f = polar_map { pos = f; neg = f }

  let pretty a f : Sexp.t =
    match f with Present t -> a t | Bot -> Atom "!" | Top -> Atom "?"

  let combine latt first second =
    match (first, second) with
    | Top, x | x, Top -> (x, Top)
    | Bot, x | x, Bot -> (Bot, x)
    | Present x, Present y -> (Present (latt.meet x y), Present (latt.join x y))

  let meet latt x y = fst (combine latt x y)
  and join latt x y = snd (combine latt x y)
end

module Row (Key : String_id.S) : sig
  type rest = [ `Top | `Bot ]

  type 'a t = { m : 'a Entry.t Key.Map.t; rest : rest }
  [@@deriving sexp, equal, compare]

  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val t_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a t
  val sexp_of_t : ('a -> Sexp.t) -> 'a t -> Sexp.t
  val pretty : ('a -> Sexp.t) -> 'a t -> Sexp.t list
  val components : 'a t -> 'a list
  val polar_map : f:('a -> 'b) Polar.t -> 'a t -> 'b t
  val map : f:('a -> 'b) -> 'a t -> 'b t
  val lift : ('a Entry.t -> 'b Entry.t -> 'c Entry.t) -> 'a t -> 'b t -> 'c t
  val update : 'a t -> Key.t -> 'a Entry.t -> 'a t
  val field : 'a t -> Key.t -> 'a Entry.t
  val subs : 'a t -> 'b t -> ('a Entry.t * 'b Entry.t) Key.Map.t
end = struct
  type rest = [ `Top | `Bot ] [@@deriving sexp, equal, compare]

  and 'a t = { m : 'a Entry.t Key.Map.t; rest : [ `Top | `Bot ] }
  [@@deriving sexp, equal, compare]

  let un = function `Bot -> Entry.Bot | `Top -> Entry.Top

  let nu = function
    | Entry.Bot -> `Bot
    | Top -> `Top
    | Present _ ->
        failwith "Record cannot be marked as having all fields present"

  let pretty a { m; rest } =
    let open Sexp in
    (Core.Map.to_alist m
    |> List.map ~f:(fun (l, f) ->
           List [ Atom (Key.to_string l); Entry.pretty a f ]))
    @
    match rest with
    | `Bot -> [ Atom "|"; Atom "!" ]
    | `Top -> [ Atom "|"; Atom "?" ]

  let polar_map ~f { m; rest } = { m = Map.map ~f:(Entry.polar_map f) m; rest }
  let map ~f t = polar_map ~f:{ pos = f; neg = f } t
  let update { m; rest } key data = { m = Map.set m ~key ~data; rest }

  let components { m; rest = _ } =
    Map.data m
    |> List.concat_map ~f:(function Top | Bot -> [] | Present t -> [ t ])

  let field { m; rest } key = Map.find m key |> Option.value ~default:(un rest)

  let subs { m; rest } { m = m'; rest = rest' } =
    Map.merge m m' ~f:(fun ~key:_ -> function
      | `Both (t, t') -> Some (t, t')
      | `Left t -> Some (t, un rest')
      | `Right t' -> Some (un rest, t'))

  let lift f first second =
    {
      m = subs first second |> Map.map ~f:(fun (fd, fd') -> f fd fd');
      rest = nu (f (un first.rest) (un second.rest));
    }
end

module RowLabel = Row (Label)
module RowTag = Row (Tag)

type 'a star_typ =
  | Top
  | Bot
  | Int
  | Float
  | Fun of { arg : 'a; res : 'a }
  | Sized
  | Record of 'a RowLabel.t
  | Variant of 'a RowTag.t
  | Product of 'a RowLabel.t
  | Concat of 'a RowTag.t
  | Array of { lower : 'a; upper : 'a; elem : 'a }
[@@deriving sexp, equal, compare]

type star_simple = T of star_simple star_typ [@@deriving sexp, equal, compare]
type star_arrow = { iota : bool } [@@deriving sexp, equal, compare]

let combine latt first second =
  let same x = (x, x) in
  let flipped f = (f latt.meet latt.join, f latt.join latt.meet) in
  let rho lift x y = (lift (Entry.meet latt) x y, lift (Entry.join latt) x y) in
  let map f (x, y) = (f x, f y) in
  match (first, second) with
  | Top, x | x, Top -> (x, Top)
  | Bot, x | x, Bot -> (Bot, x)
  | Int, Int -> same Int
  | Float, Float -> same Float
  | Sized, Sized -> same Sized
  | Fun x, Fun y ->
      flipped (fun join meet ->
          Fun { arg = meet x.arg y.arg; res = join x.res y.res })
  | Record x, Record y -> map (fun r -> Record r) (rho RowLabel.lift x y)
  | Product x, Product y -> map (fun t -> Product t) (rho RowLabel.lift x y)
  | Variant x, Variant y -> map (fun t -> Variant t) (rho RowTag.lift x y)
  | Concat x, Concat y -> map (fun t -> Concat t) (rho RowTag.lift x y)
  | Array x, Array y ->
      flipped (fun join meet ->
          Array
            {
              lower = meet x.lower y.lower;
              upper = join x.upper y.upper;
              elem = join x.elem y.elem;
            })
  | _, _ -> (Bot, Top)

let%expect_test "" =
  let rec latt = { join; meet }
  and join (T x) (T y) = T (combine latt x y |> snd)
  and meet (T x) (T y) = T (combine latt x y |> fst) in
  let bnd x y = (meet (T x) (T y), join (T x) (T y)) in
  let test x y = print_s [%message (bnd x y : star_simple * star_simple)] in
  test Bot Top;
  [%expect {| ("bnd x y" ((T Bot) (T Top))) |}];
  test Bot Int;
  [%expect {| ("bnd x y" ((T Bot) (T Int))) |}];
  test Top Int;
  [%expect {| ("bnd x y" ((T Int) (T Top))) |}];
  test (Fun { arg = T Int; res = T Bot }) (Fun { arg = T Top; res = T Int });
  [%expect
    {|
    ("bnd x y"
     ((T (Fun (arg (T Top)) (res (T Bot))))
      (T (Fun (arg (T Int)) (res (T Int))))))
    |}];
  test
    (Array
       {
         lower =
           T
             (Product
                {
                  m =
                    Label.Map.of_alist_exn
                      [ (Label.of_string "x", Entry.Present (T Sized)) ];
                  rest = `Top;
                });
         upper =
           T
             (Product
                {
                  m =
                    Label.Map.of_alist_exn
                      [ (Label.of_string "x", Entry.Present (T Sized)) ];
                  rest = `Top;
                });
         elem = T Float;
       })
    (Array
       {
         lower =
           T
             (Product
                {
                  m =
                    Label.Map.of_alist_exn
                      [
                        (Label.of_string "x", Entry.Present (T Sized));
                        (Label.of_string "y", Entry.Present (T Sized));
                      ];
                  rest = `Top;
                });
         upper = T (Product { m = Label.Map.empty; rest = `Top });
         elem = T Float;
       });
  [%expect
    {|
    ("bnd x y"
     ((T
       (Array
        (lower (T (Product ((m ((x (Present (T Sized))) (y Top))) (rest Top)))))
        (upper (T (Product ((m ((x (Present (T Sized))))) (rest Top)))))
        (elem (T Float))))
      (T
       (Array
        (lower
         (T
          (Product
           ((m ((x (Present (T Sized))) (y (Present (T Sized))))) (rest Top)))))
        (upper (T (Product ((m ((x Top))) (rest Top))))) (elem (T Float))))))
    |}]

module StarTypeSystem :
  TypeSystem with type 'a typ = 'a star_typ and type arrow = star_arrow = struct
  type nonrec 'a typ = 'a star_typ [@@deriving sexp, equal, compare]
  type simple = star_simple
  type arrow = star_arrow [@@deriving sexp, equal, compare]

  let pretty pretty_t t =
    let open Sexp in
    match t with
    | Top -> Atom "top"
    | Bot -> Atom "bot"
    | Int -> Atom "int"
    | Float -> Atom "float"
    | Sized -> Atom "#"
    | Fun { arg; res } -> List [ pretty_t arg; Atom "->"; pretty_t res ]
    | Record row ->
        List ([ Atom "{" ] @ RowLabel.pretty pretty_t row @ [ Atom "}" ])
    | Product row ->
        List ([ Atom "{!" ] @ RowLabel.pretty pretty_t row @ [ Atom "!}" ])
    | Variant row ->
        List ([ Atom "[" ] @ RowTag.pretty pretty_t row @ [ Atom "]" ])
    | Concat row ->
        List ([ Atom "[!" ] @ RowTag.pretty pretty_t row @ [ Atom "!]" ])
    | Array { lower; upper; elem } ->
        List
          [
            Atom "[";
            pretty_t lower;
            Atom "..";
            pretty_t upper;
            Atom "]";
            pretty_t elem;
          ]

  let polar_map ~f:Polar.{ pos; neg } = function
    | Top -> Top
    | Bot -> Bot
    | Int -> Int
    | Float -> Float
    | Fun { arg; res } -> Fun { arg = neg arg; res = pos res }
    | Sized -> Sized
    | Record row -> Record (RowLabel.map ~f:pos row)
    | Product row -> Product (RowLabel.map ~f:pos row)
    | Variant row -> Variant (RowTag.map ~f:pos row)
    | Concat row -> Concat (RowTag.map ~f:pos row)
    | Array { lower; upper; elem } ->
        Array { lower = neg lower; upper = pos upper; elem = pos elem }

  let map ~f = polar_map ~f:{ pos = f; neg = f }
  let unwrap (T t) = t
  let () = ignore (T Top)

  let components =
    let open Polar in
    function
    | Top -> { pos = []; neg = [] }
    | Bot -> { pos = []; neg = [] }
    | Int -> { pos = []; neg = [] }
    | Float -> { pos = []; neg = [] }
    | Fun { arg; res } -> { pos = [ res ]; neg = [ arg ] }
    | Sized -> { pos = []; neg = [] }
    | Record row -> { pos = RowLabel.components row; neg = [] }
    | Product row -> { pos = RowLabel.components row; neg = [] }
    | Variant row -> { pos = RowTag.components row; neg = [] }
    | Concat row -> { pos = RowTag.components row; neg = [] }
    | Array { lower; upper; elem } -> { pos = [ upper; elem ]; neg = [ lower ] }

  let entry_decompose sexp ((lower, upper) : 'a Entry.t * 'a Entry.t) :
      ('a * 'a) list Or_error.t =
    match (lower, upper) with
    | Bot, _ | _, Top -> Ok []
    | Present t, Present t' -> Ok [ (t, t') ]
    | Top, Present _ | (Present _ | Top), Bot ->
        let lower = Entry.pretty sexp lower
        and upper = Entry.pretty sexp upper in
        error_s
          [%message
            "Incompatible record fields" (lower : Sexp.t) (upper : Sexp.t)]

  let decompose sexp ((lower : 'a typ), (upper : 'a typ)) :
      ('a * 'a) list Or_error.t =
    let rho subs =
      subs |> Map.to_alist
      |> List.map ~f:(fun (_, (f, f')) -> entry_decompose sexp (f, f'))
      |> Or_error.all
      |> Or_error.map ~f:List.concat
    in
    match (lower, upper) with
    | _, Top | Bot, _ -> Ok []
    | Int, Int | Float, Float | Sized, Sized -> Ok []
    | Fun { arg; res }, Fun { arg = arg'; res = res' } ->
        Ok [ (res, res'); (arg', arg) ]
    | Record x, Record y -> RowLabel.subs x y |> rho
    | Product x, Product y -> RowLabel.subs x y |> rho
    | Variant x, Variant y -> RowTag.subs x y |> rho
    | Concat x, Concat y -> RowTag.subs x y |> rho
    | Array a, Array b ->
        Ok [ (b.lower, a.lower); (a.upper, b.upper); (a.elem, b.elem) ]
    | _ ->
        let lower = pretty sexp lower and upper = pretty sexp upper in
        error_s
          [%message "Incompatible types" (lower : Sexp.t) (upper : Sexp.t)]

  let top = Top
  and bot = Bot

  let join l x y = snd (combine l x y)
  and meet l x y = fst (combine l x y)

  module Arrow = struct
    type t = arrow [@@deriving sexp, equal, compare]

    let pretty { iota } = if iota then Sexp.Atom "iota" else Sexp.List []
    let id = { iota = false }
    let is_id { iota } = not iota
    let compose x y = if x.iota then { iota = not y.iota } else y

    let apply { iota } t =
      match iota with
      | false -> t
      | true -> (
          match t with
          | Int -> Sized
          | Sized -> Int
          | Record x -> Product x
          | Product x -> Record x
          | Variant x -> Concat x
          | Concat x -> Variant x
          | t -> t)

    let swap_left wrap { iota } = ({ iota }, wrap Top)
    let swap_right wrap { iota } = ({ iota }, wrap Bot)
  end
end

module Expr = struct
  type t =
    | Int of int
    | Float of float
    | IntOp of t * t
    | FloatOp of t * t
    | Var of Var.t
    | Let of Var.t * t * t
    | Lam of Var.t * t
    | App of t * t
    | Record of (Label.t * t) list
    | Project of t * Label.t
    | Tag of Tag.t * t
    | Match of t * (Label.t * Var.t * t) list
    | Array of Var.t * t * t
    | Index of t * t
    | Shape of t
    | Size of t
    | Len of t
    | Product of (Label.t * t) list
    | Dimension of t * Label.t
    | Concat of (Tag.t * t) list
    | Component of t * Tag.t
    | Broadcast of t * t
end

module StarTyper = struct
  module Type = Type (StarTypeSystem)
  module Constrained = Constrained (StarTypeSystem)
  module Solver = Solver (StarTypeSystem)
  module Sig = Sig.Make (StarTypeSystem)
  open Type

  let all_in_entry fd =
    let open Entry in
    match fd with
    | Top -> Constrained.wrap (Top, Constraint.truth)
    | Bot -> Constrained.wrap (Bot, Constraint.truth)
    | Present t ->
        let t, c = Constrained.unwrap t in
        Constrained.wrap (Present t, c)

  let rec alg_of_typ t =
    typ (StarTypeSystem.map ~f:alg_of_typ (StarTypeSystem.unwrap t))

  let push x x_ (env : _ Var.Map.t) = Map.add_exn ~key:x ~data:x_ env

  let rec go (env : Alg.t Var.Map.t) : Expr.t -> Alg.t Constrained.t =
    let open Constrained in
    let iota = apply { iota = true } in
    let return_typ t = return (typ t) in
    let hyp x = Map.find_exn env x in
    let cons of_alist r =
      all_in_map
        (List.map r ~f:(fun (l, e) -> (l, e))
        |> of_alist
        |> Map.map ~f:(fun e -> Entry.Present (go env e))
        |> Map.map ~f:all_in_entry)
    in
    let lu () =
      let$ lower = () in
      let$ upper = () in
      let* () = lower <: upper in
      return (lower, upper)
    in
    function
    | Int _ -> return_typ Int
    | Float _ -> return_typ Float
    | IntOp (e, e') ->
        let* e = go env e and* e' = go env e' in
        let* () = e <: typ Int and* () = e' <: typ Int in
        return_typ Int
    | FloatOp (e, e') ->
        let* e = go env e and* e' = go env e' in
        let* () = e <: typ Float and* () = e' <: typ Float in
        return_typ Float
    | Var x -> return (hyp x)
    | Let (x, e, e') ->
        let$ t = () in
        let* e = go env e in
        let* () = e <: t in
        go (push x t env) e'
    | Lam (x, e) ->
        let$ t = () in
        let* e = go (push x t env) e in
        return_typ (Fun { arg = t; res = e })
    | App (e, e') ->
        let$ res = () in
        let* e = go env e and* e' = go env e' in
        let* () = e <: typ (Fun { arg = e'; res }) in
        return res
    | Size e ->
        let* e = go env e in
        let* () = e <: typ Int in
        return_typ Sized
    | Len e ->
        let* e = go env e in
        let* () = e <: typ Sized in
        return_typ Int
    | Array (x, e, e') ->
        let$ t = () in
        let* e = go env e in
        let* elem = go (push x t env) e' in
        let lower = iota t and upper = e in
        let* () = lower <: upper in
        return_typ (Array { lower; upper; elem })
    | Index (e, e') ->
        let* lower, upper = lu () in
        let$ elem = () in
        let* e = go env e in
        let* e' = go env e' in
        let* () = e <: typ (Array { lower; upper; elem }) in
        let* () = iota e' <: lower in
        return elem
    | Shape e ->
        let* lower, upper = lu () in
        let$ elem = () in
        let* e = go env e in
        let* () = e <: typ (Array { lower; upper; elem }) in
        return upper
    | Record r ->
        let* m = cons Label.Map.of_alist_exn r in
        return_typ (Record { m; rest = `Top })
    | Product r ->
        let* m = cons Label.Map.of_alist_exn r in
        return_typ (Product { m; rest = `Top })
    | Concat r ->
        let* m = cons Tag.Map.of_alist_exn r in
        return_typ (Concat { m; rest = `Top })
    | Project (e, l) ->
        let open Label.Map in
        let$ t = () in
        let* e = go env e in
        let* () =
          e <: typ (Record { m = singleton l (Entry.Present t); rest = `Top })
        in
        return t
    | Dimension (e, l) ->
        let open Label.Map in
        let$ t = () in
        let* e = go env e in
        let* () =
          e <: typ (Product { m = singleton l (Entry.Present t); rest = `Top })
        in
        return t
    | Component (e, l) ->
        let open Tag.Map in
        let$ t = () in
        let* e = go env e in
        let* () =
          e <: typ (Concat { m = singleton l (Entry.Present t); rest = `Top })
        in
        return t
    | Tag _ -> failwith "Tag"
    | Match _ -> failwith "Match"
    | Broadcast (_, _) -> failwith "Broadcast"
end

let%expect_test "" =
  let test e =
    let open StarTyper in
    curr_type_var := 0;
    let t, c = Constrained.unwrap (go Var.Map.empty e) in
    (* print_s [%message (t : StarTyper.Type.Alg.t) (c : Type.Alg.t Constraint.t)]; *)
    let c = Constraint.simp c in
    print_s [%message (c : Type.Alg.t Constraint.t)];
    match Solver.run c with
    | Ok bounds ->
        (* print_s
          [%message
            (bounds
              : (StarTyper.Type.DNF.t * StarTyper.Type.CNF.t) Type_var.Map.t)
              (Type.dnf t : StarTyper.Type.DNF.t)]; *)
        let s = Sig.t bounds (Type.dnf t) in
        print_s [%message (Sig.pretty s : Sexp.t)]
    | Error err -> print_s [%message (err : Error.t)]
  in
  let v x = Var.of_string x in
  let vv x = Expr.Var (v x) in
  let lab x = Label.of_string x in
  test (Int 0);
  [%expect {| ("Sig.pretty s" int) |}];
  (* IMPROVE: simplify this further? *)
  test (Array (v "i", Size (Int 10), vv "i"));
  [%expect {| ("Sig.pretty s" ([ (& (iota $1) #) .. # ] $1)) |}];
  test (Array (v "i", Size (Int 10), IntOp (vv "i", Int 0)));
  [%expect {| ("Sig.pretty s" ([ # .. # ] int)) |}];
  (* IMPROVE: this should probably raise a type error - the type is useless
              it is related to above: the only non-bot iota under # is int *)
  test (Array (v "i", Size (Int 10), FloatOp (vv "i", Float 0.0)));
  [%expect {| ("Sig.pretty s" ([ bot .. # ] float)) |}];
  test (Lam (v "x", Index (vv "x", Int 0)));
  [%expect {| ("Sig.pretty s" (([ # .. top ] $4) -> $4)) |}];
  test (Lam (v "s", Shape (Array (v "x", vv "s", vv "x"))));
  (* IMPROVE: simplify x & y -> x | y, also up to iota applications *)
  [%expect {| ("Sig.pretty s" ((& $1 $3) -> (| $1 $3))) |}];
  test
    (Let
       ( v "x",
         Array (v "i", Size (Int 10), Int 1),
         Let (v "y", Array (v "i", Size (Int 5), Index (vv "x", vv "i")), vv "y")
       ));
  [%expect {| ("Sig.pretty s" ([ # .. # ] int)) |}];
  test (Lam (v "a", Index (vv "a", Record [ (lab "i", Int 0) ])));
  [%expect {| ("Sig.pretty s" (([ ({! (i int) | ? !}) .. top ] $4) -> $4)) |}];
  test (Array (v "x", Product [ (lab "a", Int 5); (lab "b", Int 4) ], vv "x"));
  [%expect
    {|
    ("Sig.pretty s"
     ([ (& (iota $1) ({! (a int) (b int) | ? !})) .. ({! (a int) (b int) | ? !})
      ] $1))
    |}];
  test
    (Array
       ( v "x",
         Product [ (lab "a", Int 5); (lab "b", Int 4) ],
         IntOp (Project (vv "x", lab "a"), Project (vv "x", lab "b")) ));
  [%expect
    {|
    ("Sig.pretty s"
     ([ ({! (a int) (b int) | ? !}) .. ({! (a int) (b int) | ? !}) ] int))
    |}];
  test
    (Lam
       ( v "a",
         Lam (v "b", FloatOp (Index (vv "a", Int 0), Index (vv "b", Int 0))) ));
  [%expect
    {| ("Sig.pretty s" (([ # .. top ] float) -> (([ # .. top ] float) -> float))) |}];
  (* FIXME: mis-applied iota? *)
  test
    (Lam
       ( v "a",
         Array
           ( v "x",
             Product [ (lab "a", Shape (vv "a")) ],
             FloatOp (Index (vv "a", Project (vv "x", lab "a")), Float 0.0) ) ));
  [%expect
    {|
    ("Sig.pretty s"
     (([ (| $6 (iota $9)) .. $4 ] float) ->
      ([ ({! (a (& $4 (iota $6) $9)) | ? !}) .. ({! (a $4) | ? !}) ] float)))
    |}];
  test
    (Lam
       ( v "a",
         Lam
           ( v "b",
             Array
               ( v "x",
                 Product
                   [ (lab "a", Shape (vv "a")); (lab "b", Shape (vv "b")) ],
                 FloatOp
                   ( Index (vv "a", Project (vv "x", lab "a")),
                     Index (vv "b", Project (vv "x", lab "b")) ) ) ) ));
  [%expect
    {|
    ("Sig.pretty s"
     (([ (| $10 (iota $13)) .. $5 ] float) ->
      (([ (| $14 (iota $17)) .. $8 ] float) ->
       ([ ({! (a (& (iota $10) $13 $5)) (b (& (iota $14) $17 $8)) | ? !}) ..
        ({! (a $5) (b $8) | ? !}) ] float))))
    |}]
