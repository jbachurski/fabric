open Core
open Lang.Sym

let next_type_var =
  let cnt = ref 0 in
  fun () ->
    cnt := !cnt + 1;
    Type_var.of_string ("$" ^ string_of_int !cnt)

type ('a, 'args) massage = ('a -> Sexp.t) -> 'args -> ('a * 'a) list Or_error.t
type 'a lattice = { join : 'a -> 'a -> 'a; meet : 'a -> 'a -> 'a }

module type TypeSystem = sig
  type 'a typ [@@deriving sexp, equal, compare]
  type simple
  type arrow

  val pretty : ('a -> Sexp.t) -> 'a typ -> Sexp.t
  val map : f:('a -> 'b) -> 'a typ -> 'b typ
  val unwrap : simple -> simple typ
  val decompose : ('a, 'a typ * 'a typ) massage
  val is_top : ('a, 'a typ) massage
  val is_bot : ('a, 'a typ) massage
  val top : 'a typ
  val bot : 'a typ
  val join : 'a lattice -> 'a typ -> 'a typ -> 'a typ
  val meet : 'a lattice -> 'a typ -> 'a typ -> 'a typ

  module Arrow : sig
    type t = arrow [@@deriving sexp, equal, compare]

    val id : t
    val is_id : t -> bool
    val compose : t -> t -> t
    val apply : t -> 'a typ -> 'a typ
    val left_adjoint : t -> t
    val right_adjoint : t -> t
  end
end

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

  module Arrow = struct
    open Lang.Fabric.Type

    type t = fabric_arrow = { records : dir Label.Map.t }
    [@@deriving sexp, equal, compare]

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

module type TypeSystem1 = sig
  type 'a typ [@@deriving sexp, equal, compare]
  type simple
  type arrow

  val pretty : ('a -> Sexp.t) -> 'a typ -> Sexp.t
  val map : f:('a -> 'b) -> 'a typ -> 'b typ
  val unwrap : simple -> simple typ
  val is_top : ('a, 'a typ) massage
  val is_bot : ('a, 'a typ) massage
  val top : 'a typ
  val bot : 'a typ
  val join : 'a lattice -> 'a typ -> 'a typ -> 'a typ
  val meet : 'a lattice -> 'a typ -> 'a typ -> 'a typ
  val join_token : string
  val meet_token : string

  module Arrow : sig
    type t = arrow [@@deriving sexp, equal, compare]

    val id : t
    val is_id : t -> bool
    val compose : t -> t -> t
    val apply : t -> 'a typ -> 'a typ
  end
end

module FabricTypeSystem1 : TypeSystem1 = struct
  include FabricTypeSystem

  let join_token = "|"
  and meet_token = "&"
end

module type NF0 = sig
  type 't typ
  type arrow

  module Var : sig
    module T : sig
      type t = { var : Type_var.t; neg : bool; app : arrow }
      [@@deriving sexp, equal, compare]
    end

    type t = T.t = { var : Type_var.t; neg : bool; app : arrow }
    [@@deriving sexp, equal, compare]

    module Set : Set.S with type Elt.t = t
  end

  type clause = { vars : Var.Set.t; pos_typ : t typ; neg_typ : t typ }
  [@@deriving sexp, equal, compare]

  and t = clause list [@@deriving sexp, equal, compare]
end

module type NF = sig
  type 't typ
  type arrow

  include NF0 with type 't typ := 't typ and type arrow := arrow

  val pretty : t -> Sexp.t
  val top : t
  val bot : t
  val typ : t typ -> t
  val var : Type_var.t -> t
  val join : t -> t -> t
  val meet : t -> t -> t
  val negate : t -> t
  val apply : arrow -> t -> t
  val lattice : t lattice

  val interpret :
    top:'a ->
    bot:'a ->
    typ:('a typ -> 'a) ->
    var:(Type_var.t -> 'a) ->
    join:('a -> 'a -> 'a) ->
    meet:('a -> 'a -> 'a) ->
    negate:('a -> 'a) ->
    apply:(arrow -> 'a -> 'a) ->
    t ->
    'a
end

module DNF (M : TypeSystem1) :
  NF with type 't typ := 't M.typ and type arrow := M.Arrow.t = struct
  module Var = struct
    module T = struct
      type t = { var : Type_var.t; neg : bool; app : M.Arrow.t }
      [@@deriving sexp, equal, compare]
    end

    include T

    let pretty { var; neg; app } =
      let open Sexp in
      let x = Atom (Type_var.to_string var) in
      match (neg, M.Arrow.is_id app) with
      | false, true -> x
      | true, true -> List [ Atom "~"; x ]
      | false, false -> List [ M.Arrow.sexp_of_t app; x ]
      | true, false -> List [ Atom "~"; M.Arrow.sexp_of_t app; x ]

    let var x = { var = x; neg = false; app = M.Arrow.id }
    let negate t = { t with neg = not t.neg }
    let apply a t = { t with app = M.Arrow.compose a t.app }

    module Set = Set.Make (T)
  end

  type clause = { vars : Var.Set.t; pos_typ : t M.typ; neg_typ : t M.typ }
  [@@deriving sexp, equal, compare]

  and t = clause list [@@deriving sexp, equal, compare]

  let must_be_top ty =
    match M.is_top (Fn.const (Sexp.Atom "")) ty with
    | Ok [] -> true
    | _ -> false

  let must_be_bot ty =
    match M.is_bot (Fn.const (Sexp.Atom "")) ty with
    | Ok [] -> true
    | _ -> false

  let must_be_sub ty ty' =
    must_be_bot ty || must_be_top ty' || [%equal: t M.typ] ty ty'

  let rec pretty_clause { vars; pos_typ; neg_typ } =
    let open Sexp in
    let os =
      List.map ~f:Var.pretty (Core.Set.to_list vars)
      @ (if must_be_top pos_typ then [] else [ M.pretty pretty pos_typ ])
      @
      if must_be_bot neg_typ then []
      else [ List [ Atom "~"; M.pretty pretty neg_typ ] ]
    in
    match os with
    | [] -> M.pretty pretty M.top
    | [ c ] -> c
    | os -> List (Atom M.meet_token :: os)

  and pretty =
    let open Sexp in
    function
    | [] -> M.pretty pretty M.bot
    | [ c ] -> pretty_clause c
    | t -> List ([ Atom M.join_token ] @ List.map ~f:pretty_clause t)

  let rec _simple t : t =
    [
      {
        vars = Var.Set.empty;
        pos_typ = M.map ~f:(fun t -> _simple t) (M.unwrap t);
        neg_typ = M.bot;
      };
    ]

  let _bot_clause = { vars = Var.Set.empty; pos_typ = M.bot; neg_typ = M.top }
  let top_clause = { vars = Var.Set.empty; pos_typ = M.top; neg_typ = M.bot }
  let bot : t = []
  let top : t = [ top_clause ]
  let typ typ : t = [ { top_clause with pos_typ = typ } ]
  let var x = [ { top_clause with vars = Var.Set.singleton (Var.var x) } ]

  let simplify cs =
    (* Deduplicate *)
    List.dedup_and_sort cs ~compare:compare_clause
    (* Eliminate clauses which are trivially bottom *)
    |> List.filter ~f:(fun { vars = _; pos_typ; neg_typ } ->
           not (must_be_bot pos_typ || must_be_top neg_typ))
    (* Eliminate subsumed clauses *)
    |> List.filter ~f:(fun c ->
           List.exists cs ~f:(fun c' ->
               (not (equal_clause c c'))
               && Set.is_subset c'.vars ~of_:c.vars
               && must_be_sub c.pos_typ c'.pos_typ
               && must_be_sub c'.neg_typ c.neg_typ)
           |> not)
    |> List.filter ~f:(fun c ->
           Set.exists c.vars ~f:(fun x -> Set.mem c.vars (Var.negate x)) |> not)

  let apply a t =
    List.map t ~f:(fun { vars; pos_typ; neg_typ } ->
        {
          vars = Var.Set.map vars ~f:(fun x -> Var.apply a x);
          pos_typ = M.Arrow.apply a pos_typ;
          neg_typ = M.Arrow.apply a neg_typ;
        })

  let join t t' = t @ t' |> simplify

  let rec meet_clause t t' =
    {
      vars = Set.union t.vars t'.vars;
      pos_typ = M.meet lattice t.pos_typ t'.pos_typ;
      neg_typ = M.join lattice t.neg_typ t'.neg_typ;
    }

  and meet t t' =
    List.cartesian_product t t'
    |> List.map ~f:(fun (c, c') -> meet_clause c c')
    |> simplify

  and lattice = { join; meet }

  let negate_clause t =
    List.map (Set.to_list t.vars) ~f:(fun x ->
        { top_clause with vars = Var.Set.singleton (Var.negate x) })
    @ [
        { top_clause with pos_typ = t.neg_typ };
        { top_clause with neg_typ = t.pos_typ };
      ]

  let negate t = List.map t ~f:negate_clause |> List.fold ~init:top ~f:meet

  let interpret ~top ~bot ~typ ~var ~join ~meet ~negate ~apply =
    let rec go_clause { vars; pos_typ; neg_typ } =
      meet
        (Set.fold vars ~init:top ~f:(fun acc { var = x; neg; app } ->
             let r = apply app (var x) in
             let r = match neg with false -> r | true -> negate r in
             meet acc r))
        (meet (typ (M.map ~f:go pos_typ)) (negate (typ (M.map ~f:go neg_typ))))
    and go t =
      List.fold t ~init:bot ~f:(fun acc clause -> join acc (go_clause clause))
    in
    go
end

let%expect_test "DNF" =
  let open DNF (FabricTypeSystem1) in
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
  |}]

module CNF (M : TypeSystem1) :
  NF with type 't typ := 't M.typ and type arrow := M.Arrow.t = struct
  module M' = struct
    type 't typ = 't M.typ [@@deriving sexp, equal, compare]
    type simple = M.simple
    type arrow = M.arrow

    let pretty = M.pretty
    let map = M.map
    let unwrap = M.unwrap

    module Arrow = M.Arrow

    let is_top = M.is_bot
    and is_bot = M.is_top

    let top = M.bot
    and bot = M.top

    let join = M.meet
    and meet = M.join

    let join_token = M.meet_token
    and meet_token = M.join_token
  end

  module T = DNF (M')
  include T

  let top = T.bot
  and bot = T.top

  let typ = T.typ
  let var = T.var

  let join = T.meet
  and meet = T.join
  and lattice = { join = T.lattice.meet; meet = T.lattice.join }

  let negate = T.negate
  let apply = T.apply

  let interpret ~top ~bot ~typ ~var ~join ~meet ~negate ~apply t =
    T.interpret ~top:bot ~bot:top ~typ ~var ~join:meet ~meet:join ~negate ~apply
      t
end

let%expect_test "CNF" =
  let open CNF (FabricTypeSystem1) in
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
  [%expect {| ("((a + b) * (b + c)) * (c + a)" (& (| a b) (| a c) (| b c))) |}];
  print_s [%message ((a * b) + (b * c) + (c * a) : t)];
  [%expect {| ("((a * b) + (b * c)) + (c * a)" (& (| a b) (| a c) (| b c))) |}]

module FabricCNF = CNF (FabricTypeSystem1)
module FabricDNF = DNF (FabricTypeSystem1)

let fabric_cnf_to_dnf t =
  let open FabricDNF in
  FabricCNF.interpret ~top ~bot ~typ ~var ~join ~meet ~negate ~apply t

let fabric_dnf_to_cnf t =
  let open FabricCNF in
  FabricDNF.interpret ~top ~bot ~typ ~var ~join ~meet ~negate ~apply t

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

module Type (M : TypeSystem) = struct
  open M
  open Lang.Sym

  module Normal = DNF (struct
    include M

    let join_token = "|"
    and meet_token = "&"
  end)

  module Alg = struct
    type dir = Bot | Top [@@deriving sexp, equal, compare]

    type t =
      | Var of Type_var.t
      | Typ of t typ
      | Apply of M.Arrow.t * t
      | Combine of dir * t * t
      | Complement of t
    [@@deriving sexp, equal, compare]

    let join t t' = Combine (Top, t, t')
    let meet t t' = Combine (Bot, t, t')
    let lattice = { join; meet }
  end

  let var x = Alg.Var x
  let typ t = Alg.Typ t
  let apply a t = Alg.Apply (a, t)

  let rec normalise : Alg.t -> Normal.t =
    let open Normal in
    function
    | Var x -> var x
    | Typ t -> typ (map ~f:normalise t)
    | Apply (a, t) -> apply a (normalise t)
    | Combine (Top, t, t') -> join (normalise t) (normalise t')
    | Combine (Bot, t, t') -> meet (normalise t) (normalise t')
    | Complement t -> negate (normalise t)
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

  type bound = Lower of Alg.t * Type_var.t | Upper of Type_var.t * Alg.t
  [@@deriving sexp]

  type dir = Alg.dir = Bot | Top

  let concat_map_or_error xs ~f =
    List.map xs ~f |> Or_error.all |> Or_error.map ~f:List.concat

  let inv = function Top -> Bot | Bot -> Top

  (* Lift back to general form *)
  let un t : Alg.t =
    match t with
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
    | Var x -> `Var x
    | Typ t -> `Typ t
    | Combine (dir, t, t') -> `Combine (dir, t, t')
    (* Complements *)
    | Complement (Complement t) -> simp t
    | Complement (Combine (dir, t, t')) ->
        `Combine (inv dir, Complement t, Complement t')
    | Complement (Var x) -> `Complement (`Var x)
    | Complement (Typ t) -> `Complement (`Typ t)
    | Complement (Apply (a, t)) -> simp (Apply (a, Complement t))
    (* Arrows *)
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
    let join = M.join Alg.lattice in
    let meet = M.meet Alg.lattice in
    match (simp lower, simp upper) with
    (* Atomic bounds *)
    | `Var x1, `Var x2 -> Ok [ Lower (Var x1, x2); Upper (x1, Var x2) ]
    | `Var x, t2 -> Ok [ Upper (x, un t2) ]
    | t1, `Var x -> Ok [ Lower (un t1, x) ]
    (* Decompose inequality on type constructors *)
    | `Typ lower, `Typ upper ->
        M.decompose Alg.sexp_of_t (lower, upper) |> atomize_decomposition
    (* Joins and meets *)
    | `Combine (Top, t1, t1'), t2 -> (t1 *<=* un t2) @@ (t1' *<=* un t2)
    | t1, `Combine (Bot, t2, t2') -> (un t1 *<=* t2) @@ (un t1 *<=* t2')
    (* Wrong! *)
    | `Combine (Bot, t1, t1'), t2 -> t1 *<=* Combine (Top, Complement t1', un t2)
    | t1, `Combine (Top, t2, t2') ->
        Combine (Bot, un t1, Complement t2) *<=* t2'
    (* Complements *)
    | `Complement t1, `Complement t2 -> un t2 *<=* un t1
    | `Complement (`Typ t1), `Typ t2 ->
        M.is_top Alg.sexp_of_t (join t1 t2) |> atomize_decomposition
    | `Typ t1, `Complement (`Typ t2) ->
        M.is_bot Alg.sexp_of_t (meet t1 t2) |> atomize_decomposition
    | t1, `Complement (`Var x) -> Var x *<=* Complement (un t1)
    | `Complement (`Var x), t2 -> Complement (un t2) *<=* Var x
    (* Arrows *)
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

  let collect_bounds atomic_bounds =
    let open Alg in
    List.fold atomic_bounds ~init:Type_var.Map.empty ~f:(fun acc -> function
      | Lower (l, u) ->
          Map.update acc u ~f:(fun v ->
              let low, high = Option.value v ~default:(Typ M.bot, Typ M.top) in
              (Combine (Top, l, low), high))
      | Upper (l, u) ->
          Map.update acc l ~f:(fun v ->
              let low, high = Option.value v ~default:(Typ M.bot, Typ M.top) in
              (low, Combine (Bot, high, u))))
    |> Map.map ~f:(fun (low, high) -> (normalise low, normalise high))

  let init c = atomize_constraint c |> Or_error.map ~f:collect_bounds

  let iter normal_bounds =
    let open Alg in
    Map.to_alist normal_bounds
    |> concat_map_or_error ~f:(fun (x, (lower, upper)) ->
           let algebraise = Obj.magic in
           let lower, upper = (algebraise lower, algebraise upper) in
           (lower *<=* Var x) @@ (Var x *<=* upper) @@ (lower *<=* upper))
    |> Or_error.map ~f:collect_bounds
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
    let bounds = Solver.init c in
    (* let bounds' = bounds |> Or_error.bind ~f:Solver.iter in *)
    let prettify =
      Or_error.map
        ~f:
          (Map.map ~f:(fun (lower, upper) ->
               (Type.Normal.pretty lower, Type.Normal.pretty upper)))
    in
    print_s
      [%message (prettify bounds : (Sexp.t * Sexp.t) Type_var.Map.t Or_error.t)]
    (* print_s
      [%message
        (prettify bounds' : (Sexp.t * Sexp.t) Type_var.Map.t Or_error.t)]; *)
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
     (Ok
      (($4 (bot ({ (foo $7) | ? }))) ($5 (bot top))
       ($7 (bot ({ (bar $6) | ? }))))))
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
      (($10 (bot ({ (foo _) | ? })))
       ($11 (bot (& (((records ((foo Top)))) $10) ({ (foo int) | ? })))))))
    |}];
  test ("r => {b: r.b.not() | r}" |> Syntax.parse_exn);
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
          (Flow (sub (Var $12))
           (sup (Typ (Record ((m ((b Absent))) (rest Top))))))
          (Flow (sub (Var $13)) (sup (Apply ((records ((b Top)))) (Var $12))))
          (Flow (sub (Var $13))
           (sup (Typ (Record ((m ((b (Present (Var $15))))) (rest Top))))))))))))
    ("prettify bounds"
     (Ok
      (($12 (bot ({ (b !) | ? })))
       ($13 (bot (& (((records ((b Top)))) $12) ({ (b $15) | ? }))))
       ($14 (() top)) ($16 (bot ($14 -> $15))) ($17 (bot ({ (not $16) | ? }))))))
    |}]
