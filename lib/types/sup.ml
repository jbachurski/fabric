open Core
module Type_var = Lang.Sym.Type_var

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

    val pretty : arrow -> Sexp.t
    val id : t
    val is_id : t -> bool
    val compose : t -> t -> t
    val apply : t -> 'a typ -> 'a typ
    val left_adjoint : t -> t
    val right_adjoint : t -> t
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

    val pretty : arrow -> Sexp.t
    val id : t
    val is_id : t -> bool
    val compose : t -> t -> t
    val apply : t -> 'a typ -> 'a typ
  end
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

    val negate : t -> t

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
  val combine_clause : clause -> clause -> clause
  val negate : t -> t
  val apply : arrow -> t -> t
  val apply_clause : arrow -> clause -> clause
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
      | false, false -> List [ M.Arrow.pretty app; x ]
      | true, false -> List [ Atom "~"; M.Arrow.pretty app; x ]

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

  let apply_clause a { vars; pos_typ; neg_typ } =
    {
      vars = Var.Set.map vars ~f:(fun x -> Var.apply a x);
      pos_typ = M.Arrow.apply a pos_typ;
      neg_typ = M.Arrow.apply a neg_typ;
    }

  let typ pos_typ : t = [ { top_clause with pos_typ } ]
  let not_typ neg_typ : t = [ { top_clause with neg_typ } ]
  let var x = [ { top_clause with vars = Var.Set.singleton (Var.var x) } ]

  let rec simplify cs =
    let cs, pos_typs =
      List.partition_map cs ~f:(fun c ->
          if Set.is_empty c.vars && must_be_bot c.neg_typ then Second c.pos_typ
          else First c)
    in
    let cs, neg_typs =
      List.partition_map cs ~f:(fun c ->
          if Set.is_empty c.vars && must_be_top c.pos_typ then Second c.neg_typ
          else First c)
    in

    let pos_typ =
      List.reduce pos_typs ~f:(M.join lattice) |> Option.value ~default:M.bot
    in
    let neg_typ =
      List.reduce neg_typs ~f:(M.meet lattice) |> Option.value ~default:M.top
    in
    let cs = cs @ typ pos_typ @ not_typ neg_typ in

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
    (* Remove clauses with both a variable and its negation *)
    |> List.filter ~f:(fun c ->
           Set.exists c.vars ~f:(fun x -> Set.mem c.vars (Var.negate x)) |> not)

  and apply a t = List.map t ~f:(apply_clause a) |> simplify
  and join t t' = t @ t' |> simplify

  and meet_clause t t' =
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

  let combine_clause = meet_clause

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

  let join = T.meet
  and meet = T.join
  and lattice = { join; meet }

  let interpret ~top ~bot ~typ ~var ~join ~meet ~negate ~apply t =
    T.interpret ~top:bot ~bot:top ~typ ~var ~join:meet ~meet:join ~negate ~apply
      t
end

module Type (M : TypeSystem) = struct
  open M
  open Lang.Sym

  module DNF = DNF (struct
    include M

    let join_token = "|"
    and meet_token = "&"
  end)

  module CNF = CNF (struct
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

    let rec interpret ~var ~typ ~join ~meet ~negate ~apply t =
      let go = interpret ~var ~typ ~join ~meet ~negate ~apply in
      match t with
      | Var x -> var x
      | Typ t -> typ (map ~f:go t)
      | Apply (a, t) -> apply a (go t)
      | Combine (Top, t, t') -> join (go t) (go t')
      | Combine (Bot, t, t') -> meet (go t) (go t')
      | Complement t -> negate (go t)
  end

  let var x = Alg.Var x
  let typ t = Alg.Typ t
  let apply a t = Alg.Apply (a, t)

  let dnf =
    let open DNF in
    Alg.interpret ~var ~typ ~join ~meet ~negate ~apply

  let cnf =
    let open CNF in
    Alg.interpret ~var ~typ ~join ~meet ~negate ~apply

  let dnf_to_cnf =
    let open CNF in
    DNF.interpret ~top ~bot ~typ ~var ~join ~meet ~negate ~apply

  let cnf_to_dnf =
    let open DNF in
    CNF.interpret ~top ~bot ~typ ~var ~join ~meet ~negate ~apply

  let negate_dnf_clause_into_cnf (c : DNF.clause) : CNF.clause =
    {
      vars =
        CNF.Var.Set.map
          ~f:(fun x ->
            let DNF.Var.{ var; neg; app } = DNF.Var.negate x in
            { var; neg; app })
          c.vars;
      pos_typ = M.map ~f:dnf_to_cnf c.neg_typ;
      neg_typ = M.map ~f:dnf_to_cnf c.pos_typ;
    }

  let negate_cnf_clause_into_dnf (c : CNF.clause) : DNF.clause =
    {
      vars =
        DNF.Var.Set.map
          ~f:(fun x ->
            let CNF.Var.{ var; neg; app } = CNF.Var.negate x in
            { var; neg; app })
          c.vars;
      pos_typ = M.map ~f:cnf_to_dnf c.neg_typ;
      neg_typ = M.map ~f:cnf_to_dnf c.pos_typ;
    }
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
    | Lower of DNF.clause * Type_var.t
    | Upper of Type_var.t * CNF.clause
  [@@deriving sexp]

  type dir = Alg.dir = Bot | Top

  let concat_map_or_error xs ~f =
    List.map xs ~f |> Or_error.all |> Or_error.map ~f:List.concat

  let inv = function Top -> Bot | Bot -> Top

  let rec atomize_decomposition =
    Or_error.bind ~f:(concat_map_or_error ~f:(fun (l, u) -> l *<=* u))

  and ( @@ ) a b = concat_map_or_error ~f:Fn.id [ a; b ]

  and ( *<=* ) (lower : DNF.t) (upper : CNF.t) =
    List.cartesian_product lower upper
    |> concat_map_or_error ~f:(fun (l, u) -> l **<=** u)

  and ( **<=** ) (lower : DNF.clause) (upper : CNF.clause) =
    let DNF.{ vars; pos_typ; neg_typ } =
      DNF.combine_clause lower (negate_cnf_clause_into_dnf upper)
    in
    (* vars /\ pos_typ /\ ~neg_typ <= bot *)
    match Set.is_empty vars with
    | true ->
        M.decompose DNF.sexp_of_t (pos_typ, neg_typ)
        |> Or_error.map
             ~f:(List.map ~f:(fun (lower, upper) -> (lower, dnf_to_cnf upper)))
        |> atomize_decomposition
    | false ->
        Set.to_list vars
        |> concat_map_or_error ~f:(fun x ->
               Ok
                 [
                   DNF.{ vars = Set.remove vars x; pos_typ; neg_typ }
                   **<= DNF.Var.negate x;
                 ])

  and ( **<= ) (bound : DNF.clause) (var : DNF.Var.t) =
    match var with
    | { var; neg = true; app } ->
        { var; neg = false; app } <=** negate_dnf_clause_into_cnf bound
    | { var; neg = false; app } ->
        Lower (DNF.apply_clause (M.Arrow.left_adjoint app) bound, var)

  and ( <=** ) (var : DNF.Var.t) (bound : CNF.clause) =
    match var with
    | { var; neg = true; app } ->
        negate_cnf_clause_into_dnf bound **<= { var; neg = false; app }
    | { var; neg = false; app } ->
        Upper (var, CNF.apply_clause (M.Arrow.right_adjoint app) bound)

  let rec atomize_constraint : Alg.t Constraint.t -> bound list Or_error.t =
    function
    | With (_, c) -> atomize_constraint c
    | Flow { sub; sup } -> dnf sub *<=* cnf sup
    | All cs -> concat_map_or_error cs ~f:atomize_constraint

  let collect_bounds atomic_bounds =
    List.fold atomic_bounds ~init:Type_var.Map.empty ~f:(fun acc -> function
      | Lower (l, u) ->
          Map.update acc u ~f:(fun v ->
              let low, high = Option.value v ~default:(DNF.bot, CNF.top) in
              (DNF.join [ l ] low, high))
      | Upper (l, u) ->
          Map.update acc l ~f:(fun v ->
              let low, high = Option.value v ~default:(DNF.bot, CNF.top) in
              (low, CNF.meet high [ u ])))

  let init c = atomize_constraint c |> Or_error.map ~f:collect_bounds

  let rec iterate bs =
    let iteration bs =
      Map.to_alist bs
      |> concat_map_or_error ~f:(fun (x, (lower, upper)) ->
             (lower *<=* CNF.var x)
             @@ (DNF.var x *<=* upper)
             @@ (lower *<=* upper))
      |> Or_error.map ~f:collect_bounds
    in
    let bs' = iteration bs in
    Or_error.bind bs' ~f:(fun bs' ->
        if [%equal: (DNF.t * CNF.t) Type_var.Map.t] bs bs' then Ok bs
        else iterate bs')

  let run c = Or_error.bind (init c) ~f:iterate
end
