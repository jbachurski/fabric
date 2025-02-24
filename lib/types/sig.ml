open Core
open Sup

module Make (M : TypeSystem) = struct
  module DNF = DNF (M)
  module CNF = CNF (M)
  module Type = Type (M)

  type t = { bounds : (DNF.t * CNF.t) Type_var.Map.t; body : DNF.t }

  let ground Polar.{ pos; neg } = pos @ neg

  let filter_singletons xs =
    List.filter xs ~f:(fun v -> List.count xs ~f:(Type_var.equal v) = 1)

  let rec dnf_free_vars (t : DNF.t) : Type_var.t list Polar.t =
    let ( @ ) = Polar.lift ~f:( @ ) in
    let concat = List.fold_right ~f:( @ ) ~init:{ pos = []; neg = [] } in
    let typ_free_vars typ =
      Polar.map
        ~f:(fun t -> List.map ~f:dnf_free_vars t |> concat)
        (M.components typ)
      |> Polar.join
      |> Polar.map ~f:(fun (a, b) -> List.append a b)
    in
    List.map t ~f:(fun { vars; pos_typ; neg_typ } ->
        let pos_vars, neg_vars =
          Set.to_list vars
          |> List.partition_map ~f:(fun { var; neg; app = _ } ->
                 match neg with false -> First var | true -> Second var)
        in
        let pvars = Polar.{ pos = pos_vars; neg = neg_vars } in
        pvars @ typ_free_vars pos_typ @ Polar.flip (typ_free_vars neg_typ))
    |> concat

  let cnf_free_vars t = dnf_free_vars (Type.cnf_to_dnf t)

  let pretty_bound (var, (lower, upper)) =
    let v = Type_var.sexp_of_t var in
    let l = DNF.pretty lower in
    let u = CNF.pretty upper in
    match (DNF.must_bot lower, CNF.must_top upper) with
    | true, true -> v
    | false, true -> Sexp.List [ l; Atom "<="; v ]
    | true, false -> Sexp.List [ v; Atom "<="; u ]
    | false, false -> Sexp.List [ l; Atom "<="; v; Atom "<="; u ]

  let t bounds body = { bounds; body }
  (*
    match dnf_free_vars body |> ground |> filter_singletons with
    | v :: _ ->
        let lower, upper =
          Map.find bounds v |> Option.value ~default:(DNF.bot, CNF.top)
        in
        let upper = Type.cnf_to_dnf upper in
        let body =
          DNF.subst v (DNF.join (DNF.meet (DNF.var v) upper) lower) body
        in
        { bounds; body }
    | _ -> { bounds; body }
    *)

  let pretty { bounds; body } =
    let body = DNF.pretty body in
    match Map.is_empty bounds with
    | true -> body
    | false ->
        Sexp.List
          [
            body;
            Sexp.Atom "where";
            Sexp.List (Map.to_alist bounds |> List.map ~f:pretty_bound);
          ]
end
