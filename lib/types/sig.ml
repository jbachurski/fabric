open Core
open Sup

module Make (M : TypeSystem) = struct
  module DNF = DNF (M)
  module CNF = CNF (M)
  module Type = Type (M)

  type t = { bounds : (DNF.t * DNF.t) Type_var.Map.t; body : DNF.t }
  [@@deriving sexp]

  let ground Polar.{ pos; neg } = pos @ neg

  let filter_singletons xs =
    List.filter xs ~f:(fun v -> List.count xs ~f:(Type_var.equal v) = 1)

  let ( @~@ ) = Polar.lift ~f:( @ )
  let polar_concat = List.fold_right ~f:( @~@ ) ~init:{ pos = []; neg = [] }

  let rec dnf_free_vars (t : DNF.t) : Type_var.t list Polar.t =
    let typ_free_vars typ =
      Polar.map
        ~f:(fun t -> List.map ~f:dnf_free_vars t |> polar_concat)
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
        pvars @~@ typ_free_vars pos_typ @~@ Polar.flip (typ_free_vars neg_typ))
    |> polar_concat

  let cnf_free_vars t = dnf_free_vars (Type.cnf_to_dnf t)

  let pretty_bound (var, (lower, upper)) =
    let v = Type_var.sexp_of_t var in
    let l = DNF.pretty lower in
    let u = DNF.pretty upper in
    match (DNF.must_bot lower, DNF.must_top upper) with
    | true, true -> v
    | false, true -> Sexp.List [ l; Atom "<="; v ]
    | true, false -> Sexp.List [ v; Atom "<="; u ]
    | false, false -> Sexp.List [ l; Atom "<="; v; Atom "<="; u ]

  exception Recursive of bool * Type_var.t
  exception Occurs

  module PolarVar = struct
    module T = struct
      type t = bool * Type_var.t [@@deriving sexp, equal, hash, compare]
    end

    include T
    module Hash_set = Hash_set.Make (T)
  end

  type dnf = DNF.t
  type cnf = CNF.t

  let sexp_of_dnf = DNF.pretty
  let sexp_of_cnf = CNF.pretty

  let unwrap_dnf_var_clause (c : DNF.clause) =
    if Set.length c.vars = 1 then
      let v = Set.min_elt_exn c.vars in
      let c' = DNF.var_clause v.var in
      if DNF.equal_clause c c' then Some v.var else None
    else None

  let unwrap_cnf_var_clause (c : CNF.clause) =
    if Set.length c.vars = 1 then
      let v = Set.min_elt_exn c.vars in
      let c' = CNF.var_clause v.var in
      if CNF.equal_clause c c' then Some v.var else None
    else None

  let remove_dnf_var_clause v (t : DNF.t) =
    List.filter t ~f:(fun c ->
        match unwrap_dnf_var_clause c with
        | Some v' -> Type_var.(v <> v')
        | None -> true)

  let remove_cnf_var_clause v (t : CNF.t) =
    List.filter t ~f:(fun c ->
        match unwrap_cnf_var_clause c with
        | Some v' -> Type_var.(v <> v')
        | None -> true)

  let t' bounds body =
    let bounds = Map.map bounds ~f:(fun (l, u) -> (l, Type.cnf_to_dnf u)) in
    (* print_s [%message (bounds : (dnf * dnf) Type_var.Map.t) (body : dnf)]; *)
    let recursive = PolarVar.Hash_set.create () in
    let rec go bounds body =
      let bounds0, body0 = (bounds, body) in
      (* print_s [%message (bounds : (dnf * dnf) Type_var.Map.t) (body : dnf)]; *)
      let occurs ~neg:neg0 v0 =
        let open DNF in
        let seen = PolarVar.Hash_set.create () in
        let rec go ~neg:pol =
          polar_interpret ~top ~bot ~typ
            ~var:(fun ~pol:neg v ->
              if Hash_set.mem seen (neg, v) || Hash_set.mem recursive (neg, v)
              then var v0
              else (
                if Bool.(neg = neg0) && Type_var.(v = v0) then raise Occurs;
                Hash_set.add seen (neg, v);
                let result = go' ~neg v in
                Hash_set.remove seen (neg, v);
                result))
            ~join ~meet ~negate ~apply ~pol
        and go' ~neg v =
          let lower, upper =
            Map.find bounds v |> Option.value ~default:(bot, top)
          in
          match neg with
          | false -> join (var v) (go ~neg lower)
          | true -> meet (var v) (go ~neg upper)
        in
        match ignore (go' ~neg:neg0 v0) with
        | _ -> false
        | exception Occurs -> true
      in
      let rec coalesce ~neg:pol =
        let open DNF in
        polar_interpret ~top ~bot ~typ
          ~var:(fun ~pol:neg v ->
            if Hash_set.mem recursive (neg, v) || occurs ~neg v then (
              Hash_set.add recursive (neg, v);
              var v)
            else
              let lower, upper =
                Map.find bounds v |> Option.value ~default:(bot, top)
              in
              match neg with
              (* Add a polarised occurence of the variable *)
              | false -> join (var v) (coalesce ~neg lower)
              | true -> meet (var v) (coalesce ~neg upper))
          ~join ~meet ~negate ~apply ~pol
      in
      let body = coalesce ~neg:false body in
      let bounds =
        Map.mapi bounds ~f:(fun ~key ~data:(lower, upper) ->
            ( (if Hash_set.mem recursive (false, key) then
                 coalesce ~neg:false lower
               else DNF.typ M.bot),
              if Hash_set.mem recursive (true, key) then
                coalesce ~neg:true upper
              else DNF.typ M.top ))
      in
      let active_vars =
        dnf_free_vars body
        @~@ (Map.map bounds ~f:(fun (lower, upper) ->
                 dnf_free_vars lower @~@ Polar.flip (dnf_free_vars upper))
            |> Map.data |> polar_concat)
        |> Polar.map ~f:Type_var.Set.of_list
      in
      (* 
      print_s [%message (bounds : (dnf * dnf) Type_var.Map.t) (body : dnf)];
      print_s [%message (active_vars : Type_var.Set.t Polar.t)]; 
      *)
      let bounds =
        Map.mapi bounds ~f:(fun ~key ~data:(lower, upper) ->
            ( (if Set.mem active_vars.pos key then lower else DNF.typ M.bot),
              if Set.mem active_vars.neg key then upper else DNF.typ M.top ))
      in
      let rec clear_coalesced ~neg =
        let open DNF in
        interpret ~top ~bot
          ~typ:(fun t ->
            M.polar_map
              ~f:
                Polar.
                  {
                    pos = clear_coalesced ~neg;
                    neg = clear_coalesced ~neg:(not neg);
                  }
              t
            |> DNF.typ)
          ~var:(fun v ->
            if Hash_set.mem recursive (neg, v) then var v
            else
              match neg with
              | false ->
                  if not (Set.mem active_vars.neg v) then typ M.bot else var v
              | true ->
                  if not (Set.mem active_vars.pos v) then typ M.top else var v)
          ~join ~meet ~negate ~apply
      in
      let bounds =
        Map.map bounds ~f:(fun (lower, upper) ->
            (clear_coalesced ~neg:false lower, clear_coalesced ~neg:true upper))
      in
      let body = clear_coalesced ~neg:false body in
      let bounds =
        Map.filter bounds ~f:(fun (lower, upper) ->
            not (DNF.must_bot lower && DNF.must_top upper))
      in
      if
        [%equal: (DNF.t * DNF.t) Type_var.Map.t] bounds bounds0
        && DNF.equal body body0
      then { body; bounds }
      else go bounds body
    in
    go bounds body

  let t bounds body =
    (* print_s [%message (bounds : (dnf * cnf) Type_var.Map.t) (body : dnf)]; *)
    let sandwiches =
      Map.mapi bounds ~f:(fun ~key ~data:(lower, upper) ->
          let lower_vars = List.filter_map ~f:unwrap_dnf_var_clause lower in
          let upper_vars = List.filter_map ~f:unwrap_cnf_var_clause upper in
          Set.inter
            (Type_var.Set.of_list lower_vars)
            (Type_var.Set.of_list upper_vars)
          |> fun s -> Set.add s key)
    in
    let dnf_subst =
      let open DNF in
      interpret ~top ~bot ~typ
        ~var:(fun v ->
          (match Map.find sandwiches v with
          | Some vs -> Set.min_elt_exn vs
          | None -> v)
          |> var)
        ~join ~meet ~negate ~apply
    in
    let cnf_subst =
      let open CNF in
      interpret ~top ~bot ~typ
        ~var:(fun v ->
          (match Map.find sandwiches v with
          | Some vs -> Set.min_elt_exn vs
          | None -> v)
          |> var)
        ~join ~meet ~negate ~apply
    in
    let bounds =
      Map.mapi bounds ~f:(fun ~key ~data:(l, u) ->
          ( dnf_subst l |> remove_dnf_var_clause key,
            cnf_subst u |> remove_cnf_var_clause key ))
    in
    let body = dnf_subst body in
    t' bounds body

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
