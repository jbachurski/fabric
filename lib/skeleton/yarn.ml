open! Core
open Env

type scope = Global | Local

module Expr = struct
  type t =
    | Trap
    | Lit of int
    | Var of Name.t
    | Let of Name.t * t * t
    | App of t * t
    | Closure of Name.t * Name.t list
    | Tuple of t list
    | Untuple of Name.t list * t * t
  (* | Proj of t * Label.t *)
  (* | Tag of Tag.t * t *)
  (* | Match of t * Tag.t * Name.t * t * t *)
  [@@deriving sexp]

  let check globals =
    let open Result.Let_syntax in
    let rec go locals expr =
      match expr with
      | Trap -> Ok ()
      | Lit _ -> Ok ()
      | Var name ->
          if List.mem locals ~equal:Name.equal name then Ok ()
          else Error ("no local " ^ Name.to_string name)
      | Closure (name, clos) ->
          if
            List.mem globals ~equal:Name.equal name
            && List.for_all ~f:(List.mem locals ~equal:Name.equal) clos
          then Ok ()
          else Error ("no global " ^ Name.to_string name)
      | Let (name, bound, body) ->
          let%bind () = go locals bound in
          go (name :: locals) body
      | App (f, e) ->
          let%bind () = go locals f in
          go locals e
      | Tuple es ->
          Result.all (List.map ~f:(go locals) es) |> Result.map ~f:ignore
      | Untuple (xs, e, e') ->
          let%bind () = go locals e in
          go (xs @ locals) e'
      (*
      | Proj (e, _) -> go locals e
      | Tag (_, e) -> go locals e
      | Match (e, _, x, e', e'') ->
          let%bind () = go locals e in
          let%bind () = go (x :: locals) e' in
          let%bind () = go (x :: locals) e'' in
          Ok ()
           *)
    in
    go
end

module Prog = struct
  module Closure = struct
    type t = {
      name : Name.t;
      knot : Name.t;
      closed : Name.t list;
      arg : Name.t;
      body : Expr.t;
    }
    [@@deriving sexp]
  end

  type t = { defs : Closure.t list; externs : Name.t list; main : Expr.t }
  [@@deriving sexp]

  let check { defs; externs = _; main } =
    let open Result.Let_syntax in
    let rec go globals = function
      | Closure.{ name; knot; closed; arg; body } :: rest ->
          let%bind () = Expr.check globals (arg :: knot :: closed) body in
          go (name :: globals) rest
      | [] -> Ok globals
    in
    let%bind globals = go [] defs in
    Expr.check globals [] main
end
