open! Core
open Env

module Value = struct
  type 'expr t =
    | Number of 'expr number_repr
    | Tuple of 'expr tuple_repr
    (* | Record of 'expr record_repr *)
    (* | Variant of 'expr variant_repr *)
    | Fun of 'expr fun_repr

  and _ number_repr = int
  and 'expr tuple_repr = 'expr t list
  and 'expr record_repr = (label * 'expr t) list
  and 'expr variant_repr = tag * 'expr t
  and 'expr fun_repr = name * name * 'expr

  let unwrap_number = function Number v -> Some v | _ -> None
  let unwrap_tuple = function Tuple v -> Some v | _ -> None

  (* let unwrap_record = function Record v -> Some v | _ -> None *)
  (* let unwrap_variant = function Variant v -> Some v | _ -> None *)
  let unwrap_fun = function Fun v -> Some v | _ -> None
end

module Type = struct
  type t = Int | Tuple of t list | Fun of t * t [@@deriving sexp]
end

module Expr = struct
  type t =
    | Trap
    | Lit of int
    | Var of Name.t
    | Abs of Name.t * Name.t * Type.t * t
    | App of t * t
    | Tuple of t list
    | Untuple of Name.t list * t * t
  (* | Proj of t * Label.t *)
  (* | Tag of Tag.t * t *)
  (* | Match of t * Tag.t * Name.t * t * t *)
  [@@deriving sexp]
end

module Interpreter : sig
  val run : Expr.t -> Expr.t Value.t
end = struct
  let rec go ~env (expr : Expr.t) : Expr.t Value.t =
    match expr with
    | Lit v -> Number v
    | Var x -> Env.lookup env x |> Option.value_exn ~message:"var not in env"
    | Abs (r, x, _, e) -> Fun (r, x, e)
    | App (f, e) ->
        let f = go ~env f in
        let e = go ~env e in
        let r, x, b =
          Value.unwrap_fun f
          |> Option.value_exn ~message:"can only apply functions"
        in
        Env.bindings env [ (r, f); (x, e) ] (go b)
    | Tuple es -> Tuple (List.map ~f:(go ~env) es)
    | Untuple (xs, e, e') ->
        let e = go ~env e in
        let vs =
          Value.unwrap_tuple e
          |> Option.value_exn ~message:"can only destruct tuples"
        in
        Env.bindings env (List.zip_exn xs vs) (go e')
    (*
    | Proj (e, l) ->
        let e = go ~env e in
        let r =
          Value.unwrap_record e
          |> Option.value_exn ~message:"only records have fields"
        in
        List.Assoc.find r ~equal:Label.equal l
        |> Option.value_exn ~message:"no record field under label"
    | Tag (t, e) -> Value.Variant (t, go ~env e)
    | Match (e, t, x, e', e'') ->
        let e = go ~env e in
        let t', e =
          Value.unwrap_variant e
          |> Option.value_exn ~message:"only records have fields"
        in
        if Tag.equal t t' then Env.bindings env [ (x, e) ] (go e')
        else go ~env e''
    *)
    | Trap -> failwith "trap"

  let run expr = go ~env:Env.init expr
end
