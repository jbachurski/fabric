open Core

module Type = struct
  type t =
    | Any
    | Int
    | Float
    | Tuple of t list
    | Function of t * t
    | Array of t
  [@@deriving sexp]
end

module Expr = struct
  type pattern = Atom of string * Type.t | List of pattern list
  [@@deriving sexp]

  type t =
    | Var of string * Type.t
    | Lit of int
    | Let of pattern * t * t
    | Fun of pattern * t
    | Tuple of t list
    | Array of string * t * t
    | Idx of t * t
    | Shape of t
    | Op of t * string * t
  [@@deriving sexp]
end

module Prog = struct
  type t = {
    functions : (string list * Expr.pattern * Expr.t) list;
    body : Expr.t;
  }
  [@@deriving sexp]
end
