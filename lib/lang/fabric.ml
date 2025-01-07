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
    | Closure of int * (string * Type.t) list
  [@@deriving sexp]

  let rec transform f = function
    | Var (x, t) -> f (Var (x, t))
    | Lit n -> f (Lit n)
    | Let (x, e, e') -> f (Let (x, transform f e, transform f e'))
    | Fun (x, e) -> f (Fun (x, transform f e))
    | Tuple es -> f (Tuple (List.map ~f:(transform f) es))
    | Array (i, e, e') -> f (Array (i, transform f e, transform f e'))
    | Idx (e, e') -> f (Idx (transform f e, transform f e'))
    | Shape e -> f (Shape (transform f e))
    | Op (e, o, e') -> f (Op (transform f e, o, transform f e'))
    | Closure (k, xs) -> f (Closure (k, xs))

  let rec var_reduce z ( !. ) ( <| ) ( <|> ) =
    let ( !! ) = var_reduce z ( !. ) ( <| ) ( <|> ) in
    function
    | Var (x, t) -> !.(x, t)
    | Lit _ -> z
    | Let (x, e, e') -> !!e <|> !!e' <| x
    | Fun (x, e) -> !!e <| x
    | Tuple es -> List.map ~f:( !! ) es |> List.fold_left ~init:z ~f:( <|> )
    | Array (i, e, e') -> !!e <|> !!e' <| Atom (i, Int)
    | Idx (e, e') -> !!e <|> !!e'
    | Shape e -> !!e
    | Op (e, _o, e') -> !!e <|> !!e'
    | Closure (_k, xs) ->
        List.map ~f:( !. ) xs |> List.fold_left ~init:z ~f:( <|> )
end

module Prog = struct
  type t = {
    functions : ((string * Type.t) list * Expr.pattern * Expr.t) list;
    body : Expr.t;
  }
  [@@deriving sexp]
end
