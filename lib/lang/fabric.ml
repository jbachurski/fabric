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

  let rec pretty =
    let open Sexp in
    function
    | Any -> Atom "*"
    | Int -> Atom "int"
    | Float -> Atom "float"
    | Tuple ts -> List (List.map ~f:pretty ts)
    | Function (s, t) -> List [ pretty s; Atom "->"; pretty t ]
    | Array t -> List [ Atom "[]"; pretty t ]
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
    | Closure of int * (string * Type.t) list * Type.t
  [@@deriving sexp]

  let pretty_var = function
    | x, Type.Any -> Sexp.Atom x
    | x, t -> Sexp.(List [ Atom x; Atom ":"; Type.pretty t ])

  let rec pretty_pattern = function
    | Atom (x, t) -> pretty_var (x, t)
    | List ps -> Sexp.List (List.map ~f:pretty_pattern ps)

  let rec pretty =
    let open Sexp in
    function
    | Var (x, t) -> pretty_var (x, t)
    | Lit n -> Atom (string_of_int n)
    | Let (x, e, e') ->
        List
          [
            Atom "let";
            pretty_pattern x;
            Atom "=";
            pretty e;
            Atom "in";
            pretty e';
          ]
    | Fun (x, e) -> List [ pretty_pattern x; Atom "=>"; pretty e ]
    | Tuple es -> List (Atom "," :: List.map ~f:pretty es)
    | Array (i, e, e') ->
        List
          [
            Atom "["; Atom i; Atom ":"; pretty e; Atom "]"; Atom "=>"; pretty e';
          ]
    | Idx (e, e') -> List [ Atom "[]"; pretty e; pretty e' ]
    | Shape e -> List [ Atom "#"; pretty e ]
    | Op (e, "", e') -> List [ pretty e; pretty e' ]
    | Op (e, o, e') -> List [ Atom o; pretty e; pretty e' ]
    | Closure (k, xs, t) ->
        List
          [
            Atom "closure";
            Atom (string_of_int k);
            [%sexp (xs : (string * Type.t) list)];
            Type.pretty t;
          ]

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
    | Closure (k, xs, t) -> f (Closure (k, xs, t))

  let rec var_reduce z ( !. ) ( <| ) ( <|> ) (e : t) =
    let ( !! ) = var_reduce z ( !. ) ( <| ) ( <|> ) in
    match e with
    | Var (x, t) -> !.(x, t)
    | Lit _ -> z
    | Let (x, e, e') -> !!e <|> (!!e' <| x)
    | Fun (x, e) -> !!e <| x
    | Tuple es -> List.map ~f:( !! ) es |> List.fold_left ~init:z ~f:( <|> )
    | Array (i, e, e') -> !!e <|> !!e' <| Atom (i, Int)
    | Idx (e, e') -> !!e <|> !!e'
    | Shape e -> !!e
    | Op (e, _o, e') -> !!e <|> !!e'
    | Closure (_k, xs, _t) ->
        List.map ~f:( !. ) xs |> List.fold_left ~init:z ~f:( <|> )

  let rec type_pattern : pattern -> Type.t = function
    | Atom (_, t) -> t
    | List ps -> Tuple (List.map ~f:type_pattern ps)

  let type_expr _ = Type.Any
end

module Prog = struct
  type t = {
    functions : ((string * Type.t) list * Expr.pattern * Expr.t) list;
    main : Expr.t;
  }
  [@@deriving sexp]

  let pretty { functions; main } =
    let open Sexp in
    List
      [
        List
          [
            Atom "functions";
            List
              (List.map
                 ~f:(fun (xs, p, e) ->
                   List
                     [
                       Atom "capture";
                       List (List.map ~f:Expr.pretty_var xs);
                       Atom "params";
                       Expr.pretty_pattern p;
                       Atom "body";
                       Expr.pretty e;
                     ])
                 functions);
          ];
        List [ Atom "main"; Expr.pretty main ];
      ]
end
