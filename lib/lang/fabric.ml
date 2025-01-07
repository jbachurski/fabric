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

  let rec traverse env ( <| ) f =
    let go0 e = traverse env ( <| ) f e in
    let go (x : pattern) e = traverse (env <| x) ( <| ) f e in
    fun e ->
      f env
        (match e with
        | Var (x, t) -> Var (x, t)
        | Lit n -> Lit n
        | Let (x, e, e') -> Let (x, go0 e, go x e')
        | Fun (x, e) -> Fun (x, go x e)
        | Tuple es -> Tuple (List.map ~f:go0 es)
        | Array (i, e, e') -> Array (i, go0 e, go (Atom (i, Int)) e')
        | Idx (e, e') -> Idx (go0 e, go0 e')
        | Shape e -> Shape (go0 e)
        | Op (e, o, e') -> Op (go0 e, o, go0 e')
        | Closure (k, xs, t) -> Closure (k, xs, t))

  let transform f = traverse () (fun x _ -> x) (fun () e -> f e)

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
