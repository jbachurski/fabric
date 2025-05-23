open Core
open Sym
open Alg
open Row

module Repr = struct
  type atom = Int32 | Float64 | Box
  type t = Unknown | Atoms of atom list

  let nothing = Atoms []

  let ( ++ ) t t' =
    match (t, t') with
    | Unknown, _ | _, Unknown -> Unknown
    | Atoms t, Atoms t' -> Atoms (t @ t')

  let cat = List.fold_right ~init:nothing ~f:( ++ )

  let pretty_atom =
    let open Sexp in
    function Int32 -> Atom "i32" | Float64 -> Atom "f64" | Box -> Atom "box"

  let pretty =
    let open Sexp in
    function Unknown -> Atom "?" | Atoms t -> List (List.map ~f:pretty_atom t)
end

module Type = struct
  type dir = Top | Bot [@@deriving equal, compare, sexp]

  let inv = function Top -> Bot | Bot -> Top

  module Field = struct
    type 'a t = Top | Bot | Absent | Present of 'a
    [@@deriving sexp, equal, compare]

    let components = function Top | Absent | Bot -> [] | Present t -> [ t ]

    let polar_map Polar.{ pos; neg = _ } = function
      | Top -> Top
      | Bot -> Bot
      | Absent -> Absent
      | Present a -> Present (pos a)

    let map ~f = polar_map { pos = f; neg = f }

    let pretty a : _ -> Sexp.t = function
      | Present t -> a t
      | Absent -> Atom "_"
      | Bot -> Atom "!"
      | Top -> Atom "?"

    let combine latt first second =
      match (first, second) with
      | Top, x | x, Top -> (x, Top)
      | Bot, x | x, Bot -> (Bot, x)
      | Absent, Absent -> (Absent, Absent)
      | Present x, Present y ->
          (Present (latt.meet x y), Present (latt.join x y))
      | _ -> (Bot, Top)

    let meet latt x y = fst (combine latt x y)
    and join latt x y = snd (combine latt x y)
  end

  module Fields = struct
    include Row (Label) (Field)

    let closed m = { m; rest = Absent }
    let open_ m = { m; rest = Top }
  end

  type 't typ =
    | Top
    | Bot
    | Int
    | Float
    | Tuple of 't list
    | Function of 't * 't
    | Array of 't
    | Record of 't Fields.t
  [@@deriving sexp, equal, compare]

  type t = T of t typ [@@deriving sexp, equal, compare]

  let polar_map ~f:Polar.{ pos; neg } = function
    | Top -> Top
    | Bot -> Bot
    | Int -> Int
    | Float -> Float
    | Tuple ts -> Tuple (List.map ~f:pos ts)
    | Function (t, t') -> Function (neg t, pos t')
    | Array t -> Array (pos t)
    | Record fs -> Record (Fields.map ~f:pos fs)

  let map ~f = polar_map ~f:{ pos = f; neg = f }
  let repr (_ : t) : Repr.t = Atoms [ Box ]
  let unit = Tuple []

  let pretty' pretty_t t =
    let open Sexp in
    match t with
    | Top -> Atom "top"
    | Bot -> Atom "bot"
    | Int -> Atom "int"
    | Float -> Atom "float"
    | Tuple ts -> List (List.map ~f:pretty_t ts)
    | Function (s, t) -> List [ pretty_t s; Atom "->"; pretty_t t ]
    | Array t -> List [ Atom "[]"; pretty_t t ]
    | Record fs -> List ([ Atom "{" ] @ Fields.pretty pretty_t fs @ [ Atom "}" ])

  let rec pretty (T t) = pretty' pretty t

  let unwrap_function = function
    | T (Function (t, t')) -> (t, t')
    | t -> raise_s [%message "not a function" (t : t)]

  let unwrap_array = function
    | T (Array t) -> t
    | t -> raise_s [%message "not an array" (t : t)]

  let unwrap_record_field t l =
    match t with
    | T (Record fs) -> (
        match Fields.field fs l with
        | Present t -> t
        | _ ->
            raise_s
              [%message
                "no such field" (l : Label.t) "in record" (fs : t Fields.t)])
    | t -> raise_s [%message "not an array" (t : t)]
end

module Expr = struct
  type pattern = Atom of string * Type.t | List of pattern list
  [@@deriving equal, sexp]

  type t =
    | Var of string * Type.t
    | Lit of int
    | Unify of string * string * t
    | Let of pattern * t * t
    | Fun of pattern * t
    | Tuple of t list
    | Array of string * t * t
    | Idx of t * t
    | Shape of t
    | Cons of (string * t) list
    | Proj of t * string
    | Restrict of t * string
    | Extend of string * t * t
    | Tag of string * t
    | Match of t * (string * t) list
    | Intrinsic of string * t
    | Op of t * string * t
    | Closure of int * (string * Type.t) list * Type.t
  [@@deriving equal, sexp]

  let pretty_var = function
    | x, Type.(T Top) -> Sexp.Atom x
    | x, t -> Sexp.(List [ Atom x; Atom ":"; Type.pretty t ])

  let rec pretty_pattern = function
    | Atom (x, t) -> pretty_var (x, t)
    | List ps -> Sexp.List (List.map ~f:pretty_pattern ps)

  let rec pretty =
    let open Sexp in
    function
    | Var (x, t) -> pretty_var (x, t)
    | Lit n -> Atom (string_of_int n)
    | Unify (x, x', e) ->
        List [ Atom "let"; Atom x; Atom "~"; Atom x'; Atom "in"; pretty e ]
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
    | Idx (e, e') -> List [ pretty e; Atom "["; pretty e'; Atom "]" ]
    | Shape e -> List [ Atom "#"; pretty e ]
    | Cons fs ->
        List
          ([ Atom "{" ]
          @ List.map fs ~f:(fun (l, t) -> List [ Atom l; pretty t ])
          @ [ Atom "}" ])
    | Proj (t, l) -> List [ pretty t; Atom "."; Atom l ]
    | Restrict (t, l) -> List [ pretty t; Atom "\\"; Atom l ]
    | Extend (f, e, e') ->
        List
          [
            Atom "{"; Atom f; Atom "="; pretty e; Atom "|"; pretty e'; Atom "}";
          ]
    | Tag (t, e) -> List [ Atom t; pretty e ]
    | Match (e, cs) ->
        List
          [
            Atom "match";
            pretty e;
            List
              (List.map
                 ~f:(fun (t, e) -> List [ Atom t; Atom "=>"; pretty e ])
                 cs);
          ]
    | Intrinsic (f, e) -> List [ Atom ("%" ^ f); pretty e ]
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
        | Unify (x, x', e) -> Unify (x, x', go0 e)
        | Let (x, e, e') -> Let (x, go0 e, go x e')
        | Fun (x, e) -> Fun (x, go x e)
        | Tuple es -> Tuple (List.map es ~f:go0)
        | Array (i, e, e') -> Array (i, go0 e, go (Atom (i, T Int)) e')
        | Idx (e, e') -> Idx (go0 e, go0 e')
        | Shape e -> Shape (go0 e)
        | Cons fs -> Cons (List.map fs ~f:(fun (l, e) -> (l, go0 e)))
        | Proj (e, l) -> Proj (go0 e, l)
        | Restrict (e, l) -> Restrict (go0 e, l)
        | Extend (f, e, e') -> Extend (f, go0 e, go0 e')
        | Tag (t, e) -> Tag (t, go0 e)
        | Match (e, cs) ->
            Match (go0 e, List.map ~f:(fun (t, e) -> (t, go0 e)) cs)
        | Intrinsic (f, e) -> Intrinsic (f, go0 e)
        | Op (e, o, e') -> Op (go0 e, o, go0 e')
        | Closure (k, xs, t) -> Closure (k, xs, t))

  let transform f = traverse () (fun x _ -> x) (fun () e -> f e)

  let rec var_reduce z ( !. ) ( <| ) ( <|> ) (e : t) =
    let ( !! ) = var_reduce z ( !. ) ( <| ) ( <|> ) in
    let all = List.fold_left ~init:z ~f:( <|> ) in
    match e with
    | Var (x, t) -> !.(x, t)
    | Lit _ -> z
    | Unify (_, _, e) -> !!e
    | Let (x, e, e') -> !!e <|> (!!e' <| x)
    | Fun (x, e) -> !!e <| x
    | Tuple es -> List.map ~f:( !! ) es |> all
    | Array (i, e, e') -> !!e <|> !!e' <| Atom (i, T Int)
    | Idx (e, e') -> !!e <|> !!e'
    | Shape e -> !!e
    | Cons fs -> List.map fs ~f:(fun (_, e) -> !!e) |> all
    | Proj (e, _) -> !!e
    | Restrict (e, _) -> !!e
    | Extend (_f, e, e') -> !!e <|> !!e'
    | Tag (_, e) -> !!e
    | Match (e, cs) -> !!e <|> (List.map cs ~f:(fun (_, e) -> !!e) |> all)
    | Intrinsic (_, e) -> !!e
    | Op (e, _o, e') -> !!e <|> !!e'
    | Closure (_k, xs, _t) -> List.map ~f:( !. ) xs |> all

  let rec type_onto_pattern (t : Type.t) (p : pattern) : pattern =
    match (t, p) with
    | t', Atom (x, _t) -> Atom (x, t')
    | T (Tuple ts), List ps -> List (List.map2_exn ~f:type_onto_pattern ts ps)
    | _ ->
        raise_s
          [%message "cannot type pattern" (t : Type.t) "with" (p : pattern)]

  let rec type_pattern : pattern -> Type.t = function
    | Atom (_, t) -> t
    | List ps -> T (Tuple (List.map ~f:type_pattern ps))

  (* This does not really do what I would want it to, but it is some approximation of the type *)
  let rec type_expr = function
    | Var (_, t) -> t
    | Lit _ -> T Int
    | Unify (_, _, e) -> type_expr e
    | Let (_, _, e') -> type_expr e'
    | Fun (x, e) -> T (Function (type_pattern x, type_expr e))
    | Tuple es -> T (Tuple (List.map ~f:type_expr es))
    | Array (_, _, e) -> T (Array (type_expr e))
    | Idx (e, _) -> Type.unwrap_array (type_expr e)
    | Shape _ -> T Int
    | Cons fs ->
        T
          (Record
             (List.map fs ~f:(fun (l, e) ->
                  (Label.of_string l, Type.Field.Present (type_expr e)))
             |> Label.Map.of_alist_exn |> Type.Fields.closed))
    | Proj (e, l) -> Type.unwrap_record_field (type_expr e) (Label.of_string l)
    | Restrict (_e, _l) -> T Top
    | Extend (_f, _e, _e') -> T Top
    | Tag (_, _) -> T Top
    | Match (_, _) -> T Top
    | Intrinsic ("print", _) -> T Type.unit
    | Intrinsic ("print_i32", _) -> T Type.unit
    | Intrinsic _ -> T Top
    | Op (e, _, _) -> type_expr e
    | Closure (_, _, t) -> t
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
