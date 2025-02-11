open Core
open Sym

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

    let map ~f = function
      | Top -> Top
      | Bot -> Bot
      | Absent -> Absent
      | Present a -> Present (f a)
  end

  module Fields : sig
    type rest = [ `Absent | `Bot | `Top ]
    type 'a t = { m : 'a Field.t Label.Map.t; rest : rest }

    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val t_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a t
    val sexp_of_t : ('a -> Sexp.t) -> 'a t -> Sexp.t
    val pretty : ('a -> Sexp.t) -> 'a t -> Sexp.t list
    val closed : 'a Field.t Label.Map.t -> 'a t
    val open_ : 'a Field.t Label.Map.t -> 'a t
    val map : f:('a -> 'b) -> 'a t -> 'b t
    val lift : ('a Field.t -> 'b Field.t -> 'c Field.t) -> 'a t -> 'b t -> 'c t
    val update : 'a t -> Label.t -> 'a Field.t -> 'a t
    val field : 'a t -> Label.t -> 'a Field.t
    val subs : 'a t -> 'b t -> ('a Field.t * 'b Field.t) Label.Map.t
  end = struct
    type rest = [ `Absent | `Bot | `Top ] [@@deriving sexp, equal, compare]

    and 'a t = { m : 'a Field.t Label.Map.t; rest : [ `Absent | `Bot | `Top ] }
    [@@deriving sexp, equal, compare]

    let un = function `Absent -> Field.Absent | `Bot -> Bot | `Top -> Top

    let nu = function
      | Field.Absent -> `Absent
      | Bot -> `Bot
      | Top -> `Top
      | Present _ ->
          failwith "Record cannot be marked as having all fields present"

    let pretty a { m; rest } =
      let open Sexp in
      (Core.Map.to_alist m
      |> List.map ~f:(fun (l, f) ->
             List
               [
                 Atom (Label.to_string l);
                 (match f with
                 | Present t -> a t
                 | Bot -> Atom "!"
                 | Top -> Atom "?"
                 | Absent -> Atom "_");
               ]))
      @
      match rest with
      | `Bot -> [ Atom "|"; Atom "!" ]
      | `Top -> [ Atom "!"; Atom "?" ]
      | `Absent -> []

    let closed m = { m; rest = `Absent }
    let open_ m = { m; rest = `Top }
    let map ~f { m; rest } = { m = Map.map ~f:(Field.map ~f) m; rest }
    let update { m; rest } key data = { m = Map.set m ~key ~data; rest }

    let field { m; rest } key =
      Map.find m key |> Option.value ~default:(un rest)

    let subs { m; rest } { m = m'; rest = rest' } =
      Map.merge m m' ~f:(fun ~key:_ -> function
        | `Both (t, t') -> Some (t, t')
        | `Left t -> Some (t, un rest')
        | `Right t' -> Some (un rest, t'))

    let lift f first second =
      {
        m = subs first second |> Map.map ~f:(fun (fd, fd') -> f fd fd');
        rest = nu (f (un first.rest) (un second.rest));
      }
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

  let map ~f = function
    | Top -> Top
    | Bot -> Bot
    | Int -> Int
    | Float -> Float
    | Tuple ts -> Tuple (List.map ~f ts)
    | Function (t, t') -> Function (f t, f t')
    | Array t -> Array (f t)
    | Record fs -> Record (Fields.map ~f fs)

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
    | Let of pattern * t * t
    | Fun of pattern * t
    | Tuple of t list
    | Array of string * t * t
    | Idx of t * t
    | Shape of t
    | Cons of (string * t) list
    | Proj of t * string
    | Extend of string * t * t
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
    | Extend (f, e, e') ->
        List
          [
            Atom "{"; Atom f; Atom "="; pretty e; Atom "|"; pretty e'; Atom "}";
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
        | Let (x, e, e') -> Let (x, go0 e, go x e')
        | Fun (x, e) -> Fun (x, go x e)
        | Tuple es -> Tuple (List.map es ~f:go0)
        | Array (i, e, e') -> Array (i, go0 e, go (Atom (i, T Int)) e')
        | Idx (e, e') -> Idx (go0 e, go0 e')
        | Shape e -> Shape (go0 e)
        | Cons fs -> Cons (List.map fs ~f:(fun (l, e) -> (l, go0 e)))
        | Proj (e, l) -> Proj (go0 e, l)
        | Extend (f, e, e') -> Extend (f, go0 e, go0 e')
        | Intrinsic (f, e) -> Intrinsic (f, go0 e)
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
    | Array (i, e, e') -> !!e <|> !!e' <| Atom (i, T Int)
    | Idx (e, e') -> !!e <|> !!e'
    | Shape e -> !!e
    | Cons fs ->
        List.map fs ~f:(fun (_, e) -> !!e) |> List.fold_left ~init:z ~f:( <|> )
    | Proj (e, _) -> !!e
    | Extend (_f, e, e') -> !!e <|> !!e'
    | Intrinsic (_, e) -> !!e
    | Op (e, _o, e') -> !!e <|> !!e'
    | Closure (_k, xs, _t) ->
        List.map ~f:( !. ) xs |> List.fold_left ~init:z ~f:( <|> )

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

  let rec type_expr = function
    | Var (_, t) -> t
    | Lit _ -> T Int
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
    | Extend (_f, _e, _e') -> T Top
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
