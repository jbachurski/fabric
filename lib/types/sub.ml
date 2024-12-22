open! Core
module Name = String
module Label = String
module Tag = String

type name = Name.t
type label = Label.t
type tag = Tag.t

type term =
  | Lit of int
  | Var of name
  | Lam of name * term
  | App of term * term
  | Rcd of (label * term) list
  | Sel of term * label
  | Tag of tag * term
  | Mat of term * (tag * string * term) list
  | Let of name * term * term

module Type = struct
  type t =
    | Variable of var
    | Primitive of string
    | Function of t * t
    | Record of (string * t) list
    | Variant of (string * t) list
  [@@deriving sexp]

  and var = {
    id : int;
    mutable lower : t list; [@hash.ignore]
    mutable upper : t list; [@hash.ignore]
  }
  [@@deriving sexp, hash, compare]

  let varname { id; _ } = "x" ^ string_of_int id
end

let fresh =
  let cnt = ref 0 in
  fun () ->
    cnt := !cnt + 1;
    Type.Variable { id = !cnt; lower = []; upper = [] }

let rec constrain ~sub ~super =
  let open Type in
  match (sub, super) with
  | Primitive a, Primitive b when String.(a = b) -> ()
  | Function (sub_arg, sub_res), Function (super_arg, super_res) ->
      (* argument must be more general *)
      constrain ~sub:super_arg ~super:sub_arg;
      (* result must be more specific *)
      constrain ~sub:sub_res ~super:super_res
  | Record sub_fs, Record super_fs ->
      List.iter super_fs ~f:(fun (l, super_l) ->
          match List.Assoc.find sub_fs ~equal:Label.equal l with
          | Some sub_l -> constrain ~sub:sub_l ~super:super_l
          | None ->
              raise_s
                [%message
                  "mismatching fields in constraint"
                    (sub : Type.t)
                    "<:"
                    (super : Type.t)])
  | Variable sub, super ->
      sub.upper <- super :: sub.upper;
      List.iter sub.lower ~f:(fun lo -> constrain ~sub:lo ~super)
  | sub, Variable super ->
      super.lower <- sub :: super.lower;
      List.iter super.upper ~f:(fun hi -> constrain ~sub ~super:hi)
  | _ ->
      raise_s [%message "bad constraint" (sub : Type.t) "<:" (super : Type.t)]

let rec typ_term ctx : term -> Type.t = function
  | Lit _ -> Type.Primitive "int"
  | Var x -> (
      match List.Assoc.find ctx ~equal:Name.equal x with
      | Some t -> t
      | None -> raise_s [%message "undefined variable" (x : Name.t)])
  | Lam (x, e) ->
      let x_typ = fresh () in
      Function (x_typ, typ_term (List.Assoc.add ctx ~equal:Name.equal x x_typ) e)
  | App (f, e) ->
      let res_typ = fresh () in
      constrain ~sub:(typ_term ctx f)
        ~super:(Function (typ_term ctx e, res_typ));
      res_typ
  | Rcd fs -> Record (List.map ~f:(fun (l, e) -> (l, typ_term ctx e)) fs)
  | Sel (e, l) ->
      let res_typ = fresh () in
      constrain ~sub:(typ_term ctx e) ~super:(Record [ (l, res_typ) ]);
      res_typ
  | Tag (t, e) -> Variant [ (t, typ_term ctx e) ]
  | Mat (t, cases) ->
      let t_typ = typ_term ctx t in
      let res_typ = fresh () in
      List.iter cases ~f:(fun (t, x, e) ->
          let x_typ = fresh () in
          constrain ~sub:(Variant [ (t, x_typ) ]) ~super:t_typ;
          constrain
            ~sub:(typ_term (List.Assoc.add ctx ~equal:Name.equal x x_typ) e)
            ~super:res_typ);
      res_typ
  | Let (x, e, e') ->
      let x_typ = fresh () in
      let ctx' = List.Assoc.add ctx ~equal:Name.equal x x_typ in
      constrain ~sub:(typ_term ctx' e) ~super:x_typ;
      typ_term ctx' e'

let infer = typ_term []

module Pretty = struct
  type t =
    | Lit of string
    | Ext of (string * string) option * t
    | Infix of string * t list
    | Prefix of string * t

  let rec t fmt =
    let open Format in
    function
    | Lit s -> fprintf fmt "%s" s
    | Ext (None, p) -> fprintf fmt "(%a)" t p
    | Ext (Some (pre, post), p) -> fprintf fmt "%s%a%s" pre t p post
    | Infix (sep, ps) ->
        pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "%s" sep) t fmt ps
    | Prefix (pre, p) -> fprintf fmt "%s%a" pre t p

  let str = Format.asprintf "%a" t
end

module UserType = struct
  type t =
    | Top
    | Bot
    | Union of t list
    | Inter of t list
    | Variable of Name.t
    | Primitive of string
    | Function of t * t
    | Record of (Label.t * t) list
    | Variant of (Label.t * t) list
    | Recursive of Name.t * t
  [@@deriving sexp]

  let map_subs ~f = function
    | Top -> Top
    | Bot -> Bot
    | Union ts -> Union (List.map ~f ts)
    | Inter ts -> Inter (List.map ~f ts)
    | Variable x -> Variable x
    | Primitive t -> Primitive t
    | Function (t, t') -> Function (f t, f t')
    | Record fs -> Record (List.map fs ~f:(fun (l, t) -> (l, f t)))
    | Variant fs -> Variant (List.map fs ~f:(fun (l, t) -> (l, f t)))
    | Recursive (x, t) -> Recursive (x, f t)

  let rec match_cases fs ts =
    match (fs, ts) with
    | [], _ -> Some []
    | _, [] -> None
    | f :: fs, t :: ts -> (
        match f t with
        | Some v -> Option.map ~f:(List.cons v) (match_cases fs ts)
        | None -> match_cases fs ts)

  let rec simplify t =
    let t = map_subs ~f:simplify t in
    match t with
    | Union [ t ] -> t
    | Inter [ t ] -> t
    | Recursive (x, Variable x') when Name.(x = x') -> Variable x
    | _ -> t

  let rec pretty =
    let open Pretty in
    function
    | Top -> Lit "'|'"
    | Bot -> Lit "_|_"
    | Union ts -> Infix (" \\/ ", List.map ts ~f:paren_pretty)
    | Inter ts -> Infix (" /\\ ", List.map ts ~f:paren_pretty)
    | Variable x -> Lit x
    | Primitive t -> Lit t
    | Function (t, t') -> fun_pretty (paren_pretty t) (paren_pretty t')
    | Record fs -> Ext (Some ("{", "}"), assocs_pretty fs)
    | Variant fs -> Ext (Some ("[", "]"), assocs_pretty fs)
    | Recursive (x, t) -> Prefix ("fix " ^ x ^ ". ", pretty t)

  and paren_pretty t =
    let p = pretty t in
    match p with Ext (_, _) -> p | Lit x -> Lit x | _ -> Ext (None, p)

  and fun_pretty p p' =
    match (p, p') with
    | _, Ext (None, Infix (" -> ", ps)) | _, Infix (" -> ", ps) ->
        Infix (" -> ", p :: ps)
    | _, _ -> Infix (" -> ", [ p; p' ])

  and assocs_pretty fs =
    Infix
      ( ", ",
        List.map fs ~f:(fun (l, t) -> Pretty.Infix (": ", [ Lit l; pretty t ]))
      )
end

module Polarity = struct
  type t = Positive | Negative [@@deriving hash, compare, sexp]

  let flip = function Positive -> Negative | Negative -> Positive

  let bounds (x : Type.var) = function
    | Positive -> x.lower
    | Negative -> x.upper
end

module PolarVar = struct
  module T = struct
    type t = Polarity.t * Type.var [@@deriving hash, sexp, compare]
  end

  include Hashable.Make (T)
  include Comparable.Make (T)
end

let coalesce : Type.t -> UserType.t =
  let recursive : string PolarVar.Table.t = PolarVar.Table.create () in
  let rec go (polarity : Polarity.t) (seen : PolarVar.Set.t) :
      Type.t -> UserType.t = function
    | Primitive t -> Primitive t
    | Function (arg, res) ->
        Function (go (Polarity.flip polarity) seen arg, go polarity seen res)
    | Record fs ->
        Record (List.map fs ~f:(fun (l, t) -> (l, go polarity seen t)))
    | Variant ts ->
        Variant (List.map ts ~f:(fun (l, t) -> (l, go polarity seen t)))
    | Variable x -> (
        let var = (polarity, x) in
        match Set.mem seen var with
        | true ->
            Variable
              (Hashtbl.find_or_add recursive var ~default:(fun () ->
                   Type.varname x))
        | false -> (
            let bounds =
              List.map
                (Polarity.bounds x polarity)
                ~f:(go polarity (Set.add seen var))
            in
            let v = UserType.Variable (Type.varname x) in
            let typ : UserType.t =
              match polarity with
              | Positive -> Union (v :: bounds)
              | Negative -> Inter (v :: bounds)
            in
            match Hashtbl.find recursive var with
            | Some r -> Recursive (r, typ)
            | None -> typ))
  in
  go Positive PolarVar.Set.empty

let%expect_test "addition" =
  let test term =
    print_string
      (term |> infer |> coalesce |> UserType.simplify |> UserType.pretty
     |> Pretty.str)
  in
  test (Rcd [ ("x", Lit 0); ("y", Lit 1) ]);
  [%expect {| {x: int, y: int} |}];
  test (Lam ("r", App (Sel (Var "r", "f"), Sel (Var "r", "x"))));
  [%expect {| (x1 /\ {f: x4 /\ (x3 -> x2)} /\ {x: x3}) -> x2 |}];
  test (Lam ("f", Lam ("x", App (Var "f", App (Var "f", Var "x")))));
  [%expect {| (x5 /\ (x8 -> x7) /\ (x6 -> x8)) -> x6 -> x7 |}];
  test
    (let nil = Tag ("Nil", Rcd []) in
     let cons h t = Tag ("Cons", Rcd [ ("head", h); ("tail", t) ]) in
     Let
       ( "stutter",
         Lam
           ( "xs",
             Mat
               ( Var "xs",
                 [
                   ( "Cons",
                     "h",
                     cons
                       (Sel (Var "h", "head"))
                       (cons
                          (Sel (Var "h", "head"))
                          (App (Var "stutter", Sel (Var "h", "tail")))) );
                   ("Nil", "_", nil);
                 ] ) ),
         Var "stutter"
         (* App (Var "stutter", cons (Lit 0) (cons (Lit 1) nil))  *) ));
  [%expect
    {| x9 \/ (x10 -> (x11 \/ [Nil: {}] \/ [Cons: {head: x13, tail: [Cons: {head: x14, tail: fix x15. x15 \/ [Cons: {head: x13, tail: [Cons: {head: x14, tail: x15}]}] \/ [Nil: {}]}]}])) |}]
