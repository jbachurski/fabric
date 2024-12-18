open! Core
open Stdlib.Format

module Typ = struct
  type fn = (string * t) list * t
  and prim = Int32 | Int64 | Float64
  and t = Prim of prim | Record | Variant | Fun of fn
end

module Expr = struct
  type t =
    | Var of string
    | App of string * t list
    | Deref of t * int
    | Eq of t * t
    | Add of t * t
    | String of string
    | Lit of int
end

module Stmt = struct
  type t =
    | Assign of string * Expr.t
    | Alloc of string * int
    | Cond of Expr.t * block * block
    | Return of Expr.t
    | Expr of Expr.t

  and block = t list
end

module Prog = struct
  type fn = { fun_typ : Typ.fn; body : Stmt.block }

  type t = {
    headers : string list;
    preamble : string;
    functions : (string * fn) list;
    main : Stmt.block;
  }
end

let pp_print_list_sep sep =
  pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt sep)

let print_prim_typ fmt : Typ.prim -> unit = function
  | Int32 -> fprintf fmt "int"
  | Int64 -> fprintf fmt "long"
  | Float64 -> fprintf fmt "double"

let rec print_named_typ fmt : string * Typ.t -> unit = function
  | name, Prim t -> fprintf fmt "%a %s" print_prim_typ t name
  | name, Record -> fprintf fmt "void* %s" name
  | name, Variant -> fprintf fmt "void* %s" name
  | name, Fun (args, result) ->
      fprintf fmt "%a (*%s)(%a)" print_named_typ ("", result) name
        (pp_print_list_sep "," print_named_typ)
        args

let rec print_expr fmt : Expr.t -> unit = function
  | Var x -> fprintf fmt "%s" x
  | App (name, args) ->
      fprintf fmt "%s(%a)" name (pp_print_list_sep "," print_expr) args
  | Deref (e, n) -> fprintf fmt "(%a)[8 * %d]" print_expr e n
  | Eq (e, e') -> fprintf fmt "(%a) == (%a)" print_expr e print_expr e'
  | Add (e, e') -> fprintf fmt "(%a) + (%a)" print_expr e print_expr e'
  | String s -> fprintf fmt "\"%s\"" s
  | Lit n -> fprintf fmt "%d" n

let rec print_stmt fmt : Stmt.t -> unit = function
  | Assign (name, expr) -> fprintf fmt "%s = %a" name print_expr expr
  | Alloc (name, words) -> fprintf fmt "%s = malloc(8 * %d)" name words
  | Cond (test, if_true, if_false) ->
      fprintf fmt "if(%a) %a else %a" print_expr test print_block if_true
        print_block if_false
  | Return expr -> fprintf fmt "return %a" print_expr expr
  | Expr expr -> print_expr fmt expr

and print_block fmt = fprintf fmt "{ %a; }" (pp_print_list_sep "; " print_stmt)

let print_func fmt (name, Prog.{ fun_typ = args, result; body }) =
  fprintf fmt "%a %s(%a) %a\n" print_named_typ ("", result) name
    (pp_print_list_sep "," print_named_typ)
    args print_block body

let print_prog fmt Prog.{ headers; preamble; functions; main } =
  fprintf fmt "%a\n%s\n%a\n%a"
    (pp_print_list (fun fmt -> fprintf fmt "#include <%s>\n"))
    headers preamble
    (pp_print_list_sep "\n" print_func)
    functions print_func
    ("main", { fun_typ = ([], Prim Int32); body = main })

let%expect_test "fib" =
  print_prog std_formatter
    {
      headers = [ "stdio.h" ];
      preamble = "";
      functions =
        [
          ( "fib",
            {
              fun_typ = ([ ("n", Prim Int64) ], Prim Int64);
              body =
                [
                  Cond
                    ( Eq (Var "n", Lit 0),
                      [ Return (Lit 0) ],
                      [
                        Cond
                          ( Eq (Var "n", Lit 1),
                            [ Return (Lit 1) ],
                            [
                              Return
                                (Add
                                   ( App ("fib", [ Add (Var "n", Lit (-1)) ]),
                                     App ("fib", [ Add (Var "n", Lit (-2)) ]) ));
                            ] );
                      ] );
                ];
            } );
        ];
      main = [ Expr (App ("printf", [ String "%d"; App ("fib", [ Lit 10 ]) ])) ];
    };
  [%expect
    {|
    #include <stdio.h>


    long  fib(long n) { if((n) == (0)) { return 0; } else { if((n) == (1)) { return 1; } else { return (fib((n) + (-1))) + (fib((n) + (-2))); }; }; }

    int  main() { printf("%d",fib(10)); }
    |}]
