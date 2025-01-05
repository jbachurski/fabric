open Angstrom
open Core

module Expr = struct
  type t =
    | Var of string
    | Lit of int
    | Let of string * t * t
    | Fun of string * t
    | Op of t * string * t
  [@@deriving sexp]
end

open Expr

let keyword w =
  let+ () = skip_while Char.is_whitespace
  and+ _ = string w
  and+ () = skip_while Char.is_whitespace in
  ()

let any_name =
  let+ first = satisfy (fun c -> Char.(is_alpha c || c = '_'))
  and+ main = take_while (function c -> Char.(is_alphanum c || c = '_'))
  and+ primes = take_while (fun c -> Char.(c = '\'')) in
  Char.to_string first ^ main ^ primes

let name =
  let* x = any_name in
  if String.(x = "let" || x = "in") then fail "keyword" else return x

let%expect_test "parse var" =
  let parse s = parse_string ~consume:All name s |> Result.ok in
  print_s [%sexp (parse "1" : string option)];
  [%expect {| () |}];
  print_s [%sexp (parse "xyz" : string option)];
  [%expect {| (xyz) |}];
  print_s [%sexp (parse "_1'" : string option)];
  [%expect {| (_1') |}];
  print_s [%sexp (parse "1" : string option)];
  [%expect {| () |}];
  print_s [%sexp (parse "1x" : string option)];
  [%expect {| () |}];
  print_s [%sexp (parse "'x" : string option)];
  [%expect {| () |}]

let var =
  let+ x = name in
  Var x

let int =
  let digits = take_while (function '0' .. '9' -> true | _ -> false) in
  let nonzero_num =
    let+ head = satisfy (function '1' .. '9' -> true | _ -> false)
    and+ tail = digits in
    Char.to_string head ^ tail
  in
  let+ sign = string "-" <|> string "+" <|> return "+"
  and+ dig = string "0" <|> nonzero_num in
  int_of_string (sign ^ dig)

let lit =
  let+ n = int in
  Lit n

let%expect_test "parse lit" =
  let parse s = parse_string ~consume:All int s |> Result.ok in
  print_s [%sexp (parse "0" : int option)];
  [%expect {| (0) |}];
  print_s [%sexp (parse "1" : int option)];
  [%expect {| (1) |}];
  print_s [%sexp (parse "123" : int option)];
  [%expect {| (123) |}];
  print_s [%sexp (parse "100" : int option)];
  [%expect {| (100) |}];
  print_s [%sexp (parse "00" : int option)];
  [%expect {| () |}];
  print_s [%sexp (parse "001" : int option)];
  [%expect {| () |}]

let let_ expr =
  let+ () = keyword "let"
  and+ x = name
  and+ () = keyword "="
  and+ e = expr
  and+ () = keyword "in"
  and+ e' = expr in
  Let (x, e, e')

let op =
  take_while (fun c -> Char.(c = '+' || c = '-' || c = '*' || c = '/'))
  >>| String.strip

let ops expr =
  let+ e = expr
  and+ es =
    many
      (let+ () = skip_while Char.is_whitespace
       and+ o = op
       and+ () = skip_while Char.is_whitespace
       and+ e = expr in
       (o, e))
  in
  List.fold_left ~init:e ~f:(fun e' (o, e) -> Op (e', o, e)) es

let par expr = keyword "(" *> expr <* keyword ")"
let pat = fix (fun pat -> choice [ keyword "(" *> pat <* keyword ")"; name ])

let fun_ expr =
  let+ x = pat and+ () = keyword "=>" and+ e = expr in
  Fun (x, e)

let expr =
  fix (fun expr -> ops (choice [ par expr; let_ expr; fun_ expr; var; lit ]))
  <?> "expr"

let parse = parse_string ~consume:All expr

let%expect_test "parse expr" =
  print_s [%sexp (parse "1" : (Expr.t, string) result)];
  [%expect {| (Ok (Lit 1)) |}];
  print_s [%sexp (parse "x" : (Expr.t, string) result)];
  [%expect {| (Ok (Var x)) |}];
  print_s [%sexp (parse "x x" : (Expr.t, string) result)];
  [%expect {| (Ok (Op (Var x) "" (Var x))) |}];
  print_s [%sexp (parse "((x) ((x)))" : (Expr.t, string) result)];
  [%expect {| (Ok (Op (Var x) "" (Var x))) |}];
  print_s [%sexp (parse "x y z" : (Expr.t, string) result)];
  [%expect {| (Ok (Op (Op (Var x) "" (Var y)) "" (Var z))) |}];
  print_s [%sexp (parse "let x = 1 in x" : (Expr.t, string) result)];
  [%expect {| (Ok (Let x (Lit 1) (Var x))) |}];
  print_s
    [%sexp
      (parse "let x = let y = 1 in y in let z = 2 in z"
        : (Expr.t, string) result)];
  [%expect {| (Ok (Let x (Let y (Lit 1) (Var y)) (Let z (Lit 2) (Var z)))) |}];
  print_s [%sexp (parse "x => y => z => x y z" : (Expr.t, string) result)];
  [%expect
    {| (Ok (Fun x (Fun y (Fun z (Op (Op (Var x) "" (Var y)) "" (Var z)))))) |}];
  print_s
    [%sexp
      (parse "f => (x => g (x x)) (x => g (x x))" : (Expr.t, string) result)];
  [%expect
    {|
    (Ok
     (Fun f
      (Op (Fun x (Op (Var g) "" (Op (Var x) "" (Var x)))) ""
       (Fun x (Op (Var g) "" (Op (Var x) "" (Var x)))))))
    |}]
