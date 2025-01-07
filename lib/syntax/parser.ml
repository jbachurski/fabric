open Angstrom
open Core
open Lang.Fabric
open Expr

let init_name_char c = Char.(is_alpha c || c = '_')
let name_char c = Char.(is_alphanum c || c = '_')

let token ~deny w =
  let* () = skip_while Char.is_whitespace
  and+ _ = string w
  and+ next = peek_char
  and+ () = skip_while Char.is_whitespace in
  if Option.map ~f:deny next |> Option.value ~default:false then
    fail "keyword followed by a name character"
  else return ()

let keyword = token ~deny:name_char
let special = token ~deny:(Fn.const false)

let any_name =
  let+ first = satisfy init_name_char
  and+ main = take_while name_char
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

let type_ =
  let+ () = keyword "int" in
  Type.Int

let var =
  let+ x = name in
  Var (x, Any)

let pattern =
  fix (fun pattern ->
      choice
        [
          special "(" *> pattern <* special ")";
          (let+ x = name and+ t = special ":" *> type_ <|> return Type.Any in
           Expr.Atom (x, t));
        ])

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
  and+ x = pattern
  and+ () = special "="
  and+ e = expr
  and+ () = keyword "in"
  and+ e' = expr in
  Let (x, e, e')

let op =
  take_while (fun c ->
      Char.(c = '+' || c = '-' || c = '*' || c = '/' || c = '.'))
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

let par expr = special "(" *> expr <* special ")"
let atomic expr = par expr <|> var <|> lit

let fun_ expr =
  let+ x = pattern and+ () = special "=>" and+ e = expr in
  Fun (x, e)

let idx expr =
  let+ e = atomic expr
  and+ js =
    many1
      (let+ () = special "[" and+ j = expr and+ () = special "]" in
       j)
  in
  List.fold_left js ~init:e ~f:(fun e j -> Idx (e, j))

let shape_pattern expr =
  let+ () = special "["
  and+ i = name
  and+ () = special ":"
  and+ n = expr
  and+ () = special "]" in
  (i, n)

let arr expr =
  let+ i, n = shape_pattern expr and+ () = special "=>" and+ e = expr in
  Array (i, n, e)

let shape expr =
  let+ () = special "#" and+ e = atomic expr in
  Shape e

let expr =
  fix (fun expr ->
      choice
        [ let_ expr; idx expr; arr expr; shape expr; fun_ expr; atomic expr ]
      |> ops)
  <?> "expr"

let parse = parse_string ~consume:All expr

let%expect_test "parse expr" =
  let pparse s =
    print_s
      [%sexp (parse s |> Result.map ~f:Expr.pretty : (Sexp.t, string) result)]
  in
  pparse "1";
  [%expect {| (Ok 1) |}];
  pparse "x";
  [%expect {| (Ok x) |}];
  pparse "x x";
  [%expect {| (Ok (x x)) |}];
  pparse "((x) ((x)))";
  [%expect {| (Ok (x x)) |}];
  pparse "x y z";
  [%expect {| (Ok ((x y) z)) |}];
  pparse "let x = 1 in x";
  [%expect {| (Ok (let x = 1 in x)) |}];
  pparse "let x = let y = 1 in y in let z = 2 in z";
  [%expect {| (Ok (let x = (let y = 1 in y) in (let z = 2 in z))) |}];
  pparse "x: int => x";
  [%expect {| (Ok ((x : int) => x)) |}];
  pparse "x => y => z => x y z";
  [%expect {| (Ok (x => (y => (z => ((x y) z))))) |}];
  pparse "f => (x => g (x x)) (x => g (x x))";
  [%expect {| (Ok (f => ((x => (g (x x))) (x => (g (x x)))))) |}];
  pparse "[i: 5] => f i";
  [%expect {| (Ok ([ i : 5 ] => (f i))) |}];
  pparse "[i: #a] => a[i]";
  [%expect {| (Ok ([ i : (# a) ] => ([] a i))) |}];
  pparse "[i: 5] => a[i+1][i+2]";
  [%expect {| (Ok ([ i : 5 ] => ([] ([] a (+ i 1)) (+ i 2)))) |}]
