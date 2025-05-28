open Angstrom
open Core
open Lang.Fabric
open Lang.Sym
open Expr

let init_name_char c = Char.(is_lowercase c || c = '_')
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
  if String.(x = "let" || x = "in" || x = "match" || x = "with") then
    fail "keyword"
  else return x

let label = name
let init_tag_char c = Char.(is_uppercase c)

let tag =
  let+ first = satisfy init_tag_char and+ main = take_while name_char in
  Char.to_string first ^ main

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

let wrap l r expr = special l *> expr <* special r
let paren expr = wrap "(" ")" expr
let brack expr = wrap "[" "]" expr
let brace expr = wrap "{" "}" expr

let sep_list1 ~sep expr =
  let+ es =
    many
      (let+ e = expr and+ () = special sep in
       e)
  and+ e = option None (map ~f:Option.some expr) in
  match e with None -> es | Some e -> es @ [ e ]

(* requires at least one comma in the list *)
let sep_list ~sep expr = sep_list1 ~sep expr <|> return []
let prim_type = keyword "int" *> return (Type.T Int)

let record_type type_ =
  sep_list ~sep:","
    (let+ l = name and+ () = special ":" and+ e = type_ in
     (Label.of_string l, Type.Field.Present e))
  |> brace
  |> map ~f:(fun fs ->
         Type.T (Record (Label.Map.of_alist_exn fs |> Type.Fields.open_)))

let array_type type_ =
  let+ () = special "[]" and+ t = type_ in
  Type.T (Array t)

let type_ =
  fix (fun type_ -> choice [ prim_type; record_type type_; array_type type_ ])

let var =
  let+ x = name in
  Var (x, T Top)

let pattern =
  fix (fun pattern ->
      choice
        Expr.
          [
            paren pattern;
            (let+ ps = paren (sep_list ~sep:"," pattern) in
             List ps);
            (let+ x = name
             and+ t = special ":" *> type_ <|> return (Type.T Top) in
             Atom (x, t));
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

let unify expr =
  let+ () = keyword "let"
  and+ x = name
  and+ () = special "~"
  and+ x' = name
  and+ () = keyword "in"
  and+ e = expr in
  Unify (x, x', e)

let op =
  choice
    [
      string "==";
      string "!=";
      string ">=";
      string ">";
      string "<=";
      string "<";
      string ";";
      take_while (fun c -> Char.(c = '+' || c = '-' || c = '*' || c = '/'));
    ]

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

let tuple expr =
  let+ es = paren (sep_list ~sep:"," expr) in
  Tuple es

let cons expr =
  sep_list ~sep:","
    (let+ l = name and+ () = special ":" and+ e = expr in
     (l, e))
  |> brace
  |> map ~f:(fun fs -> Cons fs)

let idxs pre_expr expr =
  let+ e = pre_expr and+ js = many (brack expr) in
  List.fold_left js ~init:e ~f:(fun e j -> Idx (e, j))

let atomic expr =
  let pre = paren expr <|> tuple expr <|> cons expr <|> var <|> lit in
  idxs pre expr

let fun_ expr =
  let+ x = pattern and+ () = special "=>" and+ e = expr in
  Fun (x, e)

let shape_pattern expr =
  (let+ i = name and+ () = special ":" and+ n = expr in
   (i, n))
  |> brack

let arr expr =
  let+ i, n = shape_pattern expr and+ () = special "=>" and+ e = expr in
  Array (i, n, e)

let shape expr =
  let+ () = special "#" and+ e = atomic expr in
  Shape e

let proj expr =
  let+ e = atomic expr
  and+ ls =
    many1
      (choice
         [
           (let+ () = special "." and+ l = label in
            (l, false));
           (let+ () = special ".?" and+ l = label in
            (l, true));
         ])
  in
  List.fold ls ~init:e ~f:(fun e (l, c) -> Proj (e, l, c))

let restrict expr =
  let+ e = atomic expr and+ () = special "\\" and+ l = label in
  Restrict (e, l)

let extend expr =
  brace
    (let+ ls =
       sep_list ~sep:","
         (let+ l = label and+ () = special ":" and+ e = expr in
          (l, e))
     and+ () = special "|"
     and+ e' = expr in
     List.fold ls ~init:e' ~f:(fun e' (l, e) -> Extend (l, e, e')))

let tagged expr =
  let+ t = tag
  and+ () = skip_many1 (satisfy Char.is_whitespace)
  and+ e = atomic expr in
  Tag (t, e)

let match_case expr =
  let+ t = tag
  and+ () = skip_many1 (satisfy Char.is_whitespace)
  and+ x = name
  and+ () = special "=>"
  and+ e = expr in
  ((t, x), e)

let match_ expr =
  let+ () = keyword "match"
  and+ e = expr
  and+ () = keyword "with"
  and+ () = option () (special "|")
  and+ c = match_case expr
  and+ cs =
    many
      (let+ () = special "|" and+ c = match_case expr in
       c)
  in
  Match (e, c :: cs)

let intrinsic expr =
  let+ () = skip_while Char.is_whitespace
  and+ _ = string "%"
  and+ f = name
  and+ () = skip_while Char.is_whitespace
  and+ e = atomic expr in
  Intrinsic (f, e)

let expr =
  fix (fun expr ->
      choice
        [
          let_ expr;
          unify expr;
          arr expr;
          shape expr;
          proj expr;
          restrict expr;
          extend expr;
          tagged expr;
          match_ expr;
          intrinsic expr;
          fun_ expr;
          atomic expr;
        ]
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
  pparse "((), (x,), (x, y), (x, y,), (x, y, z))";
  [%expect {| (Ok (, (,) (, x) (, x y) (, x y) (, x y z))) |}];
  pparse "let ((x,), (a, b, c)) = ((1,), (2, 3, 4)) in x + (a * b * c)";
  [%expect
    {| (Ok (let ((x) (a b c)) = (, (, 1) (, 2 3 4)) in (+ x (* (* a b) c)))) |}];
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
  [%expect {| (Ok ([ i : (# a) ] => (a [ i ]))) |}];
  pparse "[i: 5] => a[i+1][i+2]";
  [%expect {| (Ok ([ i : 5 ] => ((a [ (+ i 1) ]) [ (+ i 2) ]))) |}];
  pparse "(%print 1, %print x, %print (2 + 2))";
  [%expect {| (Ok (, (%print 1) (%print x) (%print (+ 2 2)))) |}];
  pparse "let o = {} in { foo : 1, bar : 2, }.foo";
  [%expect {| (Ok (let o = ({ }) in (({ (foo 1) (bar 2) }) . foo))) |}];
  pparse "let x: {foo: int, bar: int} = {foo: int, bar: int} in x.foo";
  [%expect
    {|
    (Ok
     (let (x : ({ (bar int) (foo int) | ? })) = ({ (foo int) (bar int) }) in
      (x . foo)))
    |}];
  pparse
    "let f = ((x: {foo: int, bar: int}) => x.foo) in \n\
     let g = ((x: {foo: int, bar: int}) => x.bar) in \n\
     let x = {foo: 4, bar: 3} in %print_i32 (f x - g x)";
  [%expect
    {|
    (Ok
     (let f = ((x : ({ (bar int) (foo int) | ? })) => (x . foo)) in
      (let g = ((x : ({ (bar int) (foo int) | ? })) => (x . bar)) in
       (let x = ({ (foo 4) (bar 3) }) in (%print_i32 ((- (f x) g) x))))))
    |}];
  pparse
    "let tab = [i: 5] => [j: 5] => {sum: i + j, prod: i * j} in \n\
     let fun = i: int => j: int => tab[i][j].sum + tab[i][j].prod + 1 in \n\
     %print_i32 (fun 2 3)";
  [%expect
    {|
    (Ok
     (let tab = ([ i : 5 ] => ([ j : 5 ] => ({ (sum (+ i j)) (prod (* i j)) })))
      in
      (let fun =
       ((i : int) =>
        ((j : int) =>
         (+ (+ (((tab [ i ]) [ j ]) . sum) (((tab [ i ]) [ j ]) . prod)) 1)))
       in (%print_i32 ((fun 2) 3)))))
    |}];
  pparse
    "let tab: [][]{sum: int, prod: int} = [i: 5] => [j: 5] => {sum: i + j, \
     prod: i * j} in ()";
  [%expect
    {|
    (Ok
     (let (tab : ([] ([] ({ (prod int) (sum int) | ? })))) =
      ([ i : 5 ] => ([ j : 5 ] => ({ (sum (+ i j)) (prod (* i j)) }))) in
      (,)))
    |}];
  pparse "r => {b: r.b.not() | r}";
  [%expect {| (Ok (r => ({ b = (((r . b) . not) (,)) | r }))) |}];
  pparse "r => {prev: r.next, next: r.prev + r.next | {prev: 5, next: 8}}";
  [%expect
    {|
    (Ok
     (r =>
      ({ next = (+ (r . prev) (r . next)) |
       ({ prev = (r . next) | ({ (prev 5) (next 8) }) }) })))
    |}];
  pparse "T 10";
  [%expect {| (Ok (T 10)) |}];
  pparse "match x with T y => y";
  [%expect {| (Ok (match x ((T y => y)))) |}];
  pparse "x => match T x with A a => 0 | B b => 1 | C c => 2";
  [%expect {| (Ok (x => (match (T x) ((A a => 0) (B b => 1) (C c => 2))))) |}];
  pparse "(p, v, d) => match (p v) with True _ => v | False _ => d";
  [%expect {| (Ok ((p v d) => (match (p v) ((True _ => v) (False _ => d))))) |}];
  pparse
    "let stutter = xs => match xs with \n\
     | Nil _ => Nil () \n\
     | Cons c => Cons { \n\
     head: c.head, \n\
     tail: Cons { head: c.head, tail: stutter c.tail }} \n\
     in stutter";
  [%expect
    {|
    (Ok
     (let stutter =
      (xs =>
       (match xs
        ((Nil _ => (Nil (,)))
         (Cons c =>
          (Cons
           ({ (head (c . head))
            (tail (Cons ({ (head (c . head)) (tail (stutter (c . tail))) }))) }))))))
      in stutter))
    |}];
  pparse "x == 0";
  [%expect {| (Ok (== x 0)) |}];
  pparse "(x == 0); (x != 0); (x > 0); (x >= 0); (x < 0); (x <= 0)";
  [%expect
    {|
    (Ok
     (";" (";" (";" (";" (";" (== x 0) (!= x 0)) (> x 0)) (>= x 0)) (< x 0))
      (<= x 0)))
    |}]
