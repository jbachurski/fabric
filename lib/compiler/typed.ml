open Core
open Lang.Fabric

let rec til_fix ~equal f x =
  let x' = f x in
  if equal x x' then x else til_fix ~equal f x'

let rec strip_pattern : Expr.pattern -> Expr.pattern = function
  | Atom (x, _) -> Atom (x, T Top)
  | List ps -> List (List.map ~f:strip_pattern ps)

let strip =
  Expr.transform (function
    | Var (x, _) -> Var (x, T Top)
    | Let (x, e, e') -> Let (strip_pattern x, e, e')
    | e -> e)

let propagate' =
  Expr.traverse []
    (fun env p -> Free.pat_free p @ env)
    (fun env -> function
      | Var (x, t) -> (
          match List.Assoc.find env ~equal:String.equal x with
          | Some t' -> Var (x, t')
          | None ->
              raise_s
                [%message "not in scope: " (Expr.pretty_var (x, t) : Sexp.t)])
      | Let (x, e, e') ->
          Let (Expr.type_onto_pattern (Expr.type_expr e) x, e, e')
      | e -> e)
  |> til_fix ~equal:Expr.equal

let propagate e =
  let e = propagate' e in
  ignore (Expr.type_expr e);
  e

let%expect_test "propagate" =
  let test s = s |> Syntax.parse_exn |> propagate |> Expr.pretty |> print_s in
  test "(x: int) => x";
  [%expect {| ((x : int) => (x : int)) |}];
  test "(x: int) => x";
  [%expect {| ((x : int) => (x : int)) |}];
  test "let x = 3 in let y = 4 in (x * x) + (y * y)";
  [%expect
    {|
    (let (x : int) = 3 in
     (let (y : int) = 4 in (+ (* (x : int) (x : int)) (* (y : int) (y : int)))))
    |}];
  test "let x = 0 in let x = x in let x = x in let x = x in let x = x in x";
  [%expect
    {|
    (let (x : int) = 0 in
     (let x = x in (let x = x in (let x = x in (let x = x in x)))))
    |}]

let%expect_test "strip & propagate" =
  let test s =
    let e = s |> Syntax.parse_exn |> strip |> propagate in
    e |> strip |> Expr.pretty |> print_s;
    e |> Expr.pretty |> print_s
  in
  test "(x: int) => x";
  [%expect {|
    ((x : int) => x)
    ((x : int) => (x : int))
    |}];
  test "(x: int) => x";
  [%expect {|
    ((x : int) => x)
    ((x : int) => (x : int))
    |}];
  test "let x: int = 3 in let y: int = 4 in (x * x) + (x * x)";
  [%expect
    {|
    (let x = 3 in (let y = 4 in (+ (* x x) (* x x))))
    (let (x : int) = 3 in
     (let (y : int) = 4 in (+ (* (x : int) (x : int)) (* (x : int) (x : int)))))
    |}];
  test
    "let x0: int = 0 in let x1: int = x0 in let x2 = x1 in let x3 = x2 in let \
     x4: int = x3 in x4";
  [%expect
    {|
    (let x0 = 0 in
     (let x1 = x0 in (let x2 = x1 in (let x3 = x2 in (let x4 = x3 in x4)))))
    (let (x0 : int) = 0 in
     (let (x1 : int) = (x0 : int) in
      (let (x2 : int) = (x1 : int) in
       (let (x3 : int) = (x2 : int) in
        (let (x4 : int) = (x3 : int) in (x4 : int))))))
    |}];
  test
    "let ((x,), (a, b, c)) = ((1,), (2, 3, 4)) in %print_i32 (x + (a * b * c))";
  [%expect
    {|
    (let ((x) (a b c)) = (, (, 1) (, 2 3 4)) in (%print_i32 (+ x (* (* a b) c))))
    (let (((x : int)) ((a : int) (b : int) (c : int))) = (, (, 1) (, 2 3 4)) in
     (%print_i32 (+ (x : int) (* (* (a : int) (b : int)) (c : int)))))
    |}]
