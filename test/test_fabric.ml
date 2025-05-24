open Core
open Fabric

let%expect_test "compile" =
  let test program =
    print_s (Syntax.parse_exn program |> Lang.Fabric.Expr.pretty);
    match Types.Fabric.check (Syntax.parse_exn program) with
    | Ok () ->
        let (module Ctx) = Binaryer.context_of_module (compile program) in
        let open Ctx in
        let valid = validate () in
        print_s [%message (valid : bool)];
        if not valid then print () else interpret ()
    | Error type_error -> print_s [%message (type_error : Error.t)]
  in
  let test program =
    try test program
    with e ->
      let msg = Exn.to_string e and stack = Printexc.get_backtrace () in
      Printf.eprintf "exception: %s\n%s\n" msg stack
  in
  test "%print_i32 (42)";
  [%expect {|
    (%print_i32 42)
    (valid true)
    42 : i32
    |}];
  test "%print_i32 (2 + (4 - 2))";
  [%expect
    {|
    (%print_i32 (+ 2 (- 4 2)))
    (valid true)
    4 : i32
    |}];
  test "let id = (x: int => x) in %print_i32 (id 42)";
  [%expect
    {|
    (let id = ((x : int) => x) in (%print_i32 (id 42)))
    (valid true)
    42 : i32
    |}];
  test "let (x, y) = (2, 3) in %print_i32 (x + y)";
  [%expect
    {|
    (let (x y) = (, 2 3) in (%print_i32 (+ x y)))
    (valid true)
    5 : i32
    |}];
  test
    "let ((x,), (a, b, c)) = ((1,), (2, 3, 4)) in %print_i32 (x + (a * b * c))";
  [%expect
    {|
    (let ((x) (a b c)) = (, (, 1) (, 2 3 4)) in (%print_i32 (+ x (* (* a b) c))))
    (valid true)
    25 : i32
    |}];
  test "let square = (x: int => x * x) in %print_i32 ((square 3) + (square 4))";
  [%expect
    {|
    (let square = ((x : int) => (* x x)) in
     (%print_i32 (+ (square 3) (square 4))))
    (valid true)
    25 : i32
    |}];
  test
    "let a = 1 in let b = 2 in let f = (x: int => (x*b)+a) in %print_i32 (f 3)";
  [%expect
    {|
    (let a = 1 in
     (let b = 2 in (let f = ((x : int) => (+ (* x b) a)) in (%print_i32 (f 3)))))
    (valid true)
    7 : i32
    |}];
  test
    "let g = (x: int => 2*x) in let f = (x: int => x+1) in %print_i32 (g (f 1))";
  [%expect
    {|
    (let g = ((x : int) => (* 2 x)) in
     (let f = ((x : int) => (+ x 1)) in (%print_i32 (g (f 1)))))
    (valid true)
    4 : i32
    |}];
  test "let a = [i: 10] => i * i in %print_i32 (a[5])";
  [%expect
    {|
    (let a = ([ i : 10 ] => (* i i)) in (%print_i32 (a [ 5 ])))
    (valid true)
    25 : i32
    |}];
  test "let a = [i: 5] => [j: 5] => i - j in %print_i32 (a[4][3])";
  [%expect
    {|
    (let a = ([ i : 5 ] => ([ j : 5 ] => (- i j))) in
     (%print_i32 ((a [ 4 ]) [ 3 ])))
    (valid true)
    1 : i32
    |}];
  test
    "let a = [i: 5] => [j: 5] => i - j in\n\
     let f = i: int => j: int => i + j in\n\
     %print_i32 (a[4][2] * (f 4 2))";
  [%expect
    {|
    (let a = ([ i : 5 ] => ([ j : 5 ] => (- i j))) in
     (let f = ((i : int) => ((j : int) => (+ i j))) in
      (%print_i32 (* ((a [ 4 ]) [ 2 ]) ((f 4) 2)))))
    (valid true)
    12 : i32
    |}];
  test
    "let f = ((x: {foo: int}) => x.foo) in \n\
     let g = ((x: {bar: int}) => x.bar) in \n\
     let x = {baz: 0, bar: 3, foo: 4, boo: 1} in %print_i32 ((f x) - (g x))";
  [%expect
    {|
    (let f = ((x : ({ (foo int) | ? })) => (x . foo)) in
     (let g = ((x : ({ (bar int) | ? })) => (x . bar)) in
      (let x = ({ (baz 0) (bar 3) (foo 4) (boo 1) }) in
       (%print_i32 (- (f x) (g x))))))
    (valid true)
    1 : i32
    |}];
  test
    "let tab: [][]{sum: int, prod: int} = \n\
     [i: 5] => [j: 5] => {sum: i + j, prod: i * j} \n\
     in \n\
     let fun = i: int => j: int => tab[i][j].sum + tab[i][j].prod + 1 in \n\
     %print_i32 (fun 2 3)";
  [%expect
    {|
    (let (tab : ([] ([] ({ (prod int) (sum int) | ? })))) =
     ([ i : 5 ] => ([ j : 5 ] => ({ (sum (+ i j)) (prod (* i j)) }))) in
     (let fun =
      ((i : int) =>
       ((j : int) =>
        (+ (+ (((tab [ i ]) [ j ]) . sum) (((tab [ i ]) [ j ]) . prod)) 1)))
      in (%print_i32 ((fun 2) 3))))
    (valid true)
    12 : i32
    |}];
  test "let y = 5 in match T y with T x => %print_i32 x";
  [%expect
    {|
    (let y = 5 in (match (T y) ((T x => (%print_i32 x)))))
    (valid true)
    5 : i32
    |}];
  test
    "let abs = x => match x > 0 with True _ => x | False _ => 0-x in \
     %print_i32 (abs 5); %print_i32 (abs (-4))";
  [%expect
    {|
    (let abs = (x => (match (> x 0) ((True _ => x) (False _ => (- 0 x))))) in
     (";" (%print_i32 (abs 5)) (%print_i32 (abs -4))))
    (valid true)
    5 : i32
    4 : i32
    |}];
  test
    "let y = f => let z = x => f (v => x x v) in z z in\n\
     let fib = y (fib => n => \n\
     match n > 1 with \n\
     | True _ => (fib (n - 1)) + (fib (n - 2)) \n\
     | False _ => n) in \n\
     %print_i32 (fib 8)";
  [%expect
    {|
    (let y = (f => (let z = (x => (f (v => ((x x) v)))) in (z z))) in
     (let fib =
      (y
       (fib =>
        (n =>
         (match (> n 1)
          ((True _ => (+ (fib (- n 1)) (fib (- n 2)))) (False _ => n))))))
      in (%print_i32 (fib 8))))
    (valid true)
    21 : i32
    |}];
  test
    "let y = f => let z = x => f (v => x x v) in z z in\n\
     let print = y (print => xs => \n\
     match xs with \n\
     | Cons c => (%print_i32 (c.head)); (print (c.tail))  \n\
     | Nil _ => ()) in \n\
     print (Cons { head: 1, tail: Cons { head: 2, tail: Cons { head: 3, tail: \
     Nil () }}})";
  [%expect
    {|
    (let y = (f => (let z = (x => (f (v => ((x x) v)))) in (z z))) in
     (let print =
      (y
       (print =>
        (xs =>
         (match xs
          ((Cons c => (";" (%print_i32 (c . head)) (print (c . tail))))
           (Nil _ => (,)))))))
      in
      (print
       (Cons
        ({ (head 1)
         (tail
          (Cons ({ (head 2) (tail (Cons ({ (head 3) (tail (Nil (,))) }))) })))
         })))))
    (valid true)
    1 : i32
    2 : i32
    3 : i32
    |}]
