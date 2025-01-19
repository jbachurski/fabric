open Core
open Fabric

let%expect_test "compile" =
  let test program =
    let (module Ctx) = Binaryer.context_of_module (compile program) in
    let open Ctx in
    let valid = validate () in
    print_s [%message (valid : bool)];
    if not valid then print () else interpret ()
  in
  test "%print_i32 (42)";
  [%expect {|
    (valid true)
    42 : i32
    |}];
  test "%print_i32 (2 + (4 - 2))";
  [%expect {|
    (valid true)
    4 : i32
    |}];
  test "let id = (x: int => x) in %print_i32 (id 42)";
  [%expect {|
    (valid true)
    42 : i32
    |}];
  test "let (x, y) = (2, 3) in %print_i32 (x + y)";
  [%expect {|
    (valid true)
    5 : i32
    |}];
  test
    "let ((x,), (a, b, c)) = ((1,), (2, 3, 4)) in %print_i32 (x + (a * b * c))";
  [%expect {|
    (valid true)
    25 : i32
    |}];
  test "let square = (x: int => x * x) in %print_i32 ((square 3) + (square 4))";
  [%expect {|
    (valid true)
    25 : i32
    |}];
  test
    "let a = 1 in let b = 2 in let f = (x: int => (x*b)+a) in %print_i32 (f 3)";
  [%expect {|
    (valid true)
    7 : i32
    |}];
  test
    "let g = (x: int => 2*x) in let f = (x: int => x+1) in %print_i32 (g (f 1))";
  [%expect {|
    (valid true)
    4 : i32
    |}];
  test
    "let f = ((x: {foo: int}) => x.foo) in \n\
     let g = ((x: {bar: int}) => x.bar) in \n\
     let x = {baz: 0, bar: 3, foo: 4, boo: 1} in %print_i32 ((f x) - (g x))";
  [%expect {|
    (valid true)
    1 : i32
    |}]
