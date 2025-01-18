open Core
open Fabric

let%expect_test "assemble" =
  let test program =
    let (module Ctx) = Binaryer.context_of_module (compile program) in
    let open Ctx in
    let valid = validate () in
    print_s [%message (valid : bool)];
    if not valid then print_stack_ir () else interpret ()
  in
  test "%print_i32 (42)";
  [%expect {|
    (valid true)
    42 : i32
    |}];
  test "let id = (x: int => x) in %print_i32 (id 42)";
  [%expect {|
    (valid true)
    42 : i32
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
    |}]
