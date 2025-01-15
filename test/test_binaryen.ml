open Core

let%expect_test "" =
  let open Binaryen in
  let test s f =
    let md =
      s |> Syntax.parse_exn |> Compiler.propagate_types |> Compiler.lift_lambdas
      |> Assembly.assemble
    in
    let valid = Module.validate md > 0 in
    print_s [%message (valid : bool)];
    if not valid then Module.print md else f md;
    Module.dispose md
  in
  test
    "let g = (x: int => 2*x) in let f = (x: int => x+1) in %print_i32 (f (g 1))"
    (fun md ->
      Module.optimize md;
      Module.interpret md);
  [%expect {|
    (valid true)
    3 : i32
    |}]
