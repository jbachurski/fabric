open Fabric

let () =
  let md =
    "let g = (x: int => 2*x) in let f = (x: int => x+1) in %print_i32 (g (f 1))"
    |> Syntax.parse_exn |> Compiler.propagate_types |> Compiler.lift_lambdas
    |> Assembly.assemble
  in
  let valid = Binaryer.C.Module.validate md <> 0 in
  assert valid;
  Binaryer.C.Module.optimize md;
  Binaryer.C.Module.print md;
  (* This aborts *)
  Binaryer.C.Module.interpret md
