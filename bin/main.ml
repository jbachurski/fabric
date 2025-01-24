open Core
open Fabric

let binaryen_ir program =
  let (module Ctx) = Binaryer.context_of_module (compile program) in
  let valid = Ctx.validate () in
  print_s [%message (valid : bool)];
  Ctx.print ()

let stack_ir program =
  let (module Ctx) = Binaryer.context_of_module (compile program) in
  assert (Ctx.validate ());
  Ctx.print_stack_ir ()

let interpret program =
  let (module Ctx) = Binaryer.context_of_module (compile program) in
  assert (Ctx.validate ());
  Ctx.interpret ()

let binaryer_ir_command =
  Command.basic ~summary:"Print the Binaryen IR emitted for a Fabric program"
    Command.Param.(
      map (anon ("program" %: string)) ~f:(fun p () -> binaryen_ir p))

let stack_ir_command =
  Command.basic
    ~summary:
      "Print the Stack IR (WebAssembly text) emitted for a Fabric program"
    Command.Param.(map (anon ("program" %: string)) ~f:(fun p () -> stack_ir p))

let interpret_command =
  Command.basic
    ~summary:
      "Run the Binaryen interpreter on the code emitted for a Fabric program"
    Command.Param.(
      map (anon ("program" %: string)) ~f:(fun p () -> interpret p))

let command =
  Command.group ~summary:"The Fabric compiler"
    [
      ("binaryen-ir", binaryer_ir_command);
      ("stack-ir", stack_ir_command);
      ("interpret", interpret_command);
    ]

let () = Command_unix.run ~version:"0.1" ~build_info:"RWO" command
