open Core
open Fabric

let play program =
  let (module Ctx) = Binaryer.context_of_module (compile program) in
  let open Ctx in
  let valid = validate () in
  print_s [%message (valid : bool)];
  if not valid then print ()
  else (
    print_stack_ir ();
    interpret ())

open Core

let command =
  Command.basic ~summary:"Compile and interpret a Fabric program"
    Command.Param.(
      map (anon ("program" %: string)) ~f:(fun program () -> play program))

let () = Command_unix.run ~version:"0.1" ~build_info:"RWO" command
