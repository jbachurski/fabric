module Binaryer = Binaryer
module Assembly = Assembly
module Compiler = Compiler
module Lang = Lang
module Syntax = Syntax
module Types = Types

let compile program =
  program |> Syntax.parse_exn |> Compiler.propagate_types
  |> Compiler.lift_lambdas |> Assembly.assemble
