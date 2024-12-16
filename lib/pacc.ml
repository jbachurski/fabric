open! Core

let compile : Yarn.Prog.t -> Cc.Prog.t =
 fun { defs = _; externs = _; main = _ } ->
  Cc.Prog.{ headers = []; preamble = ""; functions = []; main = [] }

let%expect_test "compile" =
  let nm = Env.Name.of_string in
  App (Var (nm "__add"), Tuple [ Lit 5; Lit 7 ])
  |> Spin.compile |> compile
  |> Cc.print_prog Format.std_formatter;
  [%expect
    {| int  main() { ; } |}]
