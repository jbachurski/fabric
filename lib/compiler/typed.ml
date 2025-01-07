open Core
open Lang.Fabric

let propagate =
  Expr.traverse []
    (fun env p -> Free.pat_free p @ env)
    (fun env e ->
      match e with
      | Var (x, t) -> (
          match List.Assoc.find env ~equal:String.equal x with
          | Some t' -> Var (x, t')
          | None ->
              raise_s
                [%message "not in scope: " (Expr.pretty_var (x, t) : Sexp.t)])
      | _ -> e)

let%expect_test "propagate" =
  let test s = s |> Syntax.parse_exn |> propagate |> Expr.pretty |> print_s in
  test "(x: int) => x";
  [%expect {| ((x : int) => (x : int)) |}];
  test "(x: int) => x";
  [%expect {| ((x : int) => (x : int)) |}]
