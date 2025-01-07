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

let%expect_test "free" =
  print_s (propagate (Fun (Atom ("x", Int), Var ("x", Any))) |> Expr.pretty);
  [%expect {| ((x : int) => (x : int)) |}];
  print_s (propagate (Fun (Atom ("x", Int), Var ("x", Int))) |> Expr.pretty);
  [%expect {| ((x : int) => (x : int)) |}]
