open Core
open Lang.Fabric

let rec pat_free : Expr.pattern -> (string * Type.t) list = function
  | Atom (x, t) -> [ (x, t) ]
  | List ps -> List.concat (List.map ~f:pat_free ps)

let capturing p =
  let ys = pat_free p in
  List.filter ~f:(fun (x, _) ->
      not (List.exists ~f:(fun (y, _) -> String.equal x y) ys))

let free =
 fun e ->
  Expr.var_reduce [] List.singleton (Fn.flip capturing) ( @ ) e
  |> List.dedup_and_sort ~compare:(fun (x, _) (y, _) -> String.compare x y)

let%expect_test "free" =
  print_s
    [%sexp
      (free (Let (Atom ("x", Int), Var ("y", Int), Var ("x", Int)))
        : (string * Type.t) list)];
  [%expect {| ((y Int)) |}];
  print_s
    [%sexp
      (free (Op (Var ("f", Any), "", Var ("f", Any))) : (string * Type.t) list)];
  [%expect {| ((f Any)) |}];
  print_s
    [%sexp
      (free (Let (Atom ("x", Int), Var ("x", Int), Var ("y", Int)))
        : (string * Type.t) list)];
  [%expect {| ((x Int) (y Int)) |}];
  print_s
    [%sexp
      (free
         (Op
            ( Var ("a", Int),
              "!",
              Fun
                ( List [ Atom ("x", Function (Int, Int)); Atom ("y", Int) ],
                  Op (Var ("x", Function (Int, Int)), "", Var ("y", Int)) ) ))
        : (string * Type.t) list)];
  [%expect {| ((a Int)) |}]
