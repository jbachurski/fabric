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
      (free (Let (Atom ("x", T Int), Var ("y", T Int), Var ("x", T Int)))
        : (string * Type.t) list)];
  [%expect {| ((y (T Int))) |}];
  print_s
    [%sexp
      (free (Op (Var ("f", T Top), "", Var ("f", T Top)))
        : (string * Type.t) list)];
  [%expect {| ((f (T Top))) |}];
  print_s
    [%sexp
      (free (Let (Atom ("x", T Int), Var ("x", T Int), Var ("y", T Int)))
        : (string * Type.t) list)];
  [%expect {| ((x (T Int)) (y (T Int))) |}];
  print_s
    [%sexp
      (free
         (Op
            ( Var ("a", T Int),
              "!",
              Fun
                ( List
                    [
                      Atom ("x", T (Function (T Int, T Int))); Atom ("y", T Int);
                    ],
                  Op
                    ( Var ("x", T (Function (T Int, T Int))),
                      "",
                      Var ("y", T Int) ) ) ))
        : (string * Type.t) list)];
  [%expect {| ((a (T Int))) |}]
