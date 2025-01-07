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

let lift expr =
  let functions : ((string * Type.t) list * Expr.pattern * Expr.t) list ref =
    ref []
  in
  let go =
    Expr.transform (function
      | Fun (x, e) ->
          let xs = free e |> capturing x in
          let k = List.length !functions in
          functions := (xs, x, e) :: !functions;
          Closure (k, xs, Function (Expr.type_pattern x, Expr.type_expr e))
      | e -> e)
  in
  let main = go expr in
  Prog.{ functions = List.rev !functions; main }

let%expect_test "lift" =
  let z =
    Expr.(
      Fun
        ( Atom ("x", Any),
          Op
            ( Var ("f", Any),
              "",
              Fun
                ( Atom ("v", Any),
                  Op
                    (Op (Var ("x", Any), "", Var ("x", Any)), "", Var ("v", Any))
                ) ) ))
  in
  print_s (lift (Fun (Atom ("f", Any), Op (z, "", z))) |> Prog.pretty);
  [%expect
    {|
    ((functions
      ((capture (x) params v body ((x x) v))
       (capture (f) params x body (f (closure 0 ((x Any)) (* -> *))))
       (capture (x) params v body ((x x) v))
       (capture (f) params x body (f (closure 2 ((x Any)) (* -> *))))
       (capture () params f body
        ((closure 3 ((f Any)) (* -> *)) (closure 1 ((f Any)) (* -> *))))))
     (main (closure 4 () (* -> *))))
    |}]
