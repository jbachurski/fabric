open Core
open Lang.Fabric

let lift expr =
  let open Free in
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
  (* these types aren't really good for anything since they are actually infinite *)
  [%expect
    {|
    ((functions
      ((capture (x) params v body ((x x) v))
       (capture (f) params x body (f (closure 0 ((x Any)) (* -> *))))
       (capture (x) params v body ((x x) v))
       (capture (f) params x body (f (closure 2 ((x Any)) (* -> *))))
       (capture () params f body
        ((closure 3 ((f Any)) (* -> *)) (closure 1 ((f Any)) (* -> *))))))
     (main (closure 4 () (* -> (* -> *)))))
    |}]
