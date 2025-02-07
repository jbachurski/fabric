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
          Closure (k, xs, T (Function (Expr.type_pattern x, Expr.type_expr e)))
      | e -> e)
  in
  let main = go expr in
  Prog.{ functions = List.rev !functions; main }

let%expect_test "lift" =
  let z =
    Expr.(
      Fun
        ( Atom ("x", T Top),
          Op
            ( Var ("f", T Top),
              "",
              Fun
                ( Atom ("v", T Top),
                  Op
                    ( Op (Var ("x", T Top), "", Var ("x", T Top)),
                      "",
                      Var ("v", T Top) ) ) ) ))
  in
  print_s (lift (Fun (Atom ("f", T Top), Op (z, "", z))) |> Prog.pretty);
  (* these types aren't really good for anything since they are actually infinite *)
  [%expect
    {|
    ((functions
      ((capture (x) params v body ((x x) v))
       (capture (f) params x body (f (closure 0 ((x (T Top))) (top -> top))))
       (capture (x) params v body ((x x) v))
       (capture (f) params x body (f (closure 2 ((x (T Top))) (top -> top))))
       (capture () params f body
        ((closure 3 ((f (T Top))) (top -> top))
         (closure 1 ((f (T Top))) (top -> top))))))
     (main (closure 4 () (top -> (top -> top)))))
    |}]
