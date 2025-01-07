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
  let rec go : Expr.t -> (string * Type.t) list = function
    | Var (x, t) -> [ (x, t) ]
    | Lit _ -> []
    | Let (x, e, e') -> go e @ (go e' |> capturing x)
    | Fun (x, e) -> go e |> capturing x
    | Tuple es -> List.concat (List.map ~f:go es)
    | Array (i, e, e') -> go e @ (go e' |> capturing (Atom (i, Int)))
    | Idx (e, e') -> go e @ go e'
    | Shape e -> go e
    | Op (e, _o, e') -> go e @ go e'
    | Closure (_k, xs) -> xs
  in
  fun e ->
    go e
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
          Closure (k, xs)
      | e -> e)
  in
  let body = go expr in
  Prog.{ functions = List.rev !functions; body }

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
  print_s [%sexp (lift (Fun (Atom ("f", Any), Op (z, "", z))) : Prog.t)];
  [%expect
    {|
    ((functions
      ((((x Any)) (Atom v Any)
        (Op (Op (Var x Any) "" (Var x Any)) "" (Var v Any)))
       (((f Any)) (Atom x Any) (Op (Var f Any) "" (Closure 0 ((x Any)))))
       (((x Any)) (Atom v Any)
        (Op (Op (Var x Any) "" (Var x Any)) "" (Var v Any)))
       (((f Any)) (Atom x Any) (Op (Var f Any) "" (Closure 2 ((x Any)))))
       (() (Atom f Any) (Op (Closure 3 ((f Any))) "" (Closure 1 ((f Any)))))))
     (body (Closure 4 ())))
    |}]
