open! Core
open Env

let without xs =
  List.filter ~f:(fun y -> not @@ List.mem xs y ~equal:Name.equal)

let free_variables =
  let rec go : Fiber.Expr.t -> name list = function
    | Trap -> []
    | Lit _ -> []
    | Var x -> [ x ]
    | Abs (r, x, _, e) -> without [ r; x ] (go e)
    | Tuple es -> List.map es ~f:go |> List.concat
    | Untuple (xs, e, e') -> go e @ without xs (go e')
    | App (f, e) -> go f @ go e
    (*
    | Proj (e, _) -> go e
    | Tag (_, e) -> go e
    | Match (e, _, x, e', e'') ->
        go e @ without [ x ] (go e') @ without [ x ] (go e'')
    *)
  in
  fun expr -> List.dedup_and_sort (go expr) ~compare:Name.compare

let%expect_test "free_variables" =
  let nm = Name.of_string in
  let var x = Fiber.Expr.Var (nm x) in
  let fn x t e = Fiber.Expr.Abs (nm "", nm x, t, e) in
  print_s [%sexp (free_variables (Var (nm "x")) : Name.t list)];
  [%expect {| (x) |}];
  print_s
    [%sexp
      (free_variables
         (Untuple
            ( [ nm "x"; nm "y" ],
              Tuple [ var "z"; var "w" ],
              fn "t" Fiber.Type.Int (App (var "x", var "t")) ))
        : Name.t list)];
  [%expect {| (w z) |}]

let rec closure_ren pre post : Yarn.Expr.t -> Yarn.Expr.t = function
  | Trap -> Trap
  | Lit n -> Lit n
  | Var x -> if Name.equal x pre then Var post else Var x
  | Let (x, e, e') ->
      Let
        ( x,
          closure_ren pre post e,
          if Name.equal x pre then e' else closure_ren pre post e' )
  | App (e, e') -> App (closure_ren pre post e, closure_ren pre post e')
  | Closure (x, xs) -> Closure (x, xs)
  | Tuple es -> Tuple (List.map ~f:(closure_ren pre post) es)
  | Untuple (xs, e, e') ->
      Untuple
        ( xs,
          closure_ren pre post e,
          if List.mem xs pre ~equal:Name.equal then e'
          else closure_ren pre post e' )

let cnt = ref 0

let gensym () =
  cnt := !cnt + 1;
  "tmp" ^ string_of_int !cnt

let compile expr : Yarn.Prog.t =
  let externs = free_variables expr in
  let rec go (fns : (name * name * name list * name * Yarn.Expr.t) list ref) :
      Fiber.Expr.t -> Yarn.Expr.t = function
    | Trap -> Trap
    | Lit v -> Lit v
    | Var x -> Var x
    | Abs (r, x, _t, e) ->
        let closed = without (r :: x :: externs) (free_variables e) in
        let sym = gensym () |> Name.of_string in
        let knot = "knot_" ^ Name.to_string sym |> Name.of_string in
        let closure = (sym, knot, closed, x, go fns e |> closure_ren r knot) in
        fns := closure :: !fns;
        Closure (sym, closed)
    | Tuple es -> Tuple (List.map ~f:(go fns) es)
    | Untuple (xs, e, e') -> Untuple (xs, go fns e, go fns e')
    | App (Abs (r, x, _, e'), e)
      when List.mem (free_variables e') r ~equal:Name.equal ->
        Let (x, go fns e, go fns e')
    | App (e, e') -> App (go fns e, go fns e')
    (*
    | Proj (e, l) -> Proj (go fns e, l)
    | Tag (t, e) -> Tag (t, go fns e)
    | Match (e, x, t, e', e'') -> Match (go fns e, x, t, go fns e', go fns e'')
    *)
  in
  let fns = ref [] in
  let main = go fns expr in
  {
    defs =
      List.rev !fns
      |> List.map ~f:(fun (name, knot, closed, arg, body) ->
             Yarn.Prog.Closure.{ name; knot; closed; arg; body });
    externs;
    main;
  }

let%expect_test "compile" =
  let nm = Name.of_string in
  let var x = Fiber.Expr.Var (nm x) in
  let fn (x, t, e) = Fiber.Expr.Abs (nm "", nm x, t, e) in
  print_s
    [%sexp
      (compile
         (fn
            ( "x",
              Int,
              fn
                ( "xs",
                  Fun (Int, Int),
                  App (var "__add", Tuple [ var "x"; App (var "xs", Lit 0) ]) )
            ))
        : Yarn.Prog.t)];
  [%expect
    {|
    ((defs
      (((name tmp2) (knot knot_tmp2) (closed (x)) (arg xs)
        (body (App (Var __add) (Tuple ((Var x) (App (Var xs) (Lit 0)))))))
       ((name tmp1) (knot knot_tmp1) (closed ()) (arg x)
        (body (Closure tmp2 (x))))))
     (externs (__add)) (main (Closure tmp1 ())))
    |}];
  print_s
    [%sexp
      (compile
         (fn
            ( "s",
              Fun (Int, Int),
              Abs (nm "f", nm "y", Int, App (var "f", App (var "s", var "y")))
            ))
        : Yarn.Prog.t)];
  [%expect
    {|
    ((defs
      (((name tmp4) (knot knot_tmp4) (closed (s)) (arg y)
        (body (App (Var knot_tmp4) (App (Var s) (Var y)))))
       ((name tmp3) (knot knot_tmp3) (closed ()) (arg s)
        (body (Closure tmp4 (s))))))
     (externs ()) (main (Closure tmp3 ())))
    |}]
