open Core
open Binaryer
module Source = Lang.Fabric

let function_table = "function_table"
let sum = List.fold_left ~init:0 ~f:( + )

let size : Source.Repr.t -> int =
  let size_atom : Source.Repr.atom -> int = function
    | Int32 -> 4
    | Float64 -> 8
    | Box -> 4
  in
  function
  | Unknown -> failwith "value/type with unknown representation"
  | Atoms ts -> List.map ~f:size_atom ts |> sum

let repr : Source.Repr.t -> T.Type.t =
  let repr_atom : Source.Repr.atom -> T.Type.t = function
    | Int32 -> Type.int32
    | Float64 -> Type.float64
    | Box -> Type.int32
  in
  function
  | Unknown -> failwith "value/type with unknown representation"
  | Atoms ts -> List.map ~f:repr_atom ts |> Type.cat

let source_type_repr : Source.Type.t -> T.Type.t =
  Fn.compose repr Source.Type.repr

let source_expr_repr : Source.Expr.t -> T.Type.t =
  Fn.compose source_type_repr Source.Expr.type_expr

let source_pattern_repr : Source.Expr.pattern -> T.Type.t =
  Fn.compose source_type_repr Source.Expr.type_pattern

let assemble_expr (module Ctx : Context) ~top_alloc init_env closure_vars expr =
  let open Ctx in
  let i32 n = Const.i32 (Int32.of_int_exn n) in
  let rec go env (expr : Source.Expr.t) : T.Expression.t =
    let open Source.Expr in
    let alloc n =
      let last_alloc = local Type.int32 in
      Cell.
        ( Control.block
            [
              last_alloc := !top_alloc;
              (top_alloc := Operator.I32.(!top_alloc + i32 n));
            ],
          !last_alloc )
    in
    let var x = List.Assoc.find_exn env ~equal:String.equal x in
    match expr with
    | Fun (_, _) -> failwith "cannot assemble first-class functions"
    | Var (x, _) -> Cell.(!(var x))
    | Lit n -> i32 n
    | Let (Atom (x, t), e, e') ->
        let a = go env e in
        let v = local (source_type_repr t) in
        Control.block Cell.[ v := a; go ((x, v) :: env) e' ]
    | Op (e, "", e') ->
        let a = go env e and a' = go env e' in
        let k = addr ~size:4 ~offset:0 Type.int32 a |> Cell.( ! ) in
        let fv = Operator.I32.(a + i32 4) in
        let t, t' = Source.(Type.unwrap_function (Expr.type_expr e)) in
        (* FIXME: This assumes we only ever call closures so the second argument makes sense *)
        Function.call_indirect function_table k [ a'; fv ]
          (Type.cat [ source_type_repr t; Type.int32 ])
          (source_type_repr t')
    | Op (e, o, e') ->
        let op =
          match o with
          | "+" -> C.Expression.Operator.I32.add
          | "-" -> C.Expression.Operator.I32.sub
          | "*" -> C.Expression.Operator.I32.mul
          | "/" -> C.Expression.Operator.I32.div_s
          | _ -> raise_s [%message "no op for" (o : string)]
        in
        Operator.binary op (go env e) (go env e')
    | Closure (k, xs, _) ->
        let closure_size =
          List.map xs ~f:(fun (_, t) -> size (Source.Type.repr t)) |> sum
        in
        let allocs, p = alloc (4 + closure_size) in
        let at i = addr ~size:4 ~offset:(4 * i) Type.int32 p in
        Control.block
          Cell.(
            [ allocs; at 0 := i32 k ]
            @ List.mapi xs ~f:(fun i (x, _) -> at (i + 1) := !(var x))
            @ [ p ])
    | Intrinsic ("print", e) -> Function.call "print" [ go env e ] Type.none
    | Intrinsic ("print_i32", e) ->
        Function.call "print_i32" [ go env e ] Type.none
    | Intrinsic (f, _) -> failwith ("unimplemented: Intrinsic " ^ f)
    | Let _ -> failwith "unimplemented: non-Atom Let"
    | Tuple _ -> failwith "unimplemented: Tuple"
    | Array _ -> failwith "unimplemented: Array"
    | Idx _ -> failwith "unimplemented: Idx"
    | Shape _ -> failwith "unimplemented: Shape"
  in
  let init_closure, init_closure_env =
    if not (List.is_empty closure_vars) then
      let closure =
        Cell.(!(List.Assoc.find_exn init_env ~equal:String.equal "__closure"))
      in
      let _, closure_init =
        List.fold_map closure_vars ~init:0 ~f:(fun offset (x, t) ->
            let v = local (source_type_repr t) in
            ( offset + size (Source.Type.repr t),
              (Cell.(v := !(addr ~size:4 ~offset Type.int32 closure)), (x, v))
            ))
      in
      List.unzip closure_init
    else ([], [])
  in
  let e =
    Control.block (init_closure @ [ go (init_env @ init_closure_env) expr ])
  in
  e

let%expect_test "assemble_expr" =
  let (module Ctx) = context () in
  let open Ctx in
  Function.make ~name:"f" ~params:Type.none ~result:Type.int32 (fun _ ->
      "let x = 3 in let y = 4 in (x * x) + (y * y)" |> Syntax.parse_exn
      |> Compiler.propagate_types
      |> assemble_expr
           (module Ctx)
           ~top_alloc:
             (global "top_alloc" Type.int32 (Const.i32 (Int32.of_int_exn 0)))
           [] [])
  |> Function.export "f";
  print_s [%message (validate () : bool)];
  print ();
  [%expect
    {|
    ("validate ()" true)
    (module
     (type $0 (func (result i32)))
     (global $top_alloc (mut i32) (i32.const 0))
     (export "f" (func $f))
     (func $f (result i32)
      (local $0 i32)
      (local $1 i32)
      (block (result i32)
       (local.set $0
        (i32.const 3)
       )
       (block (result i32)
        (local.set $1
         (i32.const 4)
        )
        (i32.add
         (i32.mul
          (local.get $0)
          (local.get $0)
         )
         (i32.mul
          (local.get $1)
          (local.get $1)
         )
        )
       )
      )
     )
    )
    |}]

let assemble_function (module Ctx : Context) ~closure ~top_alloc name (fv, p, e)
    =
  let open Ctx in
  let xs = Compiler.pattern_vars p |> List.map ~f:fst in
  let params = source_pattern_repr p in
  Function.make ~name
    ~params:(if closure then Type.cat [ params; Type.int32 ] else params)
    ~result:(source_expr_repr e)
    (fun args ->
      assemble_expr
        (module Ctx)
        ~top_alloc
        (List.zip_exn (if closure then xs @ [ "__closure" ] else xs) args)
        fv e)

let assemble Source.Prog.{ functions; main } : T.Module.t =
  let (module Ctx) = context () in
  let open Ctx in
  feature C.Features.reference_types;
  feature C.Features.gc;
  let top_alloc =
    global "top_alloc" Type.int32 (Const.i32 (Int32.of_int_exn 420))
  in
  (* FIXME: Memory limits >:( *)
  Memory.set ~initial:10 ~maximum:10 ();
  let funs =
    List.mapi functions ~f:(fun i (fv, p, e) ->
        assemble_function
          (module Ctx)
          ~closure:true ~top_alloc
          ("_f" ^ string_of_int i)
          (fv, p, e))
  in
  let main =
    assemble_function
      (module Ctx)
      ~closure:false ~top_alloc "main" ([], List [], main)
  in
  let () =
    let n = List.length funs in
    let tab = Table.make ~initial:n ~maximum:n Type.funcref function_table in
    Table.add "init_function_table" tab funs |> ignore
  in
  Function.start main;
  Function.export "main" main;
  (* Import.add_function_import md "print" "spectest" "print" Type.none Type.none; *)
  Function.import "print_i32" "spectest" "print_i32" Type.int32 Type.none;
  me

let%expect_test "assemble" =
  let (module Ctx) =
    Binaryer.context_of_module
      ("let a = 1 in let b = 2 in let f = (x: int => (x*b)+a) in %print_i32 (f \
        3)" |> Syntax.parse_exn |> Compiler.propagate_types
     |> Compiler.lift_lambdas |> assemble)
  in
  let open Ctx in
  let valid = validate () in
  print_s [%message (valid : bool)];
  interpret ();
  print ();
  [%expect
    {|
    (valid true)
    7 : i32
    (module
     (type $0 (func (param i32 i32) (result i32)))
     (type $1 (func))
     (type $2 (func (param i32)))
     (import "spectest" "print_i32" (func $print_i32 (type $2) (param i32)))
     (global $top_alloc (mut i32) (i32.const 420))
     (memory $__memory__ 10 10)
     (table $function_table 1 1 funcref)
     (elem $init_function_table (i32.const 0) $_f0)
     (export "main" (func $main))
     (start $main)
     (func $_f0 (type $0) (param $0 i32) (param $1 i32) (result i32)
      (local $2 i32)
      (local $3 i32)
      (local.set $2
       (i32.load
        (local.get $1)
       )
      )
      (local.set $3
       (i32.load offset=4
        (local.get $1)
       )
      )
      (i32.add
       (i32.mul
        (local.get $0)
        (local.get $3)
       )
       (local.get $2)
      )
     )
     (func $main (type $1)
      (local $0 i32)
      (local $1 i32)
      (local $2 i32)
      (local $3 i32)
      (block
       (local.set $0
        (i32.const 1)
       )
       (block
        (local.set $1
         (i32.const 2)
        )
        (block
         (local.set $3
          (block (result i32)
           (block
            (local.set $2
             (global.get $top_alloc)
            )
            (global.set $top_alloc
             (i32.add
              (global.get $top_alloc)
              (i32.const 12)
             )
            )
           )
           (i32.store
            (local.get $2)
            (i32.const 0)
           )
           (i32.store offset=4
            (local.get $2)
            (local.get $0)
           )
           (i32.store offset=8
            (local.get $2)
            (local.get $1)
           )
           (local.get $2)
          )
         )
         (call $print_i32
          (call_indirect $function_table (type $0)
           (i32.const 3)
           (i32.add
            (local.get $3)
            (i32.const 4)
           )
           (i32.load
            (local.get $3)
           )
          )
         )
        )
       )
      )
     )
    )
    |}]
