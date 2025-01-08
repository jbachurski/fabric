open Binaryen
open Core
module Source = Lang.Fabric

let function_table = "function_table"

let gensym =
  let cnt = ref 0 in
  fun base ->
    cnt := !cnt + 1;
    base ^ string_of_int !cnt

let%expect_test "example" =
  let wasm_mod = Module.create () in
  let x = Expression.Local_get.make wasm_mod 0 Type.int32 in
  let y = Expression.Local_get.make wasm_mod 1 Type.int32 in
  let add = Expression.Binary.make wasm_mod Op.add_int32 x y in
  let adder =
    Function.add_function wasm_mod "adder"
      (Type.create [| Type.int32; Type.int32 |])
      Type.int32 [||] add
  in
  ignore adder;
  Module.print wasm_mod;
  print_s [%message (Module.validate wasm_mod : int)];
  Module.dispose wasm_mod;
  [%expect
    {|
    ("Module.validate wasm_mod" 1)
    (module
     (type $i32_i32_=>_i32 (func (param i32 i32) (result i32)))
     (func $adder (param $0 i32) (param $1 i32) (result i32)
      (i32.add
       (local.get $0)
       (local.get $1)
      )
     )
    )
    |}]

let sum = List.fold_left ~init:0 ~f:( + )

let rec size : Source.Repr.t -> int =
  let size_atom : Source.Repr.atom -> int = function
    | Int32 -> 4
    | Float64 -> 8
    | Box -> 4
  in
  function
  | Unknown -> failwith "value/type with unknown representation"
  | Atoms ts -> List.map ~f:size_atom ts |> sum

let rec repr : Source.Repr.t -> Type.t =
  let repr_atom : Source.Repr.atom -> Type.t = function
    | Int32 -> Type.int32
    | Float64 -> Type.float64
    | Box -> Type.int32
  in
  function
  | Unknown -> failwith "value/type with unknown representation"
  | Atoms ts -> Type.create (List.map ~f:repr_atom ts |> Array.of_list)

let source_type_repr : Source.Type.t -> Type.t =
  Fn.compose repr Source.Type.repr

let source_expr_repr : Source.Expr.t -> Type.t =
  Fn.compose source_type_repr Source.Expr.type_expr

let source_pattern_repr : Source.Expr.pattern -> Type.t =
  Fn.compose source_type_repr Source.Expr.type_pattern

let var md env (x, t) =
  Expression.Local_get.make md
    (List.Assoc.find_exn env ~equal:String.equal x)
    (source_type_repr t)

let lit md n = Expression.Const.make md (Literal.int32 (Int32.of_int_exn n))

let assemble_expr md locals closure_vars expr =
  let slots = ref [] in
  let init_env = List.mapi locals ~f:(fun i (x, _) -> (x, i)) in
  let push_slot t =
    let i = List.length !slots in
    slots := source_type_repr t :: !slots;
    List.length init_env + i
  in
  let rec go env (expr : Source.Expr.t) : Expression.t =
    let open Source.Expr in
    let var = var md env in
    let lit = lit md in
    let alloc n =
      let set_alloc =
        Expression.Global_get.make md "top_alloc" Type.int32
        |> Expression.Global_set.make md "last_alloc"
      in
      let ret = Expression.Global_get.make md "last_alloc" Type.int32 in
      ( Expression.Block.make md (gensym "alloc")
          [
            set_alloc;
            Expression.Global_set.make md "top_alloc"
              (Expression.Binary.make md Op.add_int32 ret (lit n));
          ],
        ret )
    in
    match expr with
    | Fun (_, _) -> failwith "cannot assemble first-class functions"
    | Var (x, t) -> var (x, t)
    | Lit n -> lit n
    | Let (Atom (x, t), e, e') ->
        let a = go env e in
        let i = push_slot t in
        Expression.Block.make md (gensym "let")
          [ Expression.Local_set.make md i a; go ((x, i) :: env) e' ]
    | Op (e, "", e') ->
        let a = go env e and a' = go env e' in
        let k = Expression.Load.make md 4 0 0 Type.int32 a "memory" in
        let fv = Expression.Binary.make md Op.add_int32 a (lit 4) in
        let t, t' = Source.(Type.unwrap_function (Expr.type_expr e)) in
        (* FIXME: This assumes we only ever call closures so the second argument makes sense *)
        Expression.Call_indirect.make md function_table k [ a'; fv ]
          (Type.create [| source_type_repr t; Type.int32 |])
          (source_type_repr t')
    | Op (e, o, e') ->
        let op =
          match o with
          | "+" -> Op.add_int32
          | "-" -> Op.sub_int32
          | "*" -> Op.mul_int32
          | "/" -> Op.div_s_int32
          | "+." -> Op.add_float64
          | "-." -> Op.sub_float64
          | "*." -> Op.mul_float64
          | "/." -> Op.div_float64
          | _ -> raise_s [%message "no op for" (o : string)]
        in
        Expression.Binary.make md op (go env e) (go env e')
    | Closure (k, xs, t) ->
        let closure_size =
          List.map xs ~f:(fun (_, t) -> size (Source.Type.repr t)) |> sum
        in
        let allocs, p = alloc (4 + closure_size) in
        Expression.Block.make md (gensym "closure")
          ([
             allocs;
             Expression.Store.make md 4 0 0 p (lit k) Type.int32 "memory";
           ]
          @ List.mapi xs ~f:(fun i (x, t) ->
                Expression.Store.make md 4
                  (4 + (4 * i))
                  0 p
                  (var (x, t))
                  Type.int32 "memory")
          @ [ p ])
    | Intrinsic ("print", e) ->
        Expression.Call.make md "print" [ go env e ] Type.none
    | Intrinsic ("print_i32", e) ->
        Expression.Call.make md "print_i32" [ go env e ] Type.none
    | Intrinsic (f, _) -> failwith ("unimplemented: Intrinsic " ^ f)
    | Let _ -> failwith "unimplemented: non-Atom Let"
    | Tuple _ -> failwith "unimplemented: Tuple"
    | Array _ -> failwith "unimplemented: Array"
    | Idx _ -> failwith "unimplemented: Idx"
    | Shape _ -> failwith "unimplemented: Shape"
  in
  let init_closure, init_closure_env =
    if not (List.is_empty closure_vars) then
      let closure = var md init_env ("__closure", Int) in
      let _, closure_init =
        List.fold_map closure_vars ~init:0 ~f:(fun offset (x, t) ->
            let i = push_slot t in
            ( offset + size (Source.Type.repr t),
              ( Expression.Load.make md 4 offset 0 Type.int32 closure "memory"
                |> Expression.Local_set.make md i,
                (x, i) ) ))
      in
      List.unzip closure_init
    else ([], [])
  in
  let e =
    Expression.Block.make md (gensym "init_closure")
      (init_closure @ [ go (init_env @ init_closure_env) expr ])
  in
  (e, List.rev !slots |> Array.of_list)

let%expect_test "assemble_expr" =
  let md = Module.create () in
  let e, slots =
    "let x = 3 in let y = 4 in (x * x) + (y * y)" |> Syntax.parse_exn
    |> Compiler.propagate_types |> assemble_expr md [] []
  in
  Function.add_function md "f" Type.none Type.int32 slots e |> ignore;
  Export.add_function_export md "f" "f" |> ignore;
  print_s [%message (Module.validate md : int)];
  Module.print_stack_ir md true;
  Module.dispose md;
  [%expect
    {|
    ("Module.validate md" 1)
    (module
     (type $none_=>_i32 (func (result i32)))
     (export "f" (func $f))
     (func $f (result i32)
      (local $0 i32)
      (local $1 i32)
      i32.const 3
      local.set $0
      i32.const 4
      local.set $1
      local.get $0
      local.get $0
      i32.mul
      local.get $1
      local.get $1
      i32.mul
      i32.add
     )
    )
    |}]

let assemble_function ~closure md name (fv, p, e) =
  let xs = Compiler.pattern_vars p in
  let e', slots =
    assemble_expr md (if closure then xs @ [ ("__closure", Int) ] else xs) fv e
  in
  let param_repr = source_pattern_repr p in
  Function.add_function md name
    (if closure then Type.create [| param_repr; Type.int32 |] else param_repr)
    (source_expr_repr e) slots e'

let assemble Source.Prog.{ functions; main } =
  let md = Module.create () in
  Global.add_global md "last_alloc" Type.int32 true (lit md 420) |> ignore;
  Global.add_global md "top_alloc" Type.int32 true (lit md 420) |> ignore;
  (* FIXME: Memory limits >:( *)
  Memory.set_memory md 10 10 "memory" [] false false "memory";
  let funs = List.length functions in
  let _tab = Table.add_table md function_table funs funs Type.funcref in
  List.iteri functions ~f:(fun i (fv, p, e) ->
      assemble_function ~closure:true md ("_f" ^ string_of_int i) (fv, p, e)
      |> ignore);
  assemble_function ~closure:false md "main" ([], List [], main)
  |> Function.set_start md;
  Export.add_function_export md "main" "main" |> ignore;
  (* Import.add_function_import md "print" "spectest" "print" Type.none Type.none; *)
  Import.add_function_import md "print_i32" "spectest" "print_i32" Type.int32
    Type.none;
  Table.add_active_element_segment md function_table "init_function_table"
    (List.init funs ~f:(fun i -> "_f" ^ string_of_int i))
    (lit md 0)
  |> ignore;
  md

let%expect_test "assemble" =
  let test s f =
    let md =
      s |> Syntax.parse_exn |> Compiler.propagate_types |> Compiler.lift_lambdas
      |> assemble
    in
    let valid = Module.validate md > 0 in
    print_s [%message (valid : bool)];
    if not valid then Module.print md else f md;
    Module.dispose md
  in
  test "let id = (x: int => x) in %print_i32 (id 42)" (fun md ->
      Module.interpret md);
  [%expect {|
    (valid true)
    42 : i32
    |}];
  test "let square = (x: int => x * x) in %print_i32 ((square 3) + (square 4))"
    (fun md -> Module.interpret md);
  [%expect {|
    (valid true)
    25 : i32
    |}];
  test
    "let a = 1 in let b = 2 in let f = (x: int => (x*b)+a) in %print_i32 (f 3)"
    (fun md ->
      (* FIXME: This also breaks with optimization. _Why_? *)
      Module.interpret md);
  [%expect {|
    (valid true)
    7 : i32
    |}];
  (* FIXME: Exchanging the order of this composition causes a crash in [optimize]. Seriously? *)
  test
    "let g = (x: int => 2*x) in let f = (x: int => x+1) in %print_i32 (f (g 1))"
    (fun md ->
      (* Module.print md; *)
      Module.optimize md;
      Module.print_stack_ir md true;
      Module.interpret md);
  [%expect
    {|
    (valid true)
    (module
     (type $i32_i32_=>_i32 (func (param i32 i32) (result i32)))
     (type $none_=>_none (func))
     (type $i32_=>_none (func (param i32)))
     (import "spectest" "print_i32" (func $print_i32 (param i32)))
     (global $last_alloc (mut i32) (i32.const 420))
     (global $top_alloc (mut i32) (i32.const 420))
     (memory $memory 10 10)
     (table $function_table 2 2 funcref)
     (elem $init_function_table (i32.const 0) $_f0 $_f1)
     (export "memory" (memory $memory))
     (export "main" (func $main))
     (start $main)
     (func $_f0 (param $0 i32) (param $1 i32) (result i32)
      local.get $0
      i32.const 1
      i32.add
     )
     (func $_f1 (param $0 i32) (param $1 i32) (result i32)
      local.get $0
      i32.const 1
      i32.shl
     )
     (func $main
      (local $0 i32)
      (local $1 i32)
      global.get $top_alloc
      global.set $last_alloc
      global.get $last_alloc
      i32.const 4
      i32.add
      global.set $top_alloc
      global.get $last_alloc
      i32.const 1
      i32.store $memory
      global.get $last_alloc
      local.set $0
      global.get $top_alloc
      global.set $last_alloc
      global.get $last_alloc
      i32.const 4
      i32.add
      global.set $top_alloc
      global.get $last_alloc
      i32.const 0
      i32.store $memory
      global.get $last_alloc
      local.set $1
      i32.const 1
      local.get $0
      i32.const 4
      i32.add
      local.get $0
      i32.load $memory
      call_indirect $function_table (type $i32_i32_=>_i32)
      local.get $1
      i32.const 4
      i32.add
      local.get $1
      i32.load $memory
      call_indirect $function_table (type $i32_i32_=>_i32)
      call $print_i32
     )
    )
    3 : i32
    |}]
