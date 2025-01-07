open Binaryen
open Core
module Source = Lang.Fabric

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

let rec of_source_type : Source.Type.t -> Type.t = function
  | Any -> failwith "cannot access type Any"
  | Int -> Type.int32
  | Float -> Type.float64
  | Tuple ts -> Type.create (List.map ~f:of_source_type ts |> Array.of_list)
  | Function (_, _) -> Type.int32
  | Array _ -> Type.int32

let lit md n = Expression.Const.make md (Literal.int32 (Int32.of_int_exn n))

let assemble_expr md fv expr =
  let slots = ref [] in
  let push_slot t =
    let i = List.length !slots in
    slots := of_source_type t :: !slots;
    i
  in
  let rec go env (expr : Source.Expr.t) : Expression.t =
    let open Source.Expr in
    let var (x, t) =
      Expression.Local_get.make md
        (List.Assoc.find_exn env ~equal:String.equal x)
        (of_source_type t)
    in
    match expr with
    | Fun (_, _) -> failwith "cannot assemble first-class functions"
    | Var (x, t) -> var (x, t)
    | Lit n -> lit md n
    | Let (Atom (x, t), e, e') ->
        let a = go env e in
        let i = push_slot t in
        Expression.Block.make md (gensym "let")
          [ Expression.Local_set.make md i a; go ((x, i) :: env) e' ]
    | Op (e, "", e') ->
        let a = go env e and a' = go env e' in
        let t, t' = Source.(Type.unwrap_function (Expr.type_expr e)) in
        Expression.Call_indirect.make md "f" a [ a' ] (of_source_type t)
          (of_source_type t')
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
        assert (List.is_empty xs);
        lit md k
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
  let env = List.map fv ~f:(fun (x, t) -> (x, push_slot t)) in
  (go env expr, slots)

let%expect_test "assemble_expr" =
  let md = Module.create () in
  let e, slots =
    "let x = 3 in let y = 4 in (x * x) + (y * y)" |> Syntax.parse_exn
    |> Compiler.propagate_types |> assemble_expr md []
  in
  Function.add_function md "f" Type.none Type.int32 (Array.of_list !slots) e
  |> ignore;
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

let assemble_function md name (fv, p, e) =
  let xs = Compiler.pattern_vars p in
  let e', slots = assemble_expr md xs e in
  Function.add_function md name
    (of_source_type (Source.Expr.type_pattern p))
    (of_source_type (Source.Expr.type_expr e))
    (Array.of_list !slots) e'

let assemble Source.Prog.{ functions; main } =
  let md = Module.create () in
  let funs = List.length functions in
  let _tab = Table.add_table md "f" funs funs Type.funcref in
  List.iteri functions ~f:(fun i (fv, p, e) ->
      assemble_function md ("_f" ^ string_of_int i) (fv, p, e) |> ignore);
  assemble_function md "main" ([], List [], main) |> Function.set_start md;
  Export.add_function_export md "main" "main" |> ignore;
  Import.add_function_import md "print_i32" "spectest" "print_i32" Type.int32
    Type.none;
  Table.add_active_element_segment md "f" "elem"
    (List.init funs ~f:(fun i -> "_f" ^ string_of_int i))
    (lit md 0)
  |> ignore;
  md

let%expect_test "assemble" =
  let md =
    "let f = (x: int => 2 * x) in let g = (x: int => x + 1) in %print_i32 (f \
     (g 1))" |> Syntax.parse_exn |> Compiler.propagate_types
    |> Compiler.lift_lambdas |> assemble
  in
  print_s [%message (Module.validate md : int)];
  Module.print_stack_ir md true;
  Module.interpret md;
  Module.dispose md;
  [%expect
    {|
    ("Module.validate md" 1)
    (module
     (type $i32_=>_i32 (func (param i32) (result i32)))
     (type $none_=>_none (func))
     (type $i32_=>_none (func (param i32)))
     (import "spectest" "print_i32" (func $print_i32 (param i32)))
     (table $f 2 2 funcref)
     (elem $elem (i32.const 0) $_f0 $_f1)
     (export "main" (func $main))
     (start $main)
     (func $_f0 (param $0 i32) (result i32)
      (local $1 i32)
      local.get $0
      i32.const 1
      i32.add
     )
     (func $_f1 (param $0 i32) (result i32)
      (local $1 i32)
      i32.const 2
      local.get $0
      i32.mul
     )
     (func $main
      (local $0 i32)
      (local $1 i32)
      i32.const 1
      local.set $0
      i32.const 0
      local.set $1
      i32.const 1
      local.get $1
      call_indirect $f (type $i32_=>_i32)
      local.get $0
      call_indirect $f (type $i32_=>_i32)
      call $print_i32
     )
    )
    4 : i32
    |}]
