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
  | Function (_, _) -> Type.funcref
  | Array _ -> Type.arrayref

let assemble md slots expr =
  let rec go env (expr : Source.Expr.t) : Expression.t =
    let open Source.Expr in
    match expr with
    | Fun (_, _) -> failwith "cannot assemble first-class functions"
    | Var (x, t) ->
        Expression.Local_get.make md
          (List.Assoc.find_exn env ~equal:String.equal x)
          Type.int32
    | Lit n -> Expression.Const.make md (Literal.int32 (Int32.of_int_exn n))
    | Let (Atom (x, t), e, e') ->
        let a = go env e in
        slots := of_source_type t :: !slots;
        let i = List.length env in
        Expression.Block.make md (gensym "let")
          [ Expression.Local_set.make md i a; go ((x, i) :: env) e' ]
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
    | Let _ -> failwith "unimplemented: non-Atom Let"
    | Tuple _ -> failwith "unimplemented: Tuple"
    | Array _ -> failwith "unimplemented: Array"
    | Idx _ -> failwith "unimplemented: Idx"
    | Shape _ -> failwith "unimplemented: Shape"
    | Closure _ -> failwith "unimplemented: Closure"
  in
  go [] expr

let%expect_test "" =
  let md = Module.create () in
  let slots = ref [] in
  let e =
    assemble md slots
      (Let
         ( Atom ("x", Int),
           Lit 3,
           Let
             ( Atom ("y", Int),
               Lit 4,
               Op
                 ( Op (Var ("x", Int), "*", Var ("x", Int)),
                   "+",
                   Op (Var ("y", Int), "*", Var ("y", Int)) ) ) ))
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
