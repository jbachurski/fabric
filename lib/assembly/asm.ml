open Binaryen
open Core

module Expr = struct
  type t =
    | Var of string
    | Lit of int
    | Let of string * t * t
    | Op of t * string * t
  [@@deriving sexp]
end

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

let assemble md slots expr =
  let rec go env (expr : Expr.t) : Expression.t =
    match expr with
    | Var x ->
        Expression.Local_get.make md
          (List.Assoc.find_exn env ~equal:String.equal x)
          Type.int32
    | Lit n -> Expression.Const.make md (Literal.int32 (Int32.of_int_exn n))
    | Let (x, e, e') ->
        let a = go env e in
        slots := Type.int32 :: !slots;
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
          | _ -> raise_s [%message "no op for" (o : string)]
        in
        Expression.Binary.make md op (go env e) (go env e')
  in
  go [] expr

let%expect_test "" =
  let md = Module.create () in
  let slots = ref [] in
  let e =
    assemble md slots
      (Let
         ( "x",
           Lit 3,
           Let
             ( "y",
               Lit 4,
               Op (Op (Var "x", "*", Var "x"), "+", Op (Var "y", "*", Var "y"))
             ) ))
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
