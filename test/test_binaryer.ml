open Core
open Binaryer

let%expect_test "empty module" =
  let md = C.Module.create () in
  C.Module.print md;
  C.Module.dispose md;
  [%expect {|
    (module
    )
    |}]

let%expect_test "context" =
  let (module Ctx) = context () in
  Ctx.print ();
  [%expect {|
    (module
    )
    |}]

let take2 = function
  | [ x; y ] -> (x, y)
  | l -> raise_s [%message "take2" (List.length l : int)]

let take3 = function
  | [ x; y; z ] -> (x, y, z)
  | l -> raise_s [%message "take3" (List.length l : int)]

let%expect_test "basic" =
  let (module Ctx) = context () in
  let open Ctx in
  Function.make ~name:"test"
    ~params:(Type.cat [ Type.int32; Type.int32 ])
    ~result:Type.int32
    (fun args ->
      let a, b = take2 args in
      Operator.I32.(
        Cell.((!a * !a) + (!b * !b) + (Int32.of_int_exn 1 |> Const.i32))))
  |> Function.export "test";
  assert (validate ());
  optimize ();
  print_stack_ir ();
  [%expect
    {|
    (module
     (type $0 (func (param i32 i32) (result i32)))
     (export "test" (func $test))
     (func $test (param $0 i32) (param $1 i32) (result i32)
      local.get $0
      local.get $0
      i32.mul
      local.get $1
      local.get $1
      i32.mul
      i32.add
      i32.const 1
      i32.add
     )
    )
    |}]

let%expect_test "cats" =
  (* TODO: printing types *)
  let look_at x = x |> Sys.opaque_identity |> ignore in
  look_at Type.int32;
  look_at (Type.cat [ Type.int32 ]);
  look_at (Type.cat [ Type.int32; Type.int32 ]);
  look_at (Type.cat [ Type.cat [ Type.int32 ] ]);
  look_at
    (Type.cat
       [
         Type.cat [ Type.int32; Type.int32 ];
         Type.cat [ Type.int32; Type.int32 ];
       ])

let%expect_test "locals" =
  let (module Ctx) = context () in
  let open Ctx in
  Function.make ~name:"test"
    ~params:(Type.cat [ Type.int32; Type.int32 ])
    ~result:Type.int32
    (fun args ->
      let open Cell in
      let a, b = take2 args in
      let r = local Type.int32 in
      Control.block
        Operator.I32.
          [
            a := !a + (!b + !b);
            b := !b + (!a + !a + !a);
            a := !a + !b;
            r := !a;
            !r;
          ])
  |> Function.export "test";
  assert (validate ());
  print ();
  [%expect
    {|
    (module
     (type $0 (func (param i32 i32) (result i32)))
     (export "test" (func $test))
     (func $test (param $0 i32) (param $1 i32) (result i32)
      (local $2 i32)
      (local.set $0
       (i32.add
        (local.get $0)
        (i32.add
         (local.get $1)
         (local.get $1)
        )
       )
      )
      (local.set $1
       (i32.add
        (local.get $1)
        (i32.add
         (i32.add
          (local.get $0)
          (local.get $0)
         )
         (local.get $0)
        )
       )
      )
      (local.set $0
       (i32.add
        (local.get $0)
        (local.get $1)
       )
      )
      (local.set $2
       (local.get $0)
      )
      (local.get $2)
     )
    )
    |}]

let%expect_test "print" =
  let (module Ctx) = context () in
  let open Ctx in
  feature C.Features.reference_types;
  feature C.Features.gc;
  Memory.set ~initial:10 ~maximum:10 ();
  Function.import "print_i32" "spectest" "print_i32" Type.int32 Type.none;
  Function.import "print_i32_i32" "spectest" "print"
    (Type.cat [ Type.int32; Type.int32 ])
    Type.none;
  let main =
    Function.make ~params:Type.none ~result:Type.none (fun _ ->
        Control.block
          Const.
            [
              Function.call "print_i32" [ i32' 1 ] Type.none;
              Function.call "print_i32_i32" [ i32' 2; i32' 3 ] Type.none;
            ])
  in
  Function.export "main" main;
  Function.start main;
  assert (validate ());
  interpret ();
  print ();
  [%expect
    {|
    1 : i32
    2 : i32
    3 : i32
    (module
     (type $0 (func (param i32)))
     (type $1 (func (param i32 i32)))
     (type $2 (func))
     (import "spectest" "print_i32" (func $print_i32 (type $0) (param i32)))
     (import "spectest" "print" (func $print_i32_i32 (type $1) (param i32 i32)))
     (memory $__memory__ 10 10)
     (export "main" (func $__fun1))
     (start $__fun1)
     (func $__fun1 (type $2)
      (call $print_i32
       (i32.const 1)
      )
      (call $print_i32_i32
       (i32.const 2)
       (i32.const 3)
      )
     )
    )
    |}]

let%expect_test "memory" =
  let (module Ctx) = context () in
  let open Ctx in
  Memory.set ~initial:10 ~maximum:10 ();
  Function.make ~params:Type.none ~result:Type.int32 (fun _ ->
      Const.i32 (Int32.of_int_exn 42))
  |> Function.export "test";
  assert (validate ());
  print ();
  [%expect
    {|
    (module
     (type $0 (func (result i32)))
     (memory $__memory__ 10 10)
     (export "test" (func $__fun1))
     (func $__fun1 (result i32)
      (i32.const 42)
     )
    )
    |}]

let%expect_test "struct" =
  let (module Ctx) = context () in
  let open Ctx in
  feature C.Features.reference_types;
  feature C.Features.gc;
  Memory.set ~initial:10 ~maximum:10 ();
  Function.import "print_i32" "spectest" "print_i32" Type.int32 Type.none;
  let main =
    Function.make ~params:Type.none ~result:Type.none (fun _ ->
        let open Struct in
        let open Cell in
        let foobar_t =
          t Type.[ ("foo", field ~mut:true int32); ("bar", field int32) ]
        in
        let q = local (Type.of_heap_type foobar_t.struct_type) in
        let q_foo = cell foobar_t !q "foo" in
        let q_bar = cell foobar_t !q "bar" in
        Control.block
          Cell.
            [
              q :=
                make foobar_t
                  [ ("foo", Const.i32' 42); ("bar", Const.i32' (1337 - 42)) ];
              (q_foo := Operator.I32.(!q_foo + !q_bar));
              Function.call "print_i32" [ !q_foo ] Type.none;
            ])
  in
  Function.export "main" main;
  Function.start main;
  assert (validate ());
  interpret ();
  print ();
  [%expect
    {|
    1337 : i32
    (module
     (type $0 (struct (field (mut i32)) (field i32)))
     (type $1 (func (param i32)))
     (type $2 (func))
     (import "spectest" "print_i32" (func $print_i32 (type $1) (param i32)))
     (memory $__memory__ 10 10)
     (export "main" (func $__fun1))
     (start $__fun1)
     (func $__fun1 (type $2)
      (local $0 (ref $0))
      (local.set $0
       (struct.new $0
        (i32.const 42)
        (i32.const 1295)
       )
      )
      (struct.set $0 0
       (local.get $0)
       (i32.add
        (struct.get $0 0
         (local.get $0)
        )
        (struct.get $0 1
         (local.get $0)
        )
       )
      )
      (call $print_i32
       (struct.get $0 0
        (local.get $0)
       )
      )
     )
    )
    |}]
