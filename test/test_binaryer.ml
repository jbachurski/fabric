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
      Operator.I32.(Local.((!a * !a) + (!b * !b))))
  |> Function.export "test";
  assert (validate ());
  optimize ();
  print_stack_ir ();
  [%expect
    {|
    (module
     (type $i32_i32_=>_i32 (func (param i32 i32) (result i32)))
     (export "test" (func $test))
     (func $test (param $0 i32) (param $1 i32) (result i32)
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
      let open Local in
      let a, b = take2 args in
      let r = new_local Type.int32 in
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
     (type $i32_i32_=>_i32 (func (param i32 i32) (result i32)))
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
