open Core
include Common

module type Context = Binaryer_intf.Context

type expr = T.Expression.t

module Type = Type

module Make (M : sig
  val me : T.Module.t
end) =
struct
  let me = M.me
  let validate () = C.Module.validate me <> 0
  let optimize () = C.Module.optimize me
  let print () = C.Module.print me
  let print_stack_ir () = C.Module.print_stack_ir me
  let print_asm_js () = C.Module.print_asm_js me

  module Const = Const.Make (M)
  module Operator = Operator.Make (M)
  module Cell = Cell.Make (M)
  module Control = Control.Make (M)
  module Function = Function.Make (M)
  module Table = Table.Make (M)
  module Memory = Memory.Make (M)

  let addr = Cell.addr

  let global ?(mut = true) name typ expr =
    let handle = C.Global.add me name typ mut expr in
    Cell.{ typ; loc = Global { name; mut; handle } }

  let local = Function.local
end

let context_of_module me =
  (module Make (struct
    let me = me
  end) : Context)

let context () =
  let t = C.Module.create () in
  Gc.Expert.add_finalizer_exn t (fun md -> C.Module.dispose md);
  context_of_module t
