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

  let feature feat =
    C.Module.Features.set me
      (Unsigned.UInt32.logor (C.Module.Features.get me) (feat ()))

  let validate () = C.Module.validate me <> 0
  let interpret () = C.Module.interpret me
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

  module Struct = struct
    type t = { struct_type : T.HeapType.t; fields : (string * T.Type.t) list }

    let t fields =
      {
        fields = List.map fields ~f:(fun (name, { t; _ }) -> (name, t));
        struct_type = Type.struct_ (List.map ~f:snd fields);
      }

    let make { struct_type; fields } inits =
      let inits' =
        List.map fields ~f:(fun (name, _) ->
            List.Assoc.find_exn inits ~equal:String.equal name)
      in
      let inits_start, inits_len = c_args T.Expression.t inits' in
      C.Expression.struct_new M.me inits_start inits_len struct_type

    let cell { struct_type = _; fields } target name =
      let i, (_, typ) =
        List.findi_exn fields ~f:(fun _ (name', _) -> String.(name = name'))
      in
      Cell.{ typ; loc = Struct { target; field_idx = u32_of_int i } }
  end

  module Array = struct
    type t = { array_type : T.HeapType.t; elem_type : T.Type.t }

    let t field = { array_type = Type.array field; elem_type = field.t }

    let make { array_type; _ } ~init size =
      C.Expression.array_new M.me array_type size init

    let cell { array_type = _; elem_type = typ } target idx =
      Cell.{ typ; loc = Array { target; idx } }
  end
end

let context_of_module me =
  (module Make (struct
    let me = me
  end) : Context)

let context () =
  let t = C.Module.create () in
  Gc.Expert.add_finalizer_exn t (fun md -> C.Module.dispose md);
  context_of_module t
