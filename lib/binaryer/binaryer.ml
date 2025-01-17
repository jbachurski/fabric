open Core
open Binaryer_intf
module C = Binaryen_ctypes.Functions
module T = Binaryen_ctypes.Types

module type Context = Context

type expr = T.Expression.t

let int_of_u32 = Unsigned.UInt32.to_int
let u32_of_int = Unsigned.UInt32.of_int

let c_args t xs =
  let open Ctypes.CArray in
  let a = of_list t xs in
  (start a, length a |> u32_of_int)

let default_memory = "__memory__"

module Type = struct
  let none = C.Type.none ()
  let int32 = C.Type.int32 ()
  let int64 = C.Type.int64 ()
  let float32 = C.Type.float32 ()
  let float64 = C.Type.float64 ()
  let funcref = C.Type.funcref ()
  let unreachable = C.Type.unreachable ()
  let auto = C.Type.auto ()
  let arity t = C.Type.arity t |> int_of_u32

  let expanded t =
    let open Ctypes.CArray in
    let ts = make T.Type.t (arity t) in
    C.Type.expand t (start ts);
    to_list ts

  let cat ts =
    let ts = List.map ts ~f:expanded |> List.concat in
    let ts_start, ts_len = c_args T.Type.t ts in
    C.Type.tuple ts_start ts_len
end

module MakeContext (M : sig
  val t : T.Module.t
end) =
struct
  let me = M.t
  let validate () = C.Module.validate me <> 0
  let optimize () = C.Module.optimize me
  let print () = C.Module.print me
  let print_stack_ir () = C.Module.print_stack_ir me
  let print_asm_js () = C.Module.print_asm_js me

  module Const = struct
    let i32 x = C.Expression.const me (C.Literal.int32 x)
  end

  module Operator = struct
    let unary op = C.Expression.unary me (op ())
    let binary op = C.Expression.binary me (op ())

    module I32 = struct
      let ( + ) = binary C.Expression.Operator.I32.add
      let ( - ) = binary C.Expression.Operator.I32.sub
      let ( * ) = binary C.Expression.Operator.I32.mul
      let ( / ) = binary C.Expression.Operator.I32.div_s
    end
  end

  module Cell = struct
    open Cell0

    type uint32 = Unsigned.UInt32.t
    type nonrec t = t

    let addr ~size ~offset ?(align = 0) ?(mem = default_memory) typ addr =
      {
        typ;
        loc =
          Address
            {
              addr;
              size = u32_of_int size;
              offset = u32_of_int offset;
              align = u32_of_int align;
              mem;
            };
      }

    let ( ! ) { typ; loc } =
      match loc with
      | Local { idx } -> C.Expression.local_get me idx typ
      | Global { name; _ } -> C.Expression.global_get me name typ
      | Address { addr; size; offset; align; mem } ->
          C.Expression.load me size false offset align typ addr mem

    let ( := ) { typ; loc } expr =
      match loc with
      | Local { idx } -> C.Expression.local_set me idx expr
      | Global { name; mut = true; _ } -> C.Expression.global_set me name expr
      | Global { name; mut = false; _ } ->
          raise_s [%message "global" name "is declared immutable"]
      | Address { addr; size; offset; align; mem } ->
          C.Expression.store me size offset align addr expr typ mem
  end

  module Control = struct
    let block ?name ?typ es =
      let es_start, es_len = c_args T.Expression.t es in
      C.Control.block me name es_start es_len
        (Option.value typ ~default:Type.auto)
  end

  module Function = struct
    type ctx = { mutable next_index : int; mutable locals : T.Type.t list }

    let cnt = ref 0
    let curr : ctx option ref = ref None

    let gensym () =
      cnt := !cnt + 1;
      "__fun" ^ string_of_int !cnt

    let local typ =
      match !curr with
      | Some t ->
          t.locals <- typ :: t.locals;
          t.next_index <- t.next_index + 1;
          Cell0.{ typ; loc = Local { idx = u32_of_int (t.next_index - 1) } }
      | None -> failwith "local: outside function"

    let make' ?name ~params ~result f =
      let name = Option.value_or_thunk name ~default:gensym in
      let ctx = { next_index = Type.arity params; locals = [] } in
      curr := Some ctx;
      let body =
        f
          (List.mapi (Type.expanded params) ~f:(fun k typ ->
               Cell0.{ typ; loc = Local { idx = u32_of_int k } }))
      in
      let locals_start, locals_len = c_args T.Type.t ctx.locals in
      let fn =
        C.Function.make me name params result locals_start locals_len body
      in
      curr := None;
      fn

    let make ?name ~params ~result f =
      match !curr with
      | Some _ -> failwith "Function: function inside function"
      | None ->
          let fn = make' ?name ~params ~result f in
          fn

    let export name fn =
      C.Export.function_ me (C.Function.get_name fn) name |> ignore

    let start fn = C.Module.set_start me fn

    let import name module_name base_name params result =
      C.Import.function_ me name module_name base_name params result

    let call name args result =
      let args_start, args_len = c_args T.Expression.t args in
      C.Expression.call me name args_start args_len result

    let call_indirect name target args params result =
      let args_start, args_len = c_args T.Expression.t args in
      C.Expression.call_indirect me name target args_start args_len params
        result
  end

  module Table = struct
    let make ~initial ~maximum ty name =
      C.Table.add me name (u32_of_int initial) (u32_of_int maximum) ty

    let add name t funs =
      let fun_start, fun_len =
        funs |> List.map ~f:C.Function.get_name |> c_args Ctypes.string
      in
      C.Table.add_active_element_segment me (C.Table.get_name t) name fun_start
        fun_len
        (Const.i32 (Int32.of_int_exn 0))
  end

  module Memory = struct
    type segment = {
      name : string;
      data : string;
      passive : bool;
      offset : expr;
      size : T.Index.t;
    }

    let set ~initial ~maximum ?(shared = false) ?(memory64 = false)
        ?(segments = []) ?export_name ?(name = default_memory) () =
      let open Ctypes in
      let get f ty =
        List.map segments ~f |> CArray.of_list ty |> CArray.start
      in
      let names, datas, passives, offsets, sizes =
        ( get (fun s -> s.name) string,
          get (fun s -> s.data) string,
          get (fun s -> s.passive) bool,
          get (fun s -> s.offset) T.Expression.t,
          get (fun s -> s.size) T.Index.t )
      in
      C.Memory.set me (u32_of_int initial) (u32_of_int maximum) export_name
        names datas passives offsets sizes
        (List.length segments |> u32_of_int)
        shared memory64 name
  end

  let addr = Cell.addr

  let global ?(mut = true) name typ expr =
    let handle = C.Global.add me name typ mut expr in
    Cell0.{ typ; loc = Global { name; mut; handle } }

  let local = Function.local
end

let context_of_module t =
  (module MakeContext (struct
    let t = t
  end) : Context)

let context () =
  let t = C.Module.create () in
  Gc.Expert.add_finalizer_exn t (fun md -> C.Module.dispose md);
  context_of_module t
