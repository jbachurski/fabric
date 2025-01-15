open Core
open Binaryer_intf
module C = Binaryen_ctypes.Functions
module T = Binaryen_ctypes.Types

type expr = T.Expression.t

let int_of_u32 = Unsigned.UInt32.to_int
let u32_of_int = Unsigned.UInt32.of_int

let c_args t xs =
  let open Ctypes.CArray in
  let a = of_list t xs in
  (start a, length a |> u32_of_int)

module Type = struct
  let none = C.Type.none ()
  let int32 = C.Type.int32 ()
  let int64 = C.Type.int64 ()
  let float32 = C.Type.float32 ()
  let float64 = C.Type.float64 ()
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

  module Local = struct
    type t = { typ : T.Type.t; idx : Unsigned.UInt32.t }

    let ( ! ) { typ; idx } = C.Expression.local_get me idx typ
    let ( := ) { typ = _; idx } expr = C.Expression.local_set me idx expr
  end

  module Control = struct
    let block ?name ?typ es =
      let es_start, es_len = c_args T.Expression.t es in
      C.Control.block me name es_start es_len
        (Option.value typ ~default:Type.auto)
  end

  module Function = struct
    type t = { mutable next_index : int; mutable locals : T.Type.t list }

    let cnt = ref 0
    let curr : t option ref = ref None

    let gensym () =
      cnt := !cnt + 1;
      "__fun" ^ string_of_int !cnt

    let new_local typ =
      match !curr with
      | Some t ->
          t.locals <- typ :: t.locals;
          t.next_index <- t.next_index + 1;
          Local.{ typ; idx = u32_of_int (t.next_index - 1) }
      | None -> failwith "new_local: outside function"

    let make' ?name ~params ~result f =
      let name = Option.value_or_thunk name ~default:gensym in
      let ctx = { next_index = Type.arity params; locals = [] } in
      curr := Some ctx;
      let body =
        f
          (List.mapi (Type.expanded params) ~f:(fun k typ ->
               Local.{ typ; idx = u32_of_int k }))
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
  end

  let new_local = Function.new_local
end

let context_of_module t =
  (module MakeContext (struct
    let t = t
  end) : Context)

let context () =
  let t = C.Module.create () in
  Gc.Expert.add_finalizer_exn t (fun md -> C.Module.dispose md);
  context_of_module t
