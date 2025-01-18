open Core
open Common

let none = C.Type.none ()
let int32 = C.Type.int32 ()
let int64 = C.Type.int64 ()
let float32 = C.Type.float32 ()
let float64 = C.Type.float64 ()
let funcref = C.Type.funcref ()
let anyref = C.Type.anyref ()
let structref = C.Type.structref ()
let arrayref = C.Type.arrayref ()
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

module Packed = struct
  let no = C.Type.Packed.no ()
  let int8 = C.Type.Packed.int8 ()
  let int16 = C.Type.Packed.int16 ()
end

module Builder = struct
  let construct ?(n = 1) f =
    let open Ctypes in
    let builder = C.Type.Builder.create (u32_of_int n) in
    f builder;
    let n = C.Type.Builder.size builder |> int_of_u32 in
    let types = CArray.make T.HeapType.t n in
    let error_indices = CArray.make T.Index.t n in
    let error_reasons = CArray.make T.TypeBuilderErrorReason.t n in
    let status =
      C.Type.Builder.build_and_dispose builder (* *)
        (CArray.start types)
        (CArray.start error_indices)
        (CArray.start error_reasons)
    in
    match status with
    | true -> Ok (CArray.to_list types)
    | false ->
        Error
          (List.zip_exn
             (CArray.to_list error_indices)
             (CArray.to_list error_reasons))

  let construct_exn ?n f =
    match construct ?n f with
    | Ok tys -> tys
    | Error es ->
        let errors =
          List.map es ~f:(fun (i, r) ->
              (int_of_u32 i, int_of_u32 (T.TypeBuilderErrorReason.unwrap r)))
        in
        raise_s [%message "TypeBuilder" (errors : (int * int) list)]
end

let unwrap_singleton = function [ x ] -> x | _ -> failwith "unwrap_singleton"

type field = { t : T.Type.t; packed : T.PackedType.t; mut : bool }

let field ?(packed = Packed.no) ?(mut = false) t = { t; packed; mut }

let function_ params result =
  Builder.construct_exn (fun builder ->
      C.Type.Builder.set_function builder (u32_of_int 0) params result)
  |> unwrap_singleton

let struct_ fields =
  Builder.construct_exn (fun builder ->
      let open Ctypes in
      let get f ty = List.map fields ~f |> CArray.of_list ty |> CArray.start in
      let field_types, field_packed_types, field_mutables =
        ( get (fun s -> s.t) T.Type.t,
          get (fun s -> s.packed) T.PackedType.t,
          get (fun s -> s.mut) bool )
      in
      C.Type.Builder.set_struct builder (u32_of_int 0) field_types
        field_packed_types field_mutables (List.length fields))
  |> unwrap_singleton

let array { t; packed; mut } =
  Builder.construct_exn (fun builder ->
      C.Type.Builder.set_array builder (u32_of_int 0) t packed
        (if mut then 1 else 0))
  |> unwrap_singleton

let of_heap_type ?(nullable = false) t = C.Type.of_heap_type t nullable
