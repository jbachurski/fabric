open Core
open Common

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
