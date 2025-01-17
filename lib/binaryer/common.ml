module C = Binaryen_ctypes.Functions
module T = Binaryen_ctypes.Types

type uint32 = Unsigned.UInt32.t
type expr = T.Expression.t
type typ = T.Type.t

let int_of_u32 = Unsigned.UInt32.to_int
let u32_of_int = Unsigned.UInt32.of_int
let default_memory = "__memory__"

let c_args t xs =
  let open Ctypes.CArray in
  let a = of_list t xs in
  (start a, length a |> u32_of_int)

let with_c_buffer f =
  let open Ctypes in
  let rec go n =
    let buf = CArray.make char n in
    match
      f (CArray.start buf) (Unsigned.Size_t.of_int n) |> Unsigned.Size_t.to_int
    with
    | k when k < n -> (buf, k)
    | _ -> go (2 * n)
  in
  let buf, length = go 1 in
  string_from_ptr ~length (CArray.start buf)
