open Core
open Common

module Make (M : sig
  val me : T.Module.t
end) =
struct
  open Const.Make (M)

  let make ~initial ~maximum ty name =
    C.Table.add M.me name (u32_of_int initial) (u32_of_int maximum) ty

  let cell t idx =
    Cell.Cell0.
      {
        typ = C.Table.get_type t;
        loc = Table { name = C.Table.get_name t; idx };
      }

  let add name t funs =
    let fun_start, fun_len =
      funs |> List.map ~f:C.Function.get_name |> c_args Ctypes.string
    in
    C.Table.add_active_element_segment M.me (C.Table.get_name t) name fun_start
      fun_len (i32' 0)
end
