open Core
open Common

module Make (M : sig
  val me : T.Module.t
end) =
struct
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
    let get f ty = List.map segments ~f |> CArray.of_list ty |> CArray.start in
    let names, datas, passives, offsets, sizes =
      ( get (fun s -> s.name) string,
        get (fun s -> s.data) string,
        get (fun s -> s.passive) bool,
        get (fun s -> s.offset) T.Expression.t,
        get (fun s -> s.size) T.Index.t )
    in
    C.Memory.set M.me (u32_of_int initial) (u32_of_int maximum) export_name
      names datas passives offsets sizes
      (List.length segments |> u32_of_int)
      shared memory64 name
end
