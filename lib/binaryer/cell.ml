open Core
open Common

module Cell0 = struct
  type loc =
    | Local of { idx : uint32 }
    | Global of { name : string; mut : bool; handle : T.Global.t }
    | Address of {
        addr : expr;
        size : uint32;
        offset : uint32;
        align : uint32;
        mem : string;
      }
    | Struct of {
        target : T.Expression.t;
        struct_type : T.HeapType.t;
        field_idx : T.Index.t;
      }
    | Array of {
        target : T.Expression.t;
        array_type : T.HeapType.t;
        idx : T.Expression.t;
      }

  type array_t = { array_type : T.HeapType.t; elem_type : T.Type.t }

  type struct_t = {
    struct_type : T.HeapType.t;
    fields : (string * T.Type.t) list;
  }

  type t = { typ : typ; loc : loc }
end

module Make (M : sig
  val me : T.Module.t
end) =
struct
  type loc = Cell0.loc =
    | Local of { idx : T.Index.t }
    | Global of { name : string; mut : bool; handle : T.Global.t }
    | Address of {
        addr : expr;
        size : uint32;
        offset : uint32;
        align : uint32;
        mem : string;
      }
    | Struct of {
        target : T.Expression.t;
        struct_type : T.HeapType.t;
        field_idx : T.Index.t;
      }
    | Array of {
        target : T.Expression.t;
        array_type : T.HeapType.t;
        idx : T.Expression.t;
      }

  type t = Cell0.t = { typ : typ; loc : Cell0.loc }

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
    | Local { idx } -> C.Expression.local_get M.me idx typ
    | Global { name; _ } -> C.Expression.global_get M.me name typ
    | Address { addr; size; offset; align; mem } ->
        C.Expression.load M.me size false offset align typ addr mem
    | Struct { target; struct_type; field_idx } ->
        C.Expression.struct_get M.me field_idx
          (C.Expression.ref_cast M.me target (Type.of_heap_type struct_type))
          typ false
    | Array { target; array_type; idx } ->
        C.Expression.array_get M.me
          (C.Expression.ref_cast M.me target (Type.of_heap_type array_type))
          idx typ false

  let ( := ) { typ; loc } expr =
    match loc with
    | Local { idx } -> C.Expression.local_set M.me idx expr
    | Global { name; mut = true; _ } -> C.Expression.global_set M.me name expr
    | Global { name; mut = false; _ } ->
        raise_s [%message "global" name "is declared immutable"]
    | Address { addr; size; offset; align; mem } ->
        C.Expression.store M.me size offset align addr expr typ mem
    | Struct { target; struct_type; field_idx } ->
        C.Expression.struct_set M.me field_idx
          (C.Expression.ref_cast M.me target (Type.of_heap_type struct_type))
          expr
    | Array { target; array_type; idx } ->
        C.Expression.array_set M.me
          (C.Expression.ref_cast M.me target (Type.of_heap_type array_type))
          idx expr
end
