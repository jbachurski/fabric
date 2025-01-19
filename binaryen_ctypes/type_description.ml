(* binaryen v121 *)
open Ctypes

module Wrap
    (F : Ctypes.TYPE)
    (T : sig
      type phantom
      type inner

      val t : inner F.typ
    end) : sig
  type t

  val wrap : T.inner -> t
  val unwrap : t -> T.inner
  val t : t F.typ
end = struct
  open F

  type _phantom = T.phantom
  type t = T.inner

  let wrap t = t
  let unwrap t = t
  let t : T.inner typ = T.t
end

module type PHANTOM = sig
  type phantom
end

module Ref
    (F : Ctypes.TYPE)
    (T : sig
      val name : string
    end) : sig
  type t

  val wrap : unit structure ptr -> t
  val unwrap : t -> unit structure ptr
  val t : t F.typ
  val opt : t option F.typ
end = struct
  open F

  type t = unit structure ptr

  let wrap t = t
  let unwrap t = t
  let t : t typ = ptr (structure T.name)
  let opt : t option typ = ptr_opt (structure T.name)
end

module Types (F : Ctypes.TYPE) = struct
  open! F

  module Index = struct
    type t = Unsigned.UInt32.t

    let t = uint32_t
  end

  module Type =
    Wrap
      (F)
      (struct
        type phantom
        type inner = Uintptr.t

        let t = uintptr_t
      end)

  module PackedType =
    Wrap
      (F)
      (struct
        type phantom
        type inner = Unsigned.UInt32.t

        let t = uint32_t
      end)

  module HeapType =
    Wrap
      (F)
      (struct
        type phantom
        type inner = Uintptr.t

        let t = uintptr_t
      end)

  module TypeBuilder =
    Ref
      (F)
      (struct
        let name = "TypeBuilder"
      end)

  module TypeBuilderErrorReason =
    Wrap
      (F)
      (struct
        type phantom
        type inner = Unsigned.UInt32.t

        let t = uint32_t
      end)

  module Literal = struct
    type t
    type v

    (* Making this structure explicit seems impossible in ctypes currently
       see: https://discuss.ocaml.org/t/ctypes-nested-anonymous-unions/1605
       Thankfully, this approach leaves the struct incomplete and uses
       the header's definition. *)
    (* 
    let v : v union typ = union "BinaryenLiteralData"
    let i32 = field v "i32" int32_t
    let i64 = field v "i64" int64_t
    let f32 = field v "f32" float
    let f64 = field v "f64" double
    let v128 = field v "v128" (array 16 uint8_t)
    let func = field v "func" string
    let () = seal v
    *)
    let t : t structure typ = structure "BinaryenLiteral"
    (* 
    let typ = field t "type" Type.t
    let value = field t "data" (array 16 uint8_t)
    *)

    let () = seal t
  end

  module Operator =
    Wrap
      (F)
      (struct
        type phantom
        type inner = Signed.Int32.t

        let t = int32_t
      end)

  module Module =
    Ref
      (F)
      (struct
        let name = "BinaryenModule"
      end)

  module Expression =
    Ref
      (F)
      (struct
        let name = "BinaryenExpression"
      end)

  module Function =
    Ref
      (F)
      (struct
        let name = "BinaryenFunction"
      end)

  module Memory =
    Ref
      (F)
      (struct
        let name = "BinaryenMemory"
      end)

  module Export =
    Ref
      (F)
      (struct
        let name = "BinaryenExport"
      end)

  module Global =
    Ref
      (F)
      (struct
        let name = "BinaryenGlobal"
      end)

  module Tag =
    Ref
      (F)
      (struct
        let name = "BinaryenTag"
      end)

  module Table =
    Ref
      (F)
      (struct
        let name = "BinaryenTable"
      end)

  module Element_segment =
    Ref
      (F)
      (struct
        let name = "BinaryenElementSegment"
      end)

  module Features = struct
    type t = Unsigned.UInt32.t

    let t = uint32_t
  end
end
