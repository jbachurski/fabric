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
    end) =
  Wrap
    (F)
    (struct
      open F

      type phantom
      type inner = unit structure ptr

      let t = ptr (structure T.name)
    end)

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
end
