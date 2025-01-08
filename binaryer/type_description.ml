open Ctypes

module Types (F : Ctypes.TYPE) = struct
  open F

  type module_ = unit ptr

  let module_ : module_ typ = ptr void
end
