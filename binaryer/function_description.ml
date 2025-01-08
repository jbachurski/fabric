open Ctypes
module Types = Types_generated

module Functions (F : Ctypes.FOREIGN) = struct
  open F

  let module_create =
    foreign "BinaryenModuleCreate" (void @-> returning Types.module_)

  let module_dispose =
    foreign "BinaryenModuleDispose" (Types.module_ @-> returning void)

  let module_print =
    foreign "BinaryenModulePrint" (Types.module_ @-> returning void)
end
