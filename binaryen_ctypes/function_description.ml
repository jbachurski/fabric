(* binaryen v121 *)
open Ctypes
module T = Types_generated

module Functions (F : Ctypes.FOREIGN) = struct
  open F

  let _free = foreign "free" (ptr void @-> returning void)

  module Module = struct
    let create = foreign "BinaryenModuleCreate" (void @-> returning T.Module.t)
    let dispose = foreign "BinaryenModuleDispose" (T.Module.t @-> returning void)
    let print = foreign "BinaryenModulePrint" (T.Module.t @-> returning void)

    let print_stack_ir =
      foreign "BinaryenModulePrintStackIR" (T.Module.t @-> returning void)

    let validate =
      foreign "BinaryenModuleValidate" (T.Module.t @-> returning int)

    let optimize =
      foreign "BinaryenModuleOptimize" (T.Module.t @-> returning void)

    let set_start =
      foreign "BinaryenSetStart" (T.Module.t @-> T.Function.t @-> returning void)
  end

  module Function = struct
    let make =
      foreign "BinaryenAddFunction"
        (T.Module.t @-> string @-> T.Type.t @-> T.Type.t @-> ptr T.Type.t
       @-> T.Index.t @-> T.Expression.t @-> returning T.Function.t)
  end

  module Expression = struct
    let local_get =
      foreign "BinaryenLocalGet"
        (T.Module.t @-> T.Index.t @-> T.Type.t @-> returning T.Expression.t)
  end

  module Table = struct
    let make =
      foreign "BinaryenAddTable"
        (T.Module.t @-> string @-> T.Index.t @-> T.Index.t @-> T.Type.t
       @-> returning T.Table.t)

    let add_active_element_segment =
      foreign "BinaryenAddActiveElementSegment"
        (T.Module.t @-> string @-> string @-> ptr string @-> T.Index.t
       @-> T.Expression.t
        @-> returning T.Element_segment.t)

    let add_passive_element_segment =
      foreign "BinaryenAddPassiveElementSegment"
        (T.Module.t @-> string @-> ptr string @-> T.Index.t
        @-> returning T.Element_segment.t)
  end

  module Global = struct
    let make =
      foreign "BinaryenAddGlobal"
        (T.Module.t @-> string @-> T.Type.t @-> bool @-> T.Expression.t
       @-> returning T.Global.t)
  end

  module Memory = struct
    let set =
      foreign "BinaryenSetMemory"
        (T.Module.t @-> T.Index.t @-> T.Index.t @-> string @-> ptr string
       @-> ptr string @-> ptr bool @-> ptr T.Expression.t @-> ptr T.Index.t
       @-> T.Index.t @-> bool @-> bool @-> string @-> returning void)
  end
end
