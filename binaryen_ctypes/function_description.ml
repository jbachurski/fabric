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

    let get_name =
      foreign "BinaryenFunctionGetName" (T.Function.t @-> returning string)

    let set_body =
      foreign "BinaryenFunctionSetBody"
        (T.Function.t @-> T.Expression.t @-> returning void)
  end

  module Type = struct
    let ( !! ) name =
      foreign ("BinaryenType" ^ name) (void @-> returning T.Type.t)

    let none = !!"None"
    let int32 = !!"Int32"
    let int64 = !!"Int64"
    let float32 = !!"Float32"
    let float64 = !!"Float64"
    let unreachable = !!"Unreachable"
    let auto = !!"Auto"

    let tuple =
      foreign "BinaryenTypeCreate"
        (ptr T.Type.t @-> T.Index.t @-> returning T.Type.t)

    let arity = foreign "BinaryenTypeArity" (T.Type.t @-> returning uint32_t)

    let expand =
      foreign "BinaryenTypeExpand" (T.Type.t @-> ptr T.Type.t @-> returning void)
  end

  module Literal = struct end

  module Expression = struct
    module Operator = struct
      let ( !! ) name =
        foreign ("Binaryen" ^ name) (void @-> returning T.Operator.t)

      module I32 = struct
        let add = !!"AddInt32"
        let sub = !!"SubInt32"
        let mul = !!"MulInt32"
        let div_s = !!"DivSInt32"
        let div_u = !!"DivUInt32"
      end
    end

    let unary =
      foreign "BinaryenUnary"
        (T.Module.t @-> T.Operator.t @-> T.Expression.t
       @-> returning T.Expression.t)

    let binary =
      foreign "BinaryenBinary"
        (T.Module.t @-> T.Operator.t @-> T.Expression.t @-> T.Expression.t
       @-> returning T.Expression.t)

    let local_get =
      foreign "BinaryenLocalGet"
        (T.Module.t @-> T.Index.t @-> T.Type.t @-> returning T.Expression.t)

    let local_set =
      foreign "BinaryenLocalSet"
        (T.Module.t @-> T.Index.t @-> T.Expression.t
       @-> returning T.Expression.t)

    let unreachable =
      foreign "BinaryenUnreachable" (T.Module.t @-> returning T.Expression.t)
  end

  module Control = struct
    let block =
      foreign "BinaryenBlock"
        (T.Module.t @-> string_opt @-> ptr T.Expression.t @-> T.Index.t
       @-> T.Type.t @-> returning T.Expression.t)
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

  module Export = struct
    let function_ =
      foreign "BinaryenAddFunctionExport"
        (T.Module.t @-> string @-> string @-> returning T.Export.t)
  end
end
