(* binaryen v121 *)
open Ctypes
module T = Types_generated

module Functions (F : Ctypes.FOREIGN) = struct
  open F

  let _free = foreign "free" (ptr void @-> returning void)

  module Module = struct
    (* Creation *)

    let create = foreign "BinaryenModuleCreate" (void @-> returning T.Module.t)
    let dispose = foreign "BinaryenModuleDispose" (T.Module.t @-> returning void)

    (* Attributes *)

    let set_start =
      foreign "BinaryenSetStart" (T.Module.t @-> T.Function.t @-> returning void)

    module Features = struct
      let get =
        foreign "BinaryenModuleGetFeatures"
          (T.Module.t @-> returning T.Features.t)

      let set =
        foreign "BinaryenModuleSetFeatures"
          (T.Module.t @-> T.Features.t @-> returning void)
    end

    module Optimize = struct
      let get = foreign "BinaryenGetOptimizeLevel" (void @-> returning int)
      let set = foreign "BinaryenSetOptimizeLevel" (int @-> returning void)
    end

    module Shrink = struct
      let get = foreign "BinaryenGetShrinkLevel" (void @-> returning int)
      let set = foreign "BinaryenSetShrinkLevel" (int @-> returning void)
    end

    (* Transformation *)

    let validate =
      foreign "BinaryenModuleValidate" (T.Module.t @-> returning int)

    let optimize =
      foreign "BinaryenModuleOptimize" (T.Module.t @-> returning void)

    (* Inspection *)

    let print = foreign "BinaryenModulePrint" (T.Module.t @-> returning void)

    let print_asm_js =
      foreign "BinaryenModulePrintAsmjs" (T.Module.t @-> returning void)

    let print_stack_ir =
      foreign "BinaryenModulePrintStackIR" (T.Module.t @-> returning void)

    let write =
      foreign "BinaryenModuleWriteText"
        (T.Module.t @-> ptr char @-> size_t @-> returning size_t)

    let write_stack_ir =
      foreign "BinaryenModuleWriteStackIR"
        (T.Module.t @-> ptr char @-> size_t @-> returning size_t)

    let write_wasm =
      foreign "BinaryenModuleWrite"
        (T.Module.t @-> ptr char @-> size_t @-> returning size_t)

    let interpret =
      foreign "BinaryenModuleInterpret" (T.Module.t @-> returning void)
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
    let funcref = !!"Funcref"
    let anyref = !!"Anyref"
    let structref = !!"Structref"
    let arrayref = !!"Arrayref"
    let unreachable = !!"Unreachable"
    let auto = !!"Auto"

    let tuple =
      foreign "BinaryenTypeCreate"
        (ptr T.Type.t @-> T.Index.t @-> returning T.Type.t)

    let arity = foreign "BinaryenTypeArity" (T.Type.t @-> returning uint32_t)

    let expand =
      foreign "BinaryenTypeExpand" (T.Type.t @-> ptr T.Type.t @-> returning void)

    module Packed = struct
      let ( !!! ) name =
        foreign ("BinaryenPackedType" ^ name) (void @-> returning T.PackedType.t)

      let no = !!!"NotPacked"
      let int8 = !!!"Int8"
      let int16 = !!!"Int16"
    end

    module Builder = struct
      let create =
        foreign "TypeBuilderCreate" (T.Index.t @-> returning T.TypeBuilder.t)

      let grow =
        foreign "TypeBuilderGrow"
          (T.TypeBuilder.t @-> T.Index.t @-> returning void)

      let size =
        foreign "TypeBuilderGetSize" (T.TypeBuilder.t @-> returning T.Index.t)

      let set_function =
        foreign "TypeBuilderSetSignatureType"
          (T.TypeBuilder.t @-> T.Index.t @-> T.Type.t @-> T.Type.t
         @-> returning void)

      let set_struct =
        foreign "TypeBuilderSetStructType"
          (T.TypeBuilder.t @-> T.Index.t @-> ptr T.Type.t @-> ptr T.PackedType.t
         @-> ptr bool @-> int @-> returning void)

      let set_array =
        foreign "TypeBuilderSetArrayType"
          (T.TypeBuilder.t @-> T.Index.t @-> T.Type.t @-> T.PackedType.t @-> int
         @-> returning void)

      let build_and_dispose =
        foreign "TypeBuilderBuildAndDispose"
          (T.TypeBuilder.t @-> ptr T.HeapType.t @-> ptr T.Index.t
          @-> ptr T.TypeBuilderErrorReason.t
          @-> returning bool)
    end

    let of_heap_type =
      foreign "BinaryenTypeFromHeapType"
        (T.HeapType.t @-> bool @-> returning T.Type.t)
  end

  module Literal = struct
    let ( $$ ) name ty =
      foreign ("BinaryenLiteral" ^ name) (ty @-> returning T.Literal.t)

    let int32 = "Int32" $$ int32_t
  end

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

    let const =
      foreign "BinaryenConst"
        (T.Module.t @-> T.Literal.t @-> returning T.Expression.t)

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

    let global_get =
      foreign "BinaryenGlobalGet"
        (T.Module.t @-> string @-> T.Type.t @-> returning T.Expression.t)

    let global_set =
      foreign "BinaryenGlobalSet"
        (T.Module.t @-> string @-> T.Expression.t @-> returning T.Expression.t)

    let load =
      foreign "BinaryenLoad"
        (T.Module.t @-> uint32_t @-> bool @-> uint32_t @-> uint32_t @-> T.Type.t
       @-> T.Expression.t @-> string @-> returning T.Expression.t)

    let store =
      foreign "BinaryenStore"
        (T.Module.t @-> uint32_t @-> uint32_t @-> uint32_t @-> T.Expression.t
       @-> T.Expression.t @-> T.Type.t @-> string @-> returning T.Expression.t)

    let call =
      foreign "BinaryenCall"
        (T.Module.t @-> string @-> ptr T.Expression.t @-> T.Index.t @-> T.Type.t
       @-> returning T.Expression.t)

    let call_indirect =
      foreign "BinaryenCallIndirect"
        (T.Module.t @-> string @-> T.Expression.t @-> ptr T.Expression.t
       @-> T.Index.t @-> T.Type.t @-> T.Type.t @-> returning T.Expression.t)

    let call_ref =
      foreign "BinaryenCallRef"
        (T.Module.t @-> T.Expression.t @-> ptr T.Expression.t @-> T.Index.t
       @-> T.Type.t @-> bool @-> returning T.Expression.t)

    let ref_cast =
      foreign "BinaryenRefCast"
        (T.Module.t @-> T.Expression.t @-> T.Type.t @-> returning T.Expression.t)

    let ref_func =
      foreign "BinaryenRefFunc"
        (T.Module.t @-> string @-> T.Type.t @-> returning T.Expression.t)

    let struct_new =
      foreign "BinaryenStructNew"
        (T.Module.t @-> ptr T.Expression.t @-> T.Index.t @-> T.HeapType.t
       @-> returning T.Expression.t)

    let struct_get =
      foreign "BinaryenStructGet"
        (T.Module.t @-> T.Index.t @-> T.Expression.t @-> T.Type.t @-> bool
       @-> returning T.Expression.t)

    let struct_set =
      foreign "BinaryenStructSet"
        (T.Module.t @-> T.Index.t @-> T.Expression.t @-> T.Expression.t
       @-> returning T.Expression.t)

    let array_new =
      foreign "BinaryenArrayNew"
        (T.Module.t @-> T.HeapType.t @-> T.Expression.t @-> T.Expression.t
       @-> returning T.Expression.t)

    let array_get =
      foreign "BinaryenArrayGet"
        (T.Module.t @-> T.Expression.t @-> T.Expression.t @-> T.Type.t @-> bool
       @-> returning T.Expression.t)

    let array_set =
      foreign "BinaryenArraySet"
        (T.Module.t @-> T.Expression.t @-> T.Expression.t @-> T.Expression.t
       @-> returning T.Expression.t)

    let array_len =
      foreign "BinaryenArrayLen"
        (T.Module.t @-> T.Expression.t @-> returning T.Expression.t)

    let drop =
      foreign "BinaryenDrop"
        (T.Module.t @-> T.Expression.t @-> returning T.Expression.t)

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
    let add =
      foreign "BinaryenAddTable"
        (T.Module.t @-> string @-> T.Index.t @-> T.Index.t @-> T.Type.t
       @-> returning T.Table.t)

    let get_name =
      foreign "BinaryenTableGetName" (T.Table.t @-> returning string)

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
    let add =
      foreign "BinaryenAddGlobal"
        (T.Module.t @-> string @-> T.Type.t @-> bool @-> T.Expression.t
       @-> returning T.Global.t)
  end

  module Memory = struct
    let set =
      foreign "BinaryenSetMemory"
        (T.Module.t @-> T.Index.t @-> T.Index.t @-> string_opt @-> ptr string
       @-> ptr string @-> ptr bool @-> ptr T.Expression.t @-> ptr T.Index.t
       @-> T.Index.t @-> bool @-> bool @-> string @-> returning void)
  end

  module Import = struct
    let function_ =
      foreign "BinaryenAddFunctionImport"
        (T.Module.t @-> string @-> string @-> string @-> T.Type.t @-> T.Type.t
       @-> returning void)
  end

  module Export = struct
    let function_ =
      foreign "BinaryenAddFunctionExport"
        (T.Module.t @-> string @-> string @-> returning T.Export.t)
  end

  module Features = struct
    let ( !! ) name =
      foreign ("BinaryenFeature" ^ name) (void @-> returning T.Features.t)

    let gc = !!"GC"
    let reference_types = !!"ReferenceTypes"
  end
end
