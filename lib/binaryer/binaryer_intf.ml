module C = Binaryen_ctypes.Functions
module T = Binaryen_ctypes.Types

type expr = T.Expression.t

module type Context = sig
  val me : T.Module.t
  val validate : unit -> bool
  val optimize : unit -> unit
  val print : unit -> unit
  val print_stack_ir : unit -> unit

  module Operator : sig
    val unary : (unit -> T.Operator.t) -> expr -> expr
    val binary : (unit -> T.Operator.t) -> expr -> expr -> expr

    module I32 : sig
      val ( + ) : expr -> expr -> expr
      val ( - ) : expr -> expr -> expr
      val ( * ) : expr -> expr -> expr
      val ( / ) : expr -> expr -> expr
    end
  end

  module Local : sig
    type t = { typ : T.Type.t; idx : Unsigned.uint32 }

    val ( ! ) : t -> expr
    val ( := ) : t -> expr -> expr
  end

  module Control : sig
    val block : ?name:string -> ?typ:T.Type.t -> expr list -> expr
  end

  module Function : sig
    val gensym : unit -> string

    val make :
      ?name:string ->
      params:T.Type.t ->
      result:T.Type.t ->
      (Local.t list -> expr) ->
      T.Function.t

    val export : string -> T.Function.t -> unit
    val start : T.Function.t -> unit
  end

  val new_local : T.Type.t -> Local.t
end
