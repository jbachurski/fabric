open! Core
open Common

type uint32 = Unsigned.UInt32.t
type expr = T.Expression.t

module Cell0 = Cell.Cell0

module type Context = sig
  val me : T.Module.t
  val feature : (unit -> T.Features.t) -> unit
  val validate : unit -> bool
  val interpret : unit -> unit
  val __optimize : unit -> unit
  val print : unit -> unit
  val print_stack_ir : unit -> unit
  val print_asm_js : unit -> unit
  val write : unit -> string
  val write_stack_ir : unit -> string

  module Const : sig
    val i32 : int32 -> expr
    val i32' : int -> expr
  end

  module Operator : sig
    val unary : (unit -> T.Operator.t) -> expr -> expr
    val binary : (unit -> T.Operator.t) -> expr -> expr -> expr

    module I32 : sig
      val ( + ) : expr -> expr -> expr
      val ( - ) : expr -> expr -> expr
      val ( * ) : expr -> expr -> expr
      val ( / ) : expr -> expr -> expr
      val ( = ) : expr -> expr -> expr
      val ( <> ) : expr -> expr -> expr
      val ( < ) : expr -> expr -> expr
      val ( <= ) : expr -> expr -> expr
      val ( > ) : expr -> expr -> expr
      val ( >= ) : expr -> expr -> expr
    end
  end

  module Cell : sig
    type t = Cell0.t

    val ( ! ) : t -> expr
    val ( := ) : t -> expr -> expr
  end

  module Control : sig
    val block : ?name:string -> ?typ:typ -> expr list -> expr
    val if_ : expr -> expr -> expr option -> expr
    val loop : ?in_:string -> expr -> expr
    val break : name:string -> ?cond:expr -> ?value:expr -> unit -> expr
    val unreachable : unit -> expr
  end

  module Function : sig
    val gensym : unit -> string

    val make :
      ?name:string ->
      params:typ ->
      result:typ ->
      (Cell.t list -> expr) ->
      T.Function.t

    val export : string -> T.Function.t -> unit
    val start : T.Function.t -> unit
    val import : string -> string -> string -> typ -> typ -> unit
    val call : string -> expr list -> typ -> expr
    val call_indirect : string -> expr -> expr list -> typ -> typ -> expr
    val call_ref : expr -> expr list -> typ -> expr
  end

  module Table : sig
    val make : initial:int -> maximum:int -> typ -> string -> T.Table.t
    val cell : T.Table.t -> expr -> Cell.t
    val add : string -> T.Table.t -> T.Function.t list -> T.Element_segment.t
  end

  module Memory : sig
    type segment = {
      name : string;
      data : string;
      passive : bool;
      offset : expr;
      size : uint32;
    }

    val set :
      initial:int ->
      maximum:int ->
      ?shared:bool ->
      ?memory64:bool ->
      ?segments:segment list ->
      ?export_name:string ->
      ?name:string ->
      unit ->
      unit
  end

  val local : typ -> Cell.t
  val global : ?mut:bool -> string -> typ -> expr -> Cell.t

  val addr :
    size:int -> offset:int -> ?align:int -> ?mem:string -> typ -> expr -> Cell.t

  module Struct : sig
    type t = Cell0.struct_t = {
      struct_type : T.HeapType.t;
      fields : (string * typ) list;
    }

    val t : (string * Type.field) list -> t
    val make : t -> (string * expr) list -> expr
    val cell : t -> expr -> string -> Cell.t
  end

  module Array : sig
    type t = Cell0.array_t = { array_type : T.HeapType.t; elem_type : typ }

    val t : Type.field -> t
    val make : t -> size:expr -> expr option -> expr
    val make_of_list : t -> expr list -> expr
    val cell : t -> expr -> expr -> Cell.t
  end
end
