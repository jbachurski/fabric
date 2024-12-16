open Core

module Name : sig
  type t

  include Sexpable.S with type t := t
  include Comparable.S with type t := t
  include Stringable.S with type t := t
end

module Label : sig
  type t

  include Sexpable.S with type t := t
  include Comparable.S with type t := t
  include Stringable.S with type t := t
end

module Tag : sig
  type t

  include Sexpable.S with type t := t
  include Comparable.S with type t := t
  include Stringable.S with type t := t
end

type name = Name.t
type label = Label.t
type tag = Tag.t
type 'value t

val init : 'value t
val bindings : 'value t -> (name * 'value) list -> (env:'value t -> 'a) -> 'a
val lookup : 'value t -> name -> 'value option
