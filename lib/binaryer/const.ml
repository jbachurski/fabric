open Core
open Common

module Make (M : sig
  val me : T.Module.t
end) =
struct
  let i32 x = C.Expression.const M.me (C.Literal.int32 x)
  let i32' x = C.Expression.const M.me (C.Literal.int32 (Int32.of_int_exn x))
end
