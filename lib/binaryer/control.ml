open Core
open Common

module Make (M : sig
  val me : T.Module.t
end) =
struct
  let block ?name ?typ es =
    let es_start, es_len = c_args T.Expression.t es in
    C.Control.block M.me name es_start es_len
      (Option.value typ ~default:Type.auto)
end
