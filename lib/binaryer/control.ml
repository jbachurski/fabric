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

  let if_ cond on_true on_false = C.Control.if_ M.me cond on_true on_false
  let loop ?in_ body = C.Control.loop M.me in_ body
  let break ~name ?cond ?value () = C.Control.break M.me name cond value
  let unreachable () = C.Expression.unreachable M.me
end
