open Core
open Common
open Cell.Cell0

module Make (M : sig
  val me : T.Module.t
end) =
struct
  type ctx = { mutable next_index : int; mutable locals : T.Type.t list }

  let cnt = ref 0
  let curr : ctx option ref = ref None

  let gensym () =
    cnt := !cnt + 1;
    "__fun" ^ string_of_int !cnt

  let local typ =
    match !curr with
    | Some t ->
        t.locals <- typ :: t.locals;
        t.next_index <- t.next_index + 1;
        { typ; loc = Local { idx = u32_of_int (t.next_index - 1) } }
    | None -> failwith "local: outside function"

  let make' ?name ~params ~result f =
    let name = Option.value_or_thunk name ~default:gensym in
    let ctx = { next_index = Type.arity params; locals = [] } in
    curr := Some ctx;
    let body =
      f
        (List.mapi (Type.expanded params) ~f:(fun k typ ->
             { typ; loc = Local { idx = u32_of_int k } }))
    in
    let locals_start, locals_len = c_args T.Type.t (List.rev ctx.locals) in
    let fn =
      C.Function.make M.me name params result locals_start locals_len body
    in
    curr := None;
    fn

  let make ?name ~params ~result f =
    match !curr with
    | Some _ -> failwith "Function: function inside function"
    | None ->
        let fn = make' ?name ~params ~result f in
        fn

  let export name fn =
    C.Export.function_ M.me (C.Function.get_name fn) name |> ignore

  let start fn = C.Module.set_start M.me fn

  let import name module_name base_name params result =
    C.Import.function_ M.me name module_name base_name params result

  let call name args result =
    let args_start, args_len = c_args T.Expression.t args in
    C.Expression.call M.me name args_start args_len result

  let call_indirect name target args params result =
    let args_start, args_len = c_args T.Expression.t args in
    C.Expression.call_indirect M.me name target args_start args_len params
      result

  let call_ref target args result =
    let args_start, args_len = c_args T.Expression.t args in
    C.Expression.call_ref M.me target args_start args_len result false
end
