open Core
module C = Binaryen_ctypes

module type Context = sig
  val me : C.Types.Module.t
  val optimize : unit -> unit
  val print : unit -> unit
  val print_stack_ir : unit -> unit
end

module Make_context (M : sig
  val t : C.Types.Module.t
end) : Context = struct
  let me = M.t
  let optimize () = C.Functions.Module.optimize me
  let print () = C.Functions.Module.print me
  let print_stack_ir () = C.Functions.Module.print_stack_ir me
end

let context_of_module t =
  (module Make_context (struct
    let t = t
  end) : Context)

let context () =
  let t = C.Functions.Module.create () in
  Gc.Expert.add_finalizer_exn t (fun md -> C.Functions.Module.dispose md);
  context_of_module t
