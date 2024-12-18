open Core
module Name = String
module Label = String
module Tag = String

type name = Name.t
type label = Label.t
type tag = Tag.t
type 'value t = (name * 'value) list

let init = []

let bindings env xvs f =
  let env =
    List.fold xvs ~init:env ~f:(fun env (x, v) ->
        List.Assoc.add env ~equal:String.equal x v)
  in
  f ~env

let lookup env name = List.Assoc.find env ~equal:String.equal name
