open Core

module Type_var =
  String_id.Make
    (struct
      let module_name = "Type_var"
    end)
    ()

module Var =
  String_id.Make
    (struct
      let module_name = "Var"
    end)
    ()

module Label =
  String_id.Make
    (struct
      let module_name = "Label"
    end)
    ()
