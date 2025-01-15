let%expect_test "" =
  let md = Binaryer.C.Functions.Module.create () in
  Binaryer.C.Functions.Module.print md;
  Binaryer.C.Functions.Module.dispose md;
  [%expect {|
    (module
    )
    |}]

let%expect_test "" =
  let (module Ctx) = Binaryer.context () in
  Ctx.print ();
  [%expect {|
    (module
    )
    |}]
