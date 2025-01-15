open Core

let _ = Fabric.Assembly.assemble

let%expect_test "" =
  print_endline "Hello, world!";
  [%expect {| Hello, world! |}]
