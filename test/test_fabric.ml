let%expect_test "" =
  print_endline "Hello, world!";
  [%expect {| Hello, world! |}]

let () = ()
