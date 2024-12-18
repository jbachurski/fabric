open! Core

let%expect_test "addition" =
  printf "%d" (1 + 2);
  [%expect {| 3 |}]
