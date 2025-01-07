open Core

let parse = Parser.parse
let parse_exn = Fn.compose Result.ok_or_failwith parse
