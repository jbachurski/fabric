open Common

module Make (M : sig
  val me : T.Module.t
end) =
struct
  let unary op = C.Expression.unary M.me (op ())
  let binary op = C.Expression.binary M.me (op ())

  module I32 = struct
    let ( + ) = binary C.Expression.Operator.I32.add
    let ( - ) = binary C.Expression.Operator.I32.sub
    let ( * ) = binary C.Expression.Operator.I32.mul
    let ( / ) = binary C.Expression.Operator.I32.div_s
    let ( = ) = binary C.Expression.Operator.I32.eq
    let ( <> ) = binary C.Expression.Operator.I32.ne
    let ( < ) = binary C.Expression.Operator.I32.lt
    let ( <= ) = binary C.Expression.Operator.I32.le
    let ( > ) = binary C.Expression.Operator.I32.gt
    let ( >= ) = binary C.Expression.Operator.I32.ge
    let ( && ) = binary C.Expression.Operator.I32.bitand
    let ( || ) = binary C.Expression.Operator.I32.bitor
    let ( ^^ ) = binary C.Expression.Operator.I32.bitxor
  end
end
