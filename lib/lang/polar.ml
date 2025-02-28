type 'a t = { pos : 'a; neg : 'a } [@@deriving sexp]

let flip { pos; neg } = { neg = pos; pos = neg }
let map ~f { pos; neg } = { pos = f pos; neg = f neg }

let lift ~f { pos; neg } { pos = pos'; neg = neg' } =
  { pos = f pos pos'; neg = f neg neg' }

let join { pos = { pos = pos1; neg = neg1 }; neg = { pos = neg2; neg = pos2 } }
    =
  { pos = (pos1, pos2); neg = (neg1, neg2) }
