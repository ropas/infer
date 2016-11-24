type astate = Bot
type t = astate
exception Not_implemented

let initial = Bot
let bot = Bot
let top = Bot
let zero = Bot
let one = Bot
let pos = Bot
let nat = Bot
let (<=) ~lhs ~rhs = raise Not_implemented
let le = (<=)
let eq x y = raise Not_implemented
let join x y = raise Not_implemented
let widen ~prev ~next ~num_iters = raise Not_implemented
let to_string x = raise Not_implemented
let pp fmt astate =  raise Not_implemented
let plus x y =  raise Not_implemented
let minus x y =  raise Not_implemented

