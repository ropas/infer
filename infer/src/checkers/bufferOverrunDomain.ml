module F = Format
module L = Logging

module Const =
struct 
  type astate = Bot | Const of int | Top

  let initial = Bot

  let of_int i = Const i

  let (<=) ~lhs ~rhs = 
    match lhs, rhs with
      _, Top -> true
    | Bot, _ -> true
    | _, _ -> false

  let join x y = 
    match x, y with
      Bot, _ -> y
    | _, Bot -> x
    | _, _ -> Top

  let widen ~prev ~next ~num_iters = 
    match prev, next with
      Bot, _ -> next
    | _, Bot -> prev
    | _, _ -> Top

  let to_string = function 
    | Bot -> "bot"
    | Const i -> string_of_int i
    | Top -> "top"

  let pp fmt astate = 
    F.fprintf fmt "%s" (to_string astate)
end

module Symbol = 
struct 
  (* TODO *)
end


module Conditions = 
struct 
  (* set of safety conditions *)
  (* collect all the B.O. safety conditions
     in the function, in terms of symbol *)
  (* TODO *)
end

module PPMap = PrettyPrintable.MakePPMap
  (struct 
     include Var
     let pp_key = pp
   end)

(* for test *)
include AbstractDomain.Map(PPMap) (Const)

(*
module Mem = AbstractDomain.Map(PPMap)(SymItv)
include AbstractDomain.Pair(Mem)(Condition)
*)
