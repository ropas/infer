module F = Format
module L = Logging

exception TODO

(* TODO: Due to the side-effect of the symbol numbers, it might have
   to place the Symbol module at the outside of the
   BufferOverrunDomain module. *)
module Symbol =
struct
  type t = int

  let compare = compare

  let get_new = raise TODO
end

module Coeff =
struct
  module M = Map.Make(Symbol)

  type t = int M.t
end

module SymItv =
struct
  type astate = int * Coeff.t

  let initial = raise TODO

  let (<=) = raise TODO

  let join = raise TODO

  let widen = raise TODO

  let pp = raise TODO

  let of_int = raise TODO
end

module Conditions =
struct
  (* set of safety conditions *)
  (* collect all the B.O. safety conditions
     in the function, in terms of symbol *)
  type cond =
    | Le of SymItv.astate * SymItv.astate
    | Lt of SymItv.astate * SymItv.astate
    | Eq of SymItv.astate * SymItv.astate

  type astate = cond list

  let initial = raise TODO

  let (<=) = raise TODO

  let join = raise TODO

  let widen = raise TODO

  let pp = raise TODO
end

module Val =
struct
  include AbstractDomain.Pair(SymItv)(ArrayBlk)

  let of_int = raise TODO
end

module PPMap = PrettyPrintable.MakePPMap
  (struct
     include Var
     let pp_key = pp
   end)

module Mem = AbstractDomain.Map(PPMap)(Val)

include AbstractDomain.Pair(Mem)(Conditions)
