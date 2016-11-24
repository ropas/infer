module F = Format
module L = Logging

exception TODO

let sym_size = ref 0

(* TODO: Due to the side-effect of the symbol numbers, it might have
   to place the Symbol module at the outside of the
   BufferOverrunDomain module. *)
module Symbol =
struct
  type t = int

  let compare : t -> t -> int = compare

  let get_new : unit -> t
  = fun () ->
    let x = !sym_size in
    sym_size := !sym_size + 1;
    x

  let pp : F.formatter -> t -> unit
  = fun fmt x ->
    F.fprintf fmt "s_%d" x
end

module Coeff =
struct
  module M = Map.Make(Symbol)

  type t = int M.t

  let empty : t = M.empty

  let initial : t = empty

  let find : Symbol.t -> t -> int
  = fun s x ->
    try M.find s x with
    | Not_found -> 0

  let le : t -> t -> bool
  = fun x y ->
    M.for_all (fun s v -> v <= find s y) x

  (* TODO: Not efficient.  Modify the function if it runs too slow. *)
  let eq : t -> t -> bool
  = fun x y ->
    le x y && le y x

  let pp1 : F.formatter -> (Symbol.t * int) -> unit
  = fun fmt (s, c) ->
    F.fprintf fmt "%d%a" c Symbol.pp s

  let pp : F.formatter -> t -> unit
  = fun fmt x ->
    if M.cardinal x = 0 then F.fprintf fmt "empty" else
      let (s1, c1) = M.min_binding x in
      pp1 fmt (s1, c1);
      M.iter (fun s c -> F.fprintf fmt "+%a" pp1 (s, c)) (M.remove s1 x)
end

module Bound =
struct
  type t =
    | MInf
    | V of int * Coeff.t
    | PInf

  let le : t -> t -> bool
  = fun x y ->
    match x, y with
    | MInf, _
    | _, PInf -> true
    | _, MInf
    | PInf, _ -> false
    | V (c0, x0), V (c1, x1) -> c0 <= c1 && Coeff.eq x0 x1

  let min : t -> t -> t
  = fun x y ->
    match x, y with
    | MInf, _
    | _, MInf -> MInf
    | PInf, _ -> y
    | _, PInf -> x
    | V (c0, x0), V (c1, x1) ->
        if Coeff.eq x0 x1 then V (min c0 c1, x0) else MInf

  let max : t -> t -> t
  = fun x y ->
    match x, y with
    | PInf, _
    | _, PInf -> PInf
    | MInf, _ -> y
    | _, MInf -> x
    | V (c0, x0), V (c1, x1) ->
        if Coeff.eq x0 x1 then V (max c0 c1, x0) else PInf

  let widen_l : t -> t -> t
  = fun x y ->
    match x, y with
    | PInf, _
    | _, PInf -> failwith "Lower bound cannot be +oo."
    | MInf, _
    | _, MInf -> MInf
    | V (c0, x0), V (c1, x1) ->
        if c0 <= c1 && Coeff.eq x0 x1 then x else MInf

  let widen_u : t -> t -> t
  = fun x y ->
    match x, y with
    | MInf, _
    | _, MInf -> failwith "Upper bound cannot be -oo."
    | PInf, _
    | _, PInf -> PInf
    | V (c0, x0), V (c1, x1) ->
        if c0 >= c1 && Coeff.eq x0 x1 then x else PInf

  let pp : F.formatter -> t -> unit
  = fun fmt x ->
    match x with
    | MInf -> F.fprintf fmt "-oo"
    | PInf -> F.fprintf fmt "+oo"
    | V (c, y) ->
        if Coeff.le y Coeff.empty then
          F.fprintf fmt "%d" c
        else
          F.fprintf fmt "%d+%a" c Coeff.pp y

  let of_int : int -> t
  = fun n ->
    V (n, Coeff.empty)

  let initial : t = of_int 0
end

module SymItvPure =
struct
  type astate = Bound.t * Bound.t

  let initial : astate = (Bound.initial, Bound.initial)

  let (<=) : lhs:astate -> rhs:astate -> bool
  = fun ~lhs:(l1, u1) ~rhs:(l2, u2) ->
    Bound.le l2 l1 && Bound.le u1 u2

  let join : astate -> astate -> astate
  = fun (l1, u1) (l2, u2) ->
    (Bound.min l1 l2, Bound.max u1 u2)

  let widen : prev:astate -> next:astate -> num_iters:int -> astate
  = fun ~prev:(l1, u1) ~next:(l2, u2) ~num_iters:_ ->
    (Bound.widen_l l1 l2, Bound.widen_u u1 u2)

  let pp : F.formatter -> astate -> unit
  = fun fmt (l, u) ->
    F.fprintf fmt "[%a, %a]" Bound.pp l Bound.pp u

  let of_int : int -> astate
  = fun n ->
    (Bound.of_int n, Bound.of_int n)
end

module SymItv = AbstractDomain.BottomLifted(SymItvPure)

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

let get_mem : astate -> Mem.astate
= fun s ->
  fst s

let get_cond : astate -> Conditions.astate
= fun s ->
  snd s

let add_mem : Var.t -> Val.astate -> astate -> astate
= fun x y s ->
  (get_mem s |> Mem.add x y, get_cond s)

let find_mem : Var.t -> astate -> Val.astate
= fun x s ->
  Mem.find x (get_mem s)
