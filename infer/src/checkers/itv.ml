open BasicDom

module F = Format
module L = Logging

exception TODO

(* TODO: Due to the side-effect of the symbol numbers, we may have to
   place the sym_size to the outside of the Itv module. *)
let sym_size = ref 0

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
  = fun fmt -> function
    | MInf -> F.fprintf fmt "-oo"
    | PInf -> F.fprintf fmt "+oo"
    | V (c, x) ->
        if Coeff.le x Coeff.empty then
          F.fprintf fmt "%d" c
        else
          F.fprintf fmt "%d+%a" c Coeff.pp x

  let of_int : int -> t
  = fun n ->
    V (n, Coeff.empty)

  let initial : t = of_int 0
end

module ItvPure =
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

include AbstractDomain.BottomLifted(ItvPure)

type t = astate

let bot = initial

(* TODO *)
let top = bot

let zero = bot

let one = bot

let pos = bot

let nat = bot

let of_int : int -> astate
= fun n ->
  NonBottom (ItvPure.of_int n)

let le = (<=)

let eq x y = raise TODO

let to_string x = raise TODO

let plus x y =  raise TODO

let minus x y =  raise TODO
