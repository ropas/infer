module F = Format
module L = Logging

exception TODO

(* TODO: Due to the side-effect of the symbol numbers, we may have to
   place the sym_size outside of the Itv module. *)
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
    F.fprintf fmt "s$%d" x
end

module SymExp =
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

  let get_new : unit -> t
  = fun () ->
    M.add (Symbol.get_new ()) 1 empty

  (* TODO: Not efficient.  Modify the function if it runs too slow. *)
  let eq : t -> t -> bool
  = fun x y ->
    le x y && le y x

  let pp1 : F.formatter -> (Symbol.t * int) -> unit
  = fun fmt (s, c) ->
    if c = 0 then ()
    else if c = 1 then
      F.fprintf fmt "%a" Symbol.pp s
    else if c < 0 then
      F.fprintf fmt "(%d)x%a" c Symbol.pp s
    else
      F.fprintf fmt "%dx%a" c Symbol.pp s

  let pp : F.formatter -> t -> unit
  = fun fmt x ->
    if M.cardinal x = 0 then F.fprintf fmt "empty" else
      let (s1, c1) = M.min_binding x in
      pp1 fmt (s1, c1);
      M.iter (fun s c -> F.fprintf fmt " + %a" pp1 (s, c)) (M.remove s1 x)

  (* Returns (Some n) only when n is not 0. *)
  let is_non_zero : int -> int option
  = fun n ->
    if n = 0 then None else Some n

  let plus : t -> t -> t
  = fun x y ->
    let plus' _ n_opt m_opt =
      match n_opt, m_opt with
      | None, None -> None
      | Some v, None
      | None, Some v -> is_non_zero v
      | Some n, Some m -> is_non_zero (n + m)
    in
    M.merge plus' x y

  let minus : t -> t -> t
  = fun x y ->
    let minus' _ n_opt m_opt =
      match n_opt, m_opt with
      | None, None -> None
      | Some v, None -> is_non_zero v
      | None, Some v -> is_non_zero (-v)
      | Some n, Some m -> is_non_zero (n - m)
    in
    M.merge minus' x y
end

module Bound =
struct
  type t =
    | MInf
    | V of int * SymExp.t
    | PInf

  let le : t -> t -> bool
  = fun x y ->
    match x, y with
    | MInf, _
    | _, PInf -> true
    | _, MInf
    | PInf, _ -> false
    | V (c0, x0), V (c1, x1) -> c0 <= c1 && SymExp.eq x0 x1

  let min : t -> t -> t
  = fun x y ->
    match x, y with
    | MInf, _
    | _, MInf -> MInf
    | PInf, _ -> y
    | _, PInf -> x
    | V (c0, x0), V (c1, x1) ->
        if SymExp.eq x0 x1 then V (min c0 c1, x0) else MInf

  let max : t -> t -> t
  = fun x y ->
    match x, y with
    | PInf, _
    | _, PInf -> PInf
    | MInf, _ -> y
    | _, MInf -> x
    | V (c0, x0), V (c1, x1) ->
        if SymExp.eq x0 x1 then V (max c0 c1, x0) else PInf

  let widen_l : t -> t -> t
  = fun x y ->
    match x, y with
    | PInf, _
    | _, PInf -> failwith "Lower bound cannot be +oo."
    | MInf, _
    | _, MInf -> MInf
    | V (c0, x0), V (c1, x1) ->
        if c0 <= c1 && SymExp.eq x0 x1 then x else MInf

  let widen_u : t -> t -> t
  = fun x y ->
    match x, y with
    | MInf, _
    | _, MInf -> failwith "Upper bound cannot be -oo."
    | PInf, _
    | _, PInf -> PInf
    | V (c0, x0), V (c1, x1) ->
        if c0 >= c1 && SymExp.eq x0 x1 then x else PInf

  let pp : F.formatter -> t -> unit
  = fun fmt -> function
    | MInf -> F.fprintf fmt "-oo"
    | PInf -> F.fprintf fmt "+oo"
    | V (c, x) ->
        if SymExp.le x SymExp.empty then
          F.fprintf fmt "%d" c
        else if c = 0 then
          F.fprintf fmt "%a" SymExp.pp x
        else
          F.fprintf fmt "%a + %d" SymExp.pp x c

  let of_int : int -> t
  = fun n ->
    V (n, SymExp.empty)

  let of_sym : SymExp.t -> t
  = fun s -> V(0, s)

  let initial : t = of_int 0

  let plus : t -> t -> t
  = fun x y ->
    match x, y with
    | MInf, PInf
    | PInf, MInf -> failwith "+oo + -oo is undefined."
    | MInf, _
    | _, MInf -> MInf
    | PInf, _
    | _, PInf -> PInf
    | V (c1, x1), V (c2, x2) -> V (c1 + c2, SymExp.plus x1 x2)

  let minus : t -> t -> t
  = fun x y ->
    match x, y with
    | MInf, MInf
    | PInf, PInf -> failwith "+oo - +oo and -oo - -oo are undefined."
    | MInf, _
    | _, PInf -> MInf
    | PInf, _
    | _, MInf -> PInf
    | V (c1, x1), V (c2, x2) -> V (c1 - c2, SymExp.minus x1 x2)
end

module ItvPure =
struct
  type astate = Bound.t * Bound.t
  type t = astate

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

  let get_new_sym : unit -> t
  = fun () ->
    (* just for pretty printing *)
    let lower = Bound.of_sym (SymExp.get_new ()) in
    let upper = Bound.of_sym (SymExp.get_new ()) in
    (lower, upper)

  let top : astate = (Bound.MInf, Bound.PInf)

  let pos : astate = (Bound.of_int 1, Bound.PInf)

  let plus : astate -> astate -> astate
  = fun (l1, u1) (l2, u2) ->
    (Bound.plus l1 l2, Bound.plus u1 u2)

  let minus : astate -> astate -> astate
  = fun (l1, u1) (l2, u2) ->
    (Bound.minus l1 u2, Bound.minus u1 l2)
end

include AbstractDomain.BottomLifted(ItvPure)

type t = astate

let bot = initial

let top = NonBottom ItvPure.top

let of_int : int -> astate
= fun n ->
  NonBottom (ItvPure.of_int n)

let zero : astate = of_int 0

let one : astate = of_int 1

let pos : astate = NonBottom ItvPure.pos

(* TODO *)
let nat : astate = bot

let le : lhs:astate -> rhs:astate -> bool = (<=)

let eq : astate -> astate -> bool
= fun x y ->
  (<=) ~lhs:x ~rhs:y && (<=) ~lhs:y ~rhs:x

let to_string : astate -> string
= fun x ->
  pp F.str_formatter x;
  F.flush_str_formatter ()

let plus : astate -> astate -> astate
= fun x y ->
  match x, y with
  | Bottom, _
  | _, Bottom -> Bottom
  | NonBottom x', NonBottom y' -> NonBottom (ItvPure.plus x' y')

let minus : astate -> astate -> astate
= fun x y ->
  match x, y with
  | Bottom, _
  | _, Bottom -> Bottom
  | NonBottom x', NonBottom y' -> NonBottom (ItvPure.minus x' y')

let get_new_sym () = NonBottom (ItvPure.get_new_sym ())

let neg x = raise TODO
let lnot x = raise TODO
let mult x y = raise TODO
let div x y = raise TODO
let mod_sem x y = raise TODO
let shiftlt x y = raise TODO
let shiftrt x y = raise TODO
let lt_sem x y = raise TODO
let gt_sem x y = raise TODO
let le_sem x y = raise TODO
let ge_sem x y = raise TODO
let eq_sem x y = raise TODO
let ne_sem x y = raise TODO
let land_sem x y = raise TODO
let lor_sem x y = raise TODO

