(*
 * Copyright (c) 2016 - present 
 * Kihong Heo (http://ropas.snu.ac.kr/~khheo)
 * Sungkeun Cho (http://ropas.snu.ac.kr/~skcho)
 * Kwangkeun Yi (http://ropas.snu.ac.kr/~kwang)
 * 
 * ROSAEC(Research On Software Analysis for Error-free Computing) Center
 * Programming Research Laboratory
 * Seoul National University, Korea
 * All rights reserved.
 *
 * This source code is licensed under the BSD style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 *)

module F = Format
module L = Logging

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

module SubstMap = Map.Make(struct type t = Symbol.t let compare = Symbol.compare end)

module SymExp =
struct
  module M = Map.Make(Symbol)

  type t = int M.t

  let empty : t = M.empty

  let add = M.add
  let cardinal = M.cardinal 
  let choose = M.choose 
  let fold = M.fold 
  let mem = M.mem

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

  let zero : t = M.empty

  let is_zero : t -> bool
  = fun x ->
    M.for_all (fun _ v -> v = 0) x

  let is_mod_zero : t -> int -> bool
  = fun x n ->
    assert (n <> 0);
    M.for_all (fun _ v -> v mod n = 0) x

  let neg : t -> t
  = fun x ->
    M.map (~-) x

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

  let mult_const : t -> int -> t
  = fun x n ->
    M.map (( * ) n) x

  let div_const : t -> int -> t
  = fun x n ->
    M.map ((/) n) x
end

module Bound =
struct
  type t =
    | MInf
    | V of int * SymExp.t
    | PInf

  let subst formal map =
    match formal with
      V (c, se) -> 
        SymExp.fold (fun sym coeff new_bound ->
            match new_bound with
              MInf | PInf -> new_bound
            | V (c', se') ->
              try
                let target = SubstMap.find sym map in
                match target with 
                  MInf | PInf -> target
                | V (target_c, target_se) when SymExp.cardinal target_se = 0 ->
                    V (c' + (target_c * coeff), se')
                | _ -> V (c', SymExp.add sym coeff se')
              with Not_found -> 
                V (c', SymExp.add sym coeff se')) se (V (c, SymExp.empty))
    | _ -> formal

  let le : t -> t -> bool
  = fun x y ->
    match x, y with
    | MInf, _
    | _, PInf -> true
    | _, MInf
    | PInf, _ -> false
    | V (c0, x0), V (c1, x1) -> c0 <= c1 && SymExp.eq x0 x1

  let lt : t -> t -> bool
  = fun x y ->
    match x, y with
    | MInf, V _
    | MInf, PInf
    | V _, PInf -> true
    | V (c0, x0), V (c1, x1) -> c0 < c1 && SymExp.eq x0 x1
    | _, _ -> false

  let eq : t -> t -> bool
  = fun x y ->
    match x, y with
    | MInf, MInf
    | PInf, PInf -> true
    | V (c0, x0), V (c1, x1) -> c0 = c1 && SymExp.eq x0 x1
    | _, _ -> false

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
  = fun s -> V (0, s)

  let initial : t = of_int 0

  let zero : t = V (0, SymExp.zero)

  let one : t = V (1, SymExp.zero)

  let is_zero : t -> bool
  = function
    | V (c, x) -> c = 0 && SymExp.is_zero x
    | _ -> false

  let is_const : t -> int option
  = function
    | V (c, x) when SymExp.is_zero x -> Some c
    | _ -> None

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

  let mult_const : t -> int -> t
  = fun x n ->
    assert (n <> 0);
    match x with
    | MInf -> if n > 0 then MInf else PInf
    | PInf -> if n > 0 then PInf else MInf
    | V (c, x') -> V (c * n, SymExp.mult_const x' n)

  let div_const : t -> int -> t option
  = fun x n ->
    if n = 0 then Some zero else
      match x with
      | MInf -> Some (if n > 0 then MInf else PInf)
      | PInf -> Some (if n > 0 then PInf else MInf)
      | V (c, x') ->
          if c mod n = 0 && SymExp.is_mod_zero x' n then
            Some (V (c / n, SymExp.div_const x' n))
          else None

  let neg : t -> t
  = function
    | MInf -> PInf
    | PInf -> MInf
    | V (c, x) -> V (-c, SymExp.neg x)

  let prune_l : t -> (t * t) -> t
  = fun x (l, u) ->
    if le l x && le x u then plus u one else x

  let prune_u : t -> (t * t) -> t
  = fun x (l, u) ->
    if le l x && le x u then minus l one else x
end

module ItvPure =
struct
  type astate = Bound.t * Bound.t
  type t = astate

  let initial : astate = (Bound.initial, Bound.initial)

  let lb = fst
  let ub = snd 

  let subst x map = (Bound.subst (lb x) map, Bound.subst (ub x) map)

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

  let nat : astate = (Bound.of_int 0, Bound.PInf)

  let zero : astate = of_int 0

  let one : astate = of_int 1

  let true_sem : astate = one

  let false_sem : astate = zero

  let unknown_bool : astate = (Bound.of_int 0, Bound.of_int 1)

  let is_true : astate -> bool
  = fun (l, u) ->
    Bound.le (Bound.of_int 1) l || Bound.le u (Bound.of_int (-1))

  let is_false : astate -> bool
  = fun (l, u) ->
    Bound.is_zero l && Bound.is_zero u

  let is_const : astate -> int option
  = fun (l, u) ->
    match Bound.is_const l, Bound.is_const u with
    | Some n, Some m when n = m -> Some n
    | _, _ -> None

  let neg : astate -> astate
  = fun (l, u) ->
    (Bound.neg u, Bound.neg l)

  let lnot : astate -> astate
  = fun x ->
    if is_true x then false_sem else
    if is_false x then true_sem else
      unknown_bool

  let plus : astate -> astate -> astate
  = fun (l1, u1) (l2, u2) ->
    (Bound.plus l1 l2, Bound.plus u1 u2)

  let minus : astate -> astate -> astate
  = fun (l1, u1) (l2, u2) ->
    (Bound.minus l1 u2, Bound.minus u1 l2)

  let mult_const : astate -> int -> astate
  = fun (l, u) n ->
    if n = 0 then zero else
      let l' = Bound.mult_const l n in
      let u' = Bound.mult_const u n in
      if n > 0 then (l', u') else (u', l')

  (* Returns a correct value only when all coefficients are divided by
     n without remainder. *)
  let div_const : astate -> int -> astate option
  = fun (l, u) n ->
    match Bound.div_const l n, Bound.div_const u n with
    | Some l', Some u' -> Some (if n >=0 then (l', u') else (u', l'))
    | _, _ -> None

  let mult : astate -> astate -> astate
  = fun x y ->
    match is_const x, is_const y with
    | _, Some n -> mult_const x n
    | Some n, _ -> mult_const y n
    | None, None -> top

  let div : astate -> astate -> astate
  = fun x y ->
    match is_const y with
    | Some n ->
        (match div_const x n with
         | Some x' -> x'
         | None -> top)
    | None -> top

  (* x % [0,0] does nothing. *)
  let mod_sem : astate -> astate -> astate
  = fun x y ->
    match is_const x, is_const y with
    | Some n, Some m -> if m = 0 then x else of_int (n mod m)
    | _, Some m -> (Bound.of_int (-m), Bound.of_int m)
    | _, None -> top

  (* x << [-1,-1] does nothing. *)
  let shiftlt : astate -> astate -> astate
  = fun x y ->
    match is_const y with
    | Some n -> if n >= 0 then mult_const x (1 lsl n) else x
    | None -> top

  (* x >> [-1,-1] does nothing. *)
  let shiftrt : astate -> astate -> astate
  = fun x y ->
    match is_const y with
    | Some n ->
        if n >= 0 then
          match div_const x (1 lsl n) with
          | Some x' -> x'
          | None -> top
        else x
    | None -> top

  let lt_sem : astate -> astate -> astate
  = fun (l1, u1) (l2, u2) ->
    if Bound.lt u1 l2 then true_sem else
    if Bound.le u2 l1 then false_sem else
      unknown_bool

  let gt_sem : astate -> astate -> astate
  = fun x y -> lt_sem y x

  let le_sem : astate -> astate -> astate
  = fun (l1, u1) (l2, u2) ->
    if Bound.le u1 l2 then true_sem else
    if Bound.lt u2 l1 then false_sem else
      unknown_bool

  let ge_sem : astate -> astate -> astate
  = fun x y -> le_sem y x

  let eq_sem : astate -> astate -> astate
  = fun (l1, u1) (l2, u2) ->
    if Bound.eq l1 u1 && Bound.eq u1 l2 && Bound.eq l2 u2 then true_sem else
    if Bound.lt u1 l2 || Bound.lt u2 l1 then false_sem else
      unknown_bool

  let ne_sem : astate -> astate -> astate
  = fun (l1, u1) (l2, u2) ->
    if Bound.eq l1 u1 && Bound.eq u1 l2 && Bound.eq l2 u2 then false_sem else
    if Bound.lt u1 l2 || Bound.lt u2 l1 then true_sem else
      unknown_bool

  let land_sem : astate -> astate -> astate
  = fun x y ->
    if is_true x && is_true y then true_sem else
    if is_false x || is_false y then false_sem else
      unknown_bool

  let lor_sem : astate -> astate -> astate
  = fun x y ->
    if is_true x || is_true y then true_sem else
    if is_false x && is_false y then false_sem else
      unknown_bool

  let valid : astate -> bool
  = fun (l, u) ->
    not (Bound.eq l Bound.PInf) && not (Bound.eq u Bound.MInf) && Bound.le l u

  let invalid : astate -> bool
  = fun (l, u) ->
    Bound.eq l Bound.PInf || Bound.eq u Bound.MInf || Bound.lt u l

  let prune : astate -> astate -> astate option
  = fun (l1, u1) y ->
    if not (valid y) then Some (l1, u1) else
      let x' = (Bound.prune_l l1 y, Bound.prune_u u1 y) in
      if invalid x' then None else Some x'

  let prune_comp : Binop.t -> astate -> astate -> astate option
  = fun c x (l, u) ->
    if not (valid (l, u)) then Some x else
      let y =
        match c with
        | Binop.Lt -> (u, Bound.PInf)
        | Binop.Gt -> (Bound.MInf, l)
        | Binop.Le -> (Bound.plus u Bound.one, Bound.PInf)
        | Binop.Ge -> (Bound.MInf, Bound.minus l Bound.one)
        | _ -> assert (false)
      in
      prune x y

  let prune_eq : astate -> astate -> astate option
  = fun x y ->
    match prune_comp Binop.Le x y with
    | None -> None
    | Some x' -> prune_comp Binop.Ge x' y

  let prune_ne : astate -> astate -> astate option
  = fun x y ->
    match prune_comp Binop.Lt x y with
    | None -> None
    | Some x' -> prune_comp Binop.Gt x' y
end

include AbstractDomain.BottomLifted(ItvPure)

type t = astate

let bot = initial

let top = NonBottom ItvPure.top

let lb = function NonBottom x -> ItvPure.lb x | _ -> raise (Failure "lower bound of bottom")
let ub = function NonBottom x -> ItvPure.ub x | _ -> raise (Failure "upper bound of bottom")

let of_int : int -> astate
= fun n ->
  NonBottom (ItvPure.of_int n)

let zero : astate = of_int 0

let one : astate = of_int 1

let pos : astate = NonBottom ItvPure.pos

let nat : astate = NonBottom ItvPure.nat

let le : lhs:astate -> rhs:astate -> bool = (<=)

let eq : astate -> astate -> bool
= fun x y ->
  (<=) ~lhs:x ~rhs:y && (<=) ~lhs:y ~rhs:x

let to_string : astate -> string
= fun x ->
  pp F.str_formatter x;
  F.flush_str_formatter ()

let lift1 : (ItvPure.t -> ItvPure.t) -> astate -> astate
= fun f -> function
  | Bottom -> Bottom
  | NonBottom x -> NonBottom (f x)

let lift2 : (ItvPure.t -> ItvPure.t -> ItvPure.t) -> astate -> astate -> astate
= fun f x y ->
  match x, y with
  | Bottom, _
  | _, Bottom -> Bottom
  | NonBottom x, NonBottom y -> NonBottom (f x y)

let lift2_opt
  : (ItvPure.t -> ItvPure.t -> ItvPure.t option) -> astate -> astate -> astate
= fun f x y ->
  match x, y with
  | Bottom, _
  | _, Bottom -> Bottom
  | NonBottom x, NonBottom y ->
      (match f x y with
       | Some v -> NonBottom v
       | None -> Bottom)

let plus : astate -> astate -> astate = lift2 ItvPure.plus

let minus : astate -> astate -> astate = lift2 ItvPure.minus

let get_new_sym () = NonBottom (ItvPure.get_new_sym ())

let neg : astate -> astate = lift1 ItvPure.neg

let lnot : astate -> astate = lift1 ItvPure.lnot

let mult : astate -> astate -> astate = lift2 ItvPure.mult

let div : astate -> astate -> astate = lift2 ItvPure.div

let mod_sem : astate -> astate -> astate = lift2 ItvPure.mod_sem

let shiftlt : astate -> astate -> astate = lift2 ItvPure.shiftlt

let shiftrt : astate -> astate -> astate = lift2 ItvPure.shiftrt

let lt_sem : astate -> astate -> astate = lift2 ItvPure.lt_sem

let gt_sem : astate -> astate -> astate = lift2 ItvPure.gt_sem

let le_sem : astate -> astate -> astate = lift2 ItvPure.le_sem

let ge_sem : astate -> astate -> astate = lift2 ItvPure.ge_sem

let eq_sem : astate -> astate -> astate = lift2 ItvPure.eq_sem

let ne_sem : astate -> astate -> astate = lift2 ItvPure.ne_sem

let land_sem : astate -> astate -> astate = lift2 ItvPure.land_sem

let lor_sem : astate -> astate -> astate = lift2 ItvPure.lor_sem

let prune : astate -> astate -> astate = lift2_opt ItvPure.prune

let prune_comp : Binop.t -> astate -> astate -> astate
= fun comp ->
  lift2_opt (ItvPure.prune_comp comp)

let prune_eq : astate -> astate -> astate = lift2_opt ItvPure.prune_eq

let prune_ne : astate -> astate -> astate = lift2_opt ItvPure.prune_ne

let subst : astate -> Bound.t SubstMap.t -> astate
= fun x map ->
  match x with 
    NonBottom x' -> NonBottom (ItvPure.subst x' map)
  | _ -> x
