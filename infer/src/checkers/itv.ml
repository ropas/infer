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

let sym_size = ref 0

module Symbol =
struct
  type t = int

  let compare : t -> t -> int
  = fun x y -> x - y

  let eq : t -> t -> bool
  = fun x y -> compare x y = 0

  let get_new : unit -> t
  = fun () ->
    let x = !sym_size in
    sym_size := !sym_size + 1;
    x

  let pp : F.formatter -> t -> unit
  = fun fmt x -> F.fprintf fmt "s$%d" x
end

module SubstMap = Map.Make (Symbol)

module SymLinear =
struct
  module M = Map.Make (Symbol)

  type t = int M.t

  let compare : t -> t -> int
  = M.compare (fun x y -> x - y)

  let empty : t
  = M.empty

  let add : int -> int -> t -> t
  = M.add

  let cardinal : t -> int
  = M.cardinal

  let choose : t -> (int * int)
  = M.choose

  let fold : (Symbol.t -> int -> 'b -> 'b) -> t -> 'b -> 'b
  = M.fold

  let mem : Symbol.t -> t -> bool
  = M.mem

  let initial : t
  = empty

  let find : Symbol.t -> t -> int
  = fun s x ->
    try M.find s x with
    | Not_found -> 0

  let le : t -> t -> bool
  = fun x y -> M.for_all (fun s v -> v <= find s y) x

  let get_new : unit -> t
  = fun () -> M.add (Symbol.get_new ()) 1 empty

  let eq : t -> t -> bool
  = fun x y -> le x y && le y x

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

  let zero : t
  = M.empty

  let is_zero : t -> bool
  = fun x -> M.for_all (fun _ v -> v = 0) x

  let is_mod_zero : t -> int -> bool
  = fun x n ->
    assert (n <> 0);
    M.for_all (fun _ v -> v mod n = 0) x

  let neg : t -> t
  = fun x -> M.map (~-) x

  (* Returns (Some n) only when n is not 0. *)
  let is_non_zero : int -> int option
  = fun n -> if n = 0 then None else Some n

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
  = fun x n -> M.map (( * ) n) x

  let div_const : t -> int -> t
  = fun x n -> M.map ((/) n) x

  (* Returns a symbol when the map contains only one symbol s with the
     coefficient 1. *)
  let one_symbol : t -> Symbol.t option
  = fun x ->
    let x = M.filter (fun _ v -> v <> 0) x in
    if M.cardinal x = 1 then
      let (k, v) = M.choose x in
      if v = 1 then Some k else None
    else None

  let is_one_symbol : t -> bool
  = fun x ->
    match one_symbol x with
    | Some _ -> true
    | None -> false

  let get_symbols : t -> Symbol.t list
  = fun x -> IList.map fst (M.bindings x)
end

module Bound =
struct
  type t =
    | MInf
    | Linear of int * SymLinear.t
    | MinMax of min_max_t * int * Symbol.t
    | PInf
    | Bot

  and min_max_t = Min | Max

  let pp_min_max : F.formatter -> min_max_t -> unit
  = fun fmt -> function
    | Min -> F.fprintf fmt "min"
    | Max -> F.fprintf fmt "max"


  let pp : F.formatter -> t -> unit
  = fun fmt -> function
    | MInf -> F.fprintf fmt "-oo"
    | PInf -> F.fprintf fmt "+oo"
    | Bot -> F.fprintf fmt "_|_"
    | Linear (c, x) ->
        if SymLinear.le x SymLinear.empty then
          F.fprintf fmt "%d" c
        else if c = 0 then
          F.fprintf fmt "%a" SymLinear.pp x
        else
          F.fprintf fmt "%a + %d" SymLinear.pp x c
    | MinMax (m, c, x) -> F.fprintf fmt "%a(%d, %a)" pp_min_max m c Symbol.pp x

  let compare : t -> t -> int
  = fun x y ->
    match x, y with
    | MInf, MInf -> 0
    | MInf, _ -> -1
    | _, MInf -> 1
    | Linear (c1, se1), Linear (c2, se2) ->
        let i = c1 - c2 in
        if i <> 0 then i else SymLinear.compare se1 se2
    | Linear _, _ -> -1
    | _, Linear _ -> 1
    | MinMax (m1, c1, s1), MinMax (m2, c2, s2) ->
        let i = compare m1 m2 in
        if i <> 0 then i else
          let i = c1 - c2 in
          if i <> 0 then i else Symbol.compare s1 s2
    | MinMax _, _ -> -1
    | _, MinMax _ -> 1
    | PInf, PInf -> 0
    | PInf, _ -> -1
    | _, PInf -> 1
    | Bot, Bot -> 0

  let of_int : int -> t
  = fun n -> Linear (n, SymLinear.empty)

  let of_sym : SymLinear.t -> t
  = fun s -> Linear (0, s)

  let is_symbolic : t -> bool
  = function
    | MInf | PInf | Bot -> false
    | Linear (_, se) -> SymLinear.cardinal se > 0
    | MinMax _ -> true

  let opt_lift : ('a -> 'b -> bool) -> 'a option -> 'b option -> bool
  = fun f a_opt b_opt ->
    match a_opt, b_opt with
    | None, _
    | _, None -> false
    | Some a, Some b -> f a b

  let eq_symbol : Symbol.t -> t -> bool
  = fun s -> function
    | Linear (c, se) ->
        c = 0 && opt_lift Symbol.eq (SymLinear.one_symbol se) (Some s)
    | _ -> false

  let one_symbol : t -> Symbol.t option
  = function
    | Linear (c, se) when c = 0 -> SymLinear.one_symbol se
    | _ -> None

  let is_one_symbol : t -> bool
  = fun x -> one_symbol x <> None

  let use_symbol : Symbol.t -> t -> bool
  = fun s -> function
    | PInf | MInf | Bot -> false
    | Linear (_, se) -> SymLinear.find s se <> 0
    | MinMax (_, _, s') -> Symbol.eq s s'

  let subst1 : t -> t -> Symbol.t -> t -> t
  = fun default x s y ->
    if not (use_symbol s x) then x else
      match x, y with
      | _, _ when eq_symbol s x -> y
      | Linear (c1, se1), Linear (c2, se2) ->
          let coeff = SymLinear.find s se1 in
          let c' = c1 + coeff * c2 in
          let se1 = SymLinear.add s 0 se1 in
          let se' = SymLinear.plus se1 (SymLinear.mult_const se2 coeff) in
          Linear (c', se')
      | MinMax (Min, _, s'), MInf when Symbol.eq s s' -> MInf
      | MinMax (Max, c, s'), MInf when Symbol.eq s s' ->
          Linear (c, SymLinear.zero)
      | MinMax (Max, _, s'), PInf when Symbol.eq s s' -> PInf
      | MinMax (Min, c, s'), PInf when Symbol.eq s s' ->
          Linear (c, SymLinear.zero)
      | MinMax (Min, c1, s'), Linear (c2, se)
        when Symbol.eq s s' && SymLinear.is_zero se ->
          Linear (min c1 c2, SymLinear.zero)
      | MinMax (Max, c1, s'), Linear (c2, se)
        when Symbol.eq s s' && SymLinear.is_zero se ->
          Linear (max c1 c2, SymLinear.zero)
      | MinMax (m, c, s'), _ when Symbol.eq s s' && is_one_symbol y ->
          (match one_symbol y with
           | Some s'' -> MinMax (m, c, s'')
           | _ -> assert false)
      | MinMax (Min, c1, s'), MinMax (Min, c2, s'') when Symbol.eq s s' ->
          MinMax (Min, min c1 c2, s'')
      | MinMax (Max, c1, s'), MinMax (Max, c2, s'') when Symbol.eq s s' ->
          MinMax (Max, max c1 c2, s'')
      | _ -> default

  (* substitution symbols in ``x'' with respect to ``map'' *)
  let subst : t -> t -> t SubstMap.t -> t
  = fun default x map -> SubstMap.fold (fun s y x -> subst1 default x s y) map x

  let le : t -> t -> bool
  = fun x y ->
    assert (x <> Bot && y <> Bot);
    match x, y with
    | MInf, _
    | _, PInf -> true
    | _, MInf
    | PInf, _ -> false
    | Linear (c0, x0), Linear (c1, x1) -> c0 <= c1 && SymLinear.eq x0 x1
    | MinMax (Min, c0, x0), MinMax (Min, c1, x1)
    | MinMax (Max, c0, x0), MinMax (Max, c1, x1) -> c0 <= c1 && Symbol.eq x0 x1
    | MinMax (Min, c0, x0), Linear (c1, x1) ->
        (c0 <= c1 && SymLinear.is_zero x1)
        || (c1 = 0 && opt_lift Symbol.eq (SymLinear.one_symbol x1) (Some x0))
    | Linear (c1, x1), MinMax (Max, c0, x0) ->
        (c1 <= c0 && SymLinear.is_zero x1)
        || (c1 = 0 && opt_lift Symbol.eq (SymLinear.one_symbol x1) (Some x0))
    | MinMax (Min, c0, x0), MinMax (Max, c1, x1) -> c0 <= c1 || Symbol.eq x0 x1
    | _, _ -> false

  let lt : t -> t -> bool
  = fun x y ->
    assert (x <> Bot && y <> Bot);
    match x, y with
    | MInf, Linear _
    | MInf, MinMax _
    | MInf, PInf
    | Linear _, PInf
    | MinMax _, PInf -> true
    | Linear (c0, x0), Linear (c1, x1) -> c0 < c1 && SymLinear.eq x0 x1
    | MinMax (Min, c0, _), Linear (c1, x1) -> c0 < c1 && SymLinear.is_zero x1
    | Linear (c1, x1), MinMax (Max, c0, _) -> c1 < c0 && SymLinear.is_zero x1
    | MinMax (Min, c0, _), MinMax (Max, c1, _) -> c0 < c1
    | _, _ -> false

  let eq : t -> t -> bool
  = fun x y ->
    if x = Bot && y = Bot then true else
    if x = Bot || y = Bot then false else
      le x y && le y x

  let min : t -> t -> t
  = fun x y ->
    assert (x <> Bot && y <> Bot);
    if le x y then x else
    if le y x then y else
      match x, y with
      | Linear (c0, x0), Linear (c1, x1)
        when SymLinear.is_zero x0 && c1 = 0 && SymLinear.is_one_symbol x1 ->
          (match SymLinear.one_symbol x1 with
           | Some x' -> MinMax (Min, c0, x')
           | None -> assert false)
      | Linear (c0, x0), Linear (c1, x1)
        when SymLinear.is_zero x1 && c0 = 0 && SymLinear.is_one_symbol x0 ->
          (match SymLinear.one_symbol x0 with
           | Some x' -> MinMax (Min, c1, x')
           | None -> assert false)
      | MinMax (Max, c0, _), Linear (c1, x1)
      | Linear (c1, x1), MinMax (Max, c0, _)
        when SymLinear.is_zero x1 && c0 < c1 -> Linear (c0, x1)
      | _, _ -> MInf

  let max : t -> t -> t
  = fun x y ->
    assert (x <> Bot && y <> Bot);
    if le x y then y else
    if le y x then x else
      match x, y with
      | Linear (c0, x0), Linear (c1, x1)
        when SymLinear.is_zero x0 && c1 = 0 && SymLinear.is_one_symbol x1 ->
          (match SymLinear.one_symbol x1 with
           | Some x' -> MinMax (Max, c0, x')
           | None -> assert false)
      | Linear (c0, x0), Linear (c1, x1)
        when SymLinear.is_zero x1 && c0 = 0 && SymLinear.is_one_symbol x0 ->
          (match SymLinear.one_symbol x0 with
           | Some x' -> MinMax (Max, c1, x')
           | None -> assert false)
      | MinMax (Min, c0, _), Linear (c1, x1)
      | Linear (c1, x1), MinMax (Min, c0, _)
        when SymLinear.is_zero x1 && c0 > c1 -> Linear (c0, x1)
      | _, _ -> PInf

  let widen_l : t -> t -> t
  = fun x y ->
    assert (x <> Bot && y <> Bot);
    if x = PInf || y = PInf then failwith "Lower bound cannot be +oo." else
    if le x y then x else
      MInf

  let widen_u : t -> t -> t
  = fun x y ->
    assert (x <> Bot && y <> Bot);
    if x = MInf || y = MInf then failwith "Upper bound cannot be -oo." else
    if le y x then x else
      PInf

  let initial : t
  = of_int 0

  let zero : t
  = Linear (0, SymLinear.zero)

  let one : t
  = Linear (1, SymLinear.zero)

  let is_zero : t -> bool
  = fun x ->
    assert (x <> Bot);
    match x with
    | Linear (c, y) -> c = 0 && SymLinear.is_zero y
    | _ -> false

  let is_const : t -> int option
  = fun x ->
    assert (x <> Bot);
    match x with
    | Linear (c, y) when SymLinear.is_zero y -> Some c
    | _ -> None

  let plus : t -> t -> t option
  = fun x y ->
    assert (x <> Bot && y <> Bot);
    match x, y with
    | MInf, PInf
    | PInf, MInf -> failwith "Cannot calculate +oo + -oo."
    | PInf, _
    | _, PInf -> Some PInf
    | MInf, _
    | _, MInf -> Some MInf
    | _, _ when is_zero x -> Some y
    | _, _ when is_zero y -> Some x
    | Linear (c1, x1), Linear (c2, x2) ->
        Some (Linear (c1 + c2, SymLinear.plus x1 x2))
    | _, _ -> None

  let minus : t -> t -> t option
  = fun x y ->
    assert (x <> Bot && y <> Bot);
    match x, y with
    | PInf, PInf -> failwith "Cannot calculate +oo - +oo."
    | MInf, MInf -> failwith "Cannot calculate -oo - -oo."
    | PInf, _ -> Some PInf
    | MInf, _ -> Some MInf
    | _, _ when is_zero y -> Some x
    | Linear (c1, x1), Linear (c2, x2) ->
        Some (Linear (c1 - c2, SymLinear.minus x1 x2))
    | _, _ -> None

  let mult_const : t -> int -> t option
  = fun x n ->
    assert (x <> Bot);
    assert (n <> 0);
    match x with
    | MInf -> Some (if n > 0 then MInf else PInf)
    | PInf -> Some (if n > 0 then PInf else MInf)
    | Linear (c, x') -> Some (Linear (c * n, SymLinear.mult_const x' n))
    | _ -> None

  let div_const : t -> int -> t option
  = fun x n ->
    assert (x <> Bot);
    if n = 0 then Some zero else
      match x with
      | MInf -> Some (if n > 0 then MInf else PInf)
      | PInf -> Some (if n > 0 then PInf else MInf)
      | Linear (c, x') ->
          if c mod n = 0 && SymLinear.is_mod_zero x' n then
            Some (Linear (c / n, SymLinear.div_const x' n))
          else None
      | _ -> None

  let neg : t -> t option
  = function
    | MInf -> Some PInf
    | PInf -> Some MInf
    | Linear (c, x) -> Some (Linear (-c, SymLinear.neg x))
    | MinMax _ -> None
    | Bot -> assert false

  let prune_l : t -> (t * t) -> t
  = fun x (l, u) ->
    assert (x <> Bot && l <> Bot && u <> Bot);
    match plus u one with
    | Some u' when le l x && le x u -> u'
    | _ -> x

  let prune_u : t -> (t * t) -> t
  = fun x (l, u) ->
    assert (x <> Bot && l <> Bot && u <> Bot);
    match minus l one with
    | Some l' when le l x && le x u -> l'
    | _ -> x

  let make_min_max : min_max_t -> t -> t -> t option
  = fun m x y ->
    assert (x <> Bot && y <> Bot);
    match x, y with
    | Linear (cx, x'), Linear (cy, y')
      when cy = 0 && SymLinear.is_zero x' && SymLinear.is_one_symbol y' ->
        (match SymLinear.one_symbol y' with
         | Some s -> Some (MinMax (m, cx, s))
         | None -> None)
    | Linear (cx, x'), Linear (cy, y')
      when cx = 0 && SymLinear.is_zero y' && SymLinear.is_one_symbol x' ->
        (match SymLinear.one_symbol x' with
         | Some s -> Some (MinMax (m, cy, s))
         | None -> None)
    | _, _ -> None

  let make_min : t -> t -> t option
  = make_min_max Min

  let make_max : t -> t -> t option
  = make_min_max Max

  let get_symbols : t -> Symbol.t list
  = function
    | MInf | PInf -> []
    | Linear (_, se) -> SymLinear.get_symbols se
    | MinMax (_, _, s) -> [s]
    | Bot -> assert false
end

module ItvPure =
struct
  type astate = Bound.t * Bound.t

  type t = astate

  let compare : t -> t -> int
  = fun (x1, x2) (y1, y2) ->
    let i = Bound.compare x1 y1 in
    if i <> 0 then i else Bound.compare x2 y2

  let initial : t
  = (Bound.initial, Bound.initial)

  let lb : t -> Bound.t
  = fst

  let ub : t -> Bound.t
  = snd

  let make : Bound.t -> Bound.t -> t
  = fun l u -> (l, u)

  let subst : t -> Bound.t SubstMap.t -> t
  = fun x map ->
    (Bound.subst Bound.MInf (lb x) map, Bound.subst Bound.PInf (ub x) map)

  let (<=) : lhs:t -> rhs:t -> bool
  = fun ~lhs:(l1, u1) ~rhs:(l2, u2) -> Bound.le l2 l1 && Bound.le u1 u2

  let join : t -> t -> t
  = fun (l1, u1) (l2, u2) -> (Bound.min l1 l2, Bound.max u1 u2)

  let widen : prev:t -> next:t -> num_iters:int -> t
  = fun ~prev:(l1, u1) ~next:(l2, u2) ~num_iters:_ ->
    (Bound.widen_l l1 l2, Bound.widen_u u1 u2)

  let pp : F.formatter -> t -> unit
  = fun fmt (l, u) -> F.fprintf fmt "[%a, %a]" Bound.pp l Bound.pp u

  let of_int : int -> t
  = fun n -> (Bound.of_int n, Bound.of_int n)

  let get_new_sym : unit -> t
  = fun () ->
    let lower = Bound.of_sym (SymLinear.get_new ()) in
    let upper = Bound.of_sym (SymLinear.get_new ()) in
    (lower, upper)

  let top : t
  = (Bound.MInf, Bound.PInf)

  let pos : t
  = (Bound.of_int 1, Bound.PInf)

  let nat : t
  = (Bound.of_int 0, Bound.PInf)

  let zero : t
  = of_int 0

  let one : t
  = of_int 1

  let true_sem : t
  = one

  let false_sem : t
  = zero

  let unknown_bool : t
  = (Bound.of_int 0, Bound.of_int 1)

  let is_true : t -> bool
  = fun (l, u) -> Bound.le (Bound.of_int 1) l || Bound.le u (Bound.of_int (-1))

  let is_false : t -> bool
  = fun (l, u) -> Bound.is_zero l && Bound.is_zero u

  let is_const : t -> int option
  = fun (l, u) ->
    match Bound.is_const l, Bound.is_const u with
    | Some n, Some m when n = m -> Some n
    | _, _ -> None

  let is_symbolic : t -> bool
  = fun (lb, ub) -> Bound.is_symbolic lb || Bound.is_symbolic ub

  let neg : t -> t
  = fun (l, u) ->
    let l' = Option.default Bound.MInf (Bound.neg u) in
    let u' = Option.default Bound.PInf (Bound.neg l) in
    (l', u')

  let lnot : t -> t
  = fun x ->
    if is_true x then false_sem else
    if is_false x then true_sem else
      unknown_bool

  let plus : t -> t -> t
  = fun (l1, u1) (l2, u2) ->
    let l' = Option.default Bound.MInf (Bound.plus l1 l2) in
    let u' = Option.default Bound.PInf (Bound.plus u1 u2) in
    (l', u')

  let minus : t -> t -> t
  = fun (l1, u1) (l2, u2) ->
    let l' = Option.default Bound.MInf (Bound.minus l1 u2) in
    let u' = Option.default Bound.PInf (Bound.minus u1 l2) in
    (l', u')

  let mult_const : t -> int -> t
  = fun (l, u) n ->
    if n = 0 then zero else
    if n > 0 then
      let l' = Option.default Bound.MInf (Bound.mult_const l n) in
      let u' = Option.default Bound.PInf (Bound.mult_const u n) in
      (l', u')
    else
      let l' = Option.default Bound.MInf (Bound.mult_const u n) in
      let u' = Option.default Bound.PInf (Bound.mult_const l n) in
      (l', u')

  (* Returns a correct value only when all coefficients are divided by
     n without remainder. *)
  let div_const : t -> int -> t
  = fun (l, u) n ->
    assert (n <> 0);
    if n > 0 then
      let l' = Option.default Bound.MInf (Bound.div_const l n) in
      let u' = Option.default Bound.PInf (Bound.div_const u n) in
      (l', u')
    else
      let l' = Option.default Bound.MInf (Bound.div_const u n) in
      let u' = Option.default Bound.PInf (Bound.div_const l n) in
      (l', u')

  let mult : t -> t -> t
  = fun x y ->
    match is_const x, is_const y with
    | _, Some n -> mult_const x n
    | Some n, _ -> mult_const y n
    | None, None -> top

  let div : t -> t -> t
  = fun x y ->
    match is_const y with
    | Some n when n <> 0 -> div_const x n
    | _ -> top

  (* x % [0,0] does nothing. *)
  let mod_sem : t -> t -> t
  = fun x y ->
    match is_const x, is_const y with
    | Some n, Some m -> if m = 0 then x else of_int (n mod m)
    | _, Some m -> (Bound.of_int (-m), Bound.of_int m)
    | _, None -> top

  (* x << [-1,-1] does nothing. *)
  let shiftlt : t -> t -> t
  = fun x y ->
    match is_const y with
    | Some n -> if n >= 0 then mult_const x (1 lsl n) else x
    | None -> top

  (* x >> [-1,-1] does nothing. *)
  let shiftrt : t -> t -> t
  = fun x y ->
    match is_const y with
    | Some n -> if n >= 0 then div_const x (1 lsl n) else x
    | None -> top

  let lt_sem : t -> t -> t
  = fun (l1, u1) (l2, u2) ->
    if Bound.lt u1 l2 then true_sem else
    if Bound.le u2 l1 then false_sem else
      unknown_bool

  let gt_sem : t -> t -> t
  = fun x y -> lt_sem y x

  let le_sem : t -> t -> t
  = fun (l1, u1) (l2, u2) ->
    if Bound.le u1 l2 then true_sem else
    if Bound.lt u2 l1 then false_sem else
      unknown_bool

  let ge_sem : t -> t -> t
  = fun x y -> le_sem y x

  let eq_sem : t -> t -> t
  = fun (l1, u1) (l2, u2) ->
    if Bound.eq l1 u1 && Bound.eq u1 l2 && Bound.eq l2 u2 then true_sem else
    if Bound.lt u1 l2 || Bound.lt u2 l1 then false_sem else
      unknown_bool

  let ne_sem : t -> t -> t
  = fun (l1, u1) (l2, u2) ->
    if Bound.eq l1 u1 && Bound.eq u1 l2 && Bound.eq l2 u2 then false_sem else
    if Bound.lt u1 l2 || Bound.lt u2 l1 then true_sem else
      unknown_bool

  let land_sem : t -> t -> t
  = fun x y ->
    if is_true x && is_true y then true_sem else
    if is_false x || is_false y then false_sem else
      unknown_bool

  let lor_sem : t -> t -> t
  = fun x y ->
    if is_true x || is_true y then true_sem else
    if is_false x && is_false y then false_sem else
      unknown_bool

  let valid : t -> bool
  = fun (l, u) ->
    not (Bound.eq l Bound.PInf) && not (Bound.eq u Bound.MInf) && Bound.le l u

  let invalid : t -> bool
  = fun (l, u) ->
    Bound.eq l Bound.PInf || Bound.eq u Bound.MInf || Bound.lt u l

  let prune : t -> t -> t option
  = fun (l1, u1) y ->
    if not (valid y) then Some (l1, u1) else
      let x' = (Bound.prune_l l1 y, Bound.prune_u u1 y) in
      if invalid x' then None else Some x'

  let prune_comp_arith : Binop.t -> t -> t -> t option
  = fun c x (l, u) ->
    let y_opt =
      match c with
      | Binop.Lt -> Some (u, Bound.PInf)
      | Binop.Gt -> Some (Bound.MInf, l)
      | Binop.Le ->
          (match Bound.plus u Bound.one with
           | Some u' -> Some (u', Bound.PInf)
           | None -> None)
      | Binop.Ge ->
          (match Bound.minus l Bound.one with
           | Some l' -> Some (Bound.MInf, l')
           | None -> None)
      | _ -> assert false
    in
    match y_opt with
    | Some y' -> prune x y'
    | None -> Some x

  let prune_comp_minmax : Binop.t -> t -> t -> t option
  = fun c (lx, ux) (l, u) ->
    match c with
    | Binop.Lt ->
        (match Bound.minus u Bound.one with
         | Some u' ->
             (match Bound.make_min ux u' with
              | Some ux' -> Some (lx, ux')
              | None -> None)
         | None -> None)
    | Binop.Gt ->
        (match Bound.plus l Bound.one with
         | Some l' ->
             (match Bound.make_max lx l' with
              | Some lx' -> Some (lx', ux)
              | None -> None)
         | None -> None)
    | Binop.Le ->
        (match Bound.make_min ux u with
         | Some u' -> Some (lx, u')
         | None -> None)
    | Binop.Ge ->
        (match Bound.make_max lx l with
         | Some l' -> Some (l', ux)
         | None -> None)
    | _ -> assert false

  let prune_comp : Binop.t -> t -> t -> t option
  = fun c x (l, u) ->
    if not (valid (l, u)) then Some x else
      let x = Option.default x (prune_comp_arith c x (l, u)) in
      let x = Option.default x (prune_comp_minmax c x (l, u)) in
      if invalid x then None else Some x

  let prune_eq : t -> t -> t option
  = fun x y ->
    match prune_comp Binop.Le x y with
    | None -> None
    | Some x' -> prune_comp Binop.Ge x' y

  let prune_ne : t -> t -> astate option
  = fun x (l, u) ->
    if not (Bound.eq l Bound.PInf)
    && not (Bound.eq u Bound.MInf)
    && Bound.eq l u
    then prune x (l, u)
    else Some x

  let get_symbols : t -> Symbol.t list
  = fun (l, u) ->
    IList.append (Bound.get_symbols l) (Bound.get_symbols u)

  let rm_bnd_bot : t -> t option
  = fun (l, u) ->
    match l, u with
    | Bound.Bot, _
    | _, Bound.Bot -> None
    | _, _ -> Some (l, u)

  let has_bnd_bot : t -> bool
  = fun (l, u) ->
    l = Bound.Bot || u = Bound.Bot
end

include AbstractDomain.BottomLifted (ItvPure)

type t = astate

let compare : t -> t -> int
= fun x y ->
  match x, y with
  | Bottom, Bottom -> 0
  | Bottom, _ -> -1
  | _, Bottom -> 1
  | NonBottom x, NonBottom y -> ItvPure.compare x y

let bot : t
= initial

let top : t
= NonBottom ItvPure.top

let lb : t -> Bound.t
= function
  | NonBottom x -> ItvPure.lb x
  | _ -> raise (Failure "lower bound of bottom")

let ub : t -> Bound.t
= function
  | NonBottom x -> ItvPure.ub x
  | _ -> raise (Failure "upper bound of bottom")

let of_int : int -> astate
= fun n -> NonBottom (ItvPure.of_int n)

let is_bot : t -> bool
= fun x -> x = Bottom

let zero : t
= of_int 0

let one : t
= of_int 1

let pos : t
= NonBottom ItvPure.pos

let nat : t
= NonBottom ItvPure.nat

let make : Bound.t -> Bound.t -> t
= fun l u -> if Bound.lt u l then Bottom else NonBottom (ItvPure.make l u)

let is_symbolic : t -> bool
= function
  | NonBottom x -> ItvPure.is_symbolic x
  | Bottom -> false

let le : lhs:t -> rhs:t -> bool
= (<=)

let eq : t -> t -> bool
= fun x y -> (<=) ~lhs:x ~rhs:y && (<=) ~lhs:y ~rhs:x

let to_string : t -> string
= fun x ->
  pp F.str_formatter x;
  F.flush_str_formatter ()

let lift1 : (ItvPure.t -> ItvPure.t) -> t -> t
= fun f -> function
  | Bottom -> Bottom
  | NonBottom x -> NonBottom (f x)

let lift1_opt : (ItvPure.t -> ItvPure.t option) -> t -> t
= fun f -> function
  | Bottom -> Bottom
  | NonBottom x ->
      (match f x with
       | None -> Bottom
       | Some v -> NonBottom v)

let lift2 : (ItvPure.t -> ItvPure.t -> ItvPure.t) -> t -> t -> t
= fun f x y ->
  match x, y with
  | Bottom, _
  | _, Bottom -> Bottom
  | NonBottom x, NonBottom y -> NonBottom (f x y)

let lift2_opt : (ItvPure.t -> ItvPure.t -> ItvPure.t option) -> t -> t -> t
= fun f x y ->
  match x, y with
  | Bottom, _
  | _, Bottom -> Bottom
  | NonBottom x, NonBottom y ->
      (match f x y with
       | Some v -> NonBottom v
       | None -> Bottom)

let plus : t -> t -> t
= lift2 ItvPure.plus

let minus : t -> t -> t
= lift2 ItvPure.minus

let get_new_sym : unit -> t
= fun () -> NonBottom (ItvPure.get_new_sym ())

let neg : t -> t
= lift1 ItvPure.neg

let lnot : t -> t
= lift1 ItvPure.lnot

let mult : t -> t -> t
= lift2 ItvPure.mult

let div : t -> t -> t
= lift2 ItvPure.div

let mod_sem : t -> t -> t
= lift2 ItvPure.mod_sem

let shiftlt : t -> t -> t
= lift2 ItvPure.shiftlt

let shiftrt : t -> t -> t
= lift2 ItvPure.shiftrt

let lt_sem : t -> t -> t
= lift2 ItvPure.lt_sem

let gt_sem : t -> t -> t
= lift2 ItvPure.gt_sem

let le_sem : t -> t -> t
= lift2 ItvPure.le_sem

let ge_sem : t -> t -> t
= lift2 ItvPure.ge_sem

let eq_sem : t -> t -> t
= lift2 ItvPure.eq_sem

let ne_sem : t -> t -> t
= lift2 ItvPure.ne_sem

let land_sem : t -> t -> t
= lift2 ItvPure.land_sem

let lor_sem : t -> t -> t
= lift2 ItvPure.lor_sem

let prune : t -> t -> t
= lift2_opt ItvPure.prune

let prune_comp : Binop.t -> t -> t -> t
= fun comp -> lift2_opt (ItvPure.prune_comp comp)

let prune_eq : t -> t -> t
= lift2_opt ItvPure.prune_eq

let prune_ne : t -> t -> t
= lift2_opt ItvPure.prune_ne

let subst : t -> Bound.t SubstMap.t -> t
= fun x map ->
  match x with
  | NonBottom x' -> NonBottom (ItvPure.subst x' map)
  | _ -> x

let get_symbols : t -> Symbol.t list
= function
  | Bottom -> []
  | NonBottom x -> ItvPure.get_symbols x

let rm_bnd_bot : t -> t
= lift1_opt ItvPure.rm_bnd_bot

let has_bnd_bot : t -> bool
= function
  | Bottom -> false
  | NonBottom x -> ItvPure.has_bnd_bot x
