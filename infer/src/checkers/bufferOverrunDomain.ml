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

open BasicDom

module F = Format
module L = Logging

module Condition = 
struct 
  type t = { idx : Itv.astate; size : Itv.astate; loc : Location.t }

  let compare = compare
  let pp fmt e = 
    F.fprintf fmt "%a < %a" Itv.pp e.idx Itv.pp e.size
  let get_location e = e.loc
  let make ~idx ~size loc = { idx; size; loc }
  let check c = 
    if Itv.is_symbolic c.idx || Itv.is_symbolic c.size then true
    else 
      let not_overrun = Itv.lt_sem c.idx c.size in 
      let not_underrun = Itv.le_sem Itv.zero c.idx in
      (not_overrun = Itv.one) && (not_underrun = Itv.one)

  let subst x subst_map = { idx = Itv.subst x.idx subst_map; size = Itv.subst x.size subst_map; loc = x.loc }
  let to_string x = "Offset : " ^ Itv.to_string x.idx ^ " Size : " ^ Itv.to_string x.size
end

module ConditionSet = 
struct
  module PPSet = PrettyPrintable.MakePPSet(struct include Condition let pp_element = pp end)
  include AbstractDomain.FiniteSet (PPSet)
  
  let add_bo_safety ~idx ~size loc cond = 
    add (Condition.make ~idx ~size loc) cond
  
  let subst : astate -> Itv.Bound.t Itv.SubstMap.t -> astate
  = fun x subst_map -> 
    fold (fun e -> add (Condition.subst e subst_map)) x empty

(* Sungkeun's version
  let pp : F.formatter -> astate -> unit
  = fun fmt x ->
    let pp_sep fmt () = F.fprintf fmt " @,/\\ " in
    F.fprintf fmt "@[<hov 0>";
    F.pp_print_list ~pp_sep pp_element fmt (elements x);
    F.fprintf fmt "@]"
*)    
end

module Val =
struct
  include AbstractDomain.Pair3(Itv)(PowLoc)(ArrayBlk)

  type t = astate

  let bot = initial

  let rec joins : astate list -> astate
  = function
    | [] -> bot
    | [a] -> a
    | a :: b -> join a (joins b)

  let get_itv (x,_,_) = x
  let get_pow_loc (_,x,_) = x
  let get_array_blk (_,_,x) = x
  let get_all_locs (_,p,a) = ArrayBlk.get_pow_loc a |> PowLoc.join p 

  let top_itv = (Itv.top, PowLoc.bot, ArrayBlk.bot)

  let of_int : int -> astate
  = fun n ->
    (Itv.of_int n, PowLoc.bot, ArrayBlk.bot)

  let of_pow_loc : PowLoc.t -> astate
  = fun x ->
    (Itv.bot, x, ArrayBlk.bot)

  let of_array_blk : ArrayBlk.astate -> astate
  = fun a ->
    (Itv.bot, PowLoc.bot, a)

  let zero : astate = of_int 0

  let get_new_sym : unit -> t 
  = fun () -> (Itv.get_new_sym (), PowLoc.bot, ArrayBlk.bot)

  let unknown_bit : astate -> astate
  = fun (_, x, a) ->
    (Itv.top, x, a)

  let neg : astate -> astate
  = fun (n, x, a) ->
    (Itv.neg n, x, a)

  let lnot : astate -> astate
  = fun (n, x, a) ->
    (Itv.lnot n, x, a)

  let lift_itv_func : (Itv.t -> Itv.t -> Itv.t) -> astate -> astate -> astate
  = fun f (n1, _, _) (n2, _, _) ->
    (f n1 n2, PowLoc.bot, ArrayBlk.bot)

  let lift_itv_func_preserve
    : (Itv.t -> Itv.t -> Itv.t) -> astate -> astate -> astate
  = fun f (n1, x1, a1) (n2, _, _) ->
    (f n1 n2, x1, a1)

  let plus : astate -> astate -> astate
  = fun (n1, _, a1) (n2, _, _) ->
    (Itv.plus n1 n2, PowLoc.bot, ArrayBlk.plus_offset a1 n2)

  let minus : astate -> astate -> astate
  = fun (n1, _, a1) (n2, _, a2) ->
    let n = Itv.join (Itv.minus n1 n2) (ArrayBlk.diff a1 a2) in
    let a = ArrayBlk.minus_offset a1 n2 in
    (n, PowLoc.bot, a)

  let mult : astate -> astate -> astate = lift_itv_func Itv.mult

  let div : astate -> astate -> astate = lift_itv_func Itv.div

  let mod_sem : astate -> astate -> astate = lift_itv_func Itv.mod_sem

  let shiftlt : astate -> astate -> astate = lift_itv_func Itv.shiftlt

  let shiftrt : astate -> astate -> astate = lift_itv_func Itv.shiftrt

  let lt_sem : astate -> astate -> astate = lift_itv_func Itv.lt_sem

  let gt_sem : astate -> astate -> astate = lift_itv_func Itv.gt_sem

  let le_sem : astate -> astate -> astate = lift_itv_func Itv.le_sem

  let ge_sem : astate -> astate -> astate = lift_itv_func Itv.ge_sem

  let eq_sem : astate -> astate -> astate = lift_itv_func Itv.eq_sem

  let ne_sem : astate -> astate -> astate = lift_itv_func Itv.ne_sem

  let land_sem : astate -> astate -> astate = lift_itv_func Itv.land_sem

  let lor_sem : astate -> astate -> astate = lift_itv_func Itv.lor_sem

  let prune : astate -> astate -> astate =
    lift_itv_func_preserve Itv.prune

  let prune_comp : Binop.t -> astate -> astate -> astate
  = fun c ->
    lift_itv_func_preserve (Itv.prune_comp c)

  let prune_eq : astate -> astate -> astate =
    lift_itv_func_preserve Itv.prune_eq

  let prune_ne : astate -> astate -> astate =
    lift_itv_func_preserve Itv.prune_ne

  let plus_pi : astate -> astate -> astate
  = fun (_, _, a1) (n2, _, _) ->
    (Itv.bot, PowLoc.bot, ArrayBlk.plus_offset a1 n2)

  let minus_pi : astate -> astate -> astate
  = fun (_, _, a1) (n2, _, _) ->
    (Itv.bot, PowLoc.bot, ArrayBlk.minus_offset a1 n2)

  let minus_pp : astate -> astate -> astate
  = fun (_, _, a1) (_, _, a2) ->
    (ArrayBlk.diff a1 a2, PowLoc.bot, ArrayBlk.bot)
end

module PPMap = 
struct 
  module Ord = struct include Loc let compare = compare let pp_key = pp end

  include PrettyPrintable.MakePPMap(Ord)

  let pp_collection ~pp_item fmt c =
    let pp_collection fmt c =
      let pp_sep fmt () = F.fprintf fmt ",@," in
      F.pp_print_list ~pp_sep pp_item fmt c in
    F.fprintf fmt "%a" pp_collection c

  let pp ~pp_value fmt m =
    let pp_item fmt (k, v) = F.fprintf fmt "%a -> %a" Ord.pp_key k pp_value v in
    F.fprintf fmt "@[<v 2>{ ";
    pp_collection ~pp_item fmt (bindings m);
    F.fprintf fmt " }@]"
end

module Mem = 
struct
  include AbstractDomain.Map(PPMap)(Val)
  let find l m =
    let l' =
      match l with
      | Loc.Var x when Loc.is_pvar_in_reg x -> Loc.PVarHeap x
      | _ -> l
    in
    try find l' m with
    | Not_found -> Val.bot

  let find_set : PowLoc.t -> astate -> Val.astate
  = fun locs mem -> 
    let find_join loc acc = Val.join acc (find loc mem) in
    PowLoc.fold find_join locs Val.bot

  let strong_update : PowLoc.t -> Val.astate -> astate -> astate
  = fun locs v mem ->
    PowLoc.fold (fun x -> add x v) locs mem

  let weak_update : PowLoc.t -> Val.astate -> astate -> astate
  = fun locs v mem ->
    PowLoc.fold (fun x -> add x (Val.join v (find x mem))) locs mem
end

module TempAlias =
struct
  module M = Map.Make(Ident)

  type astate = Pvar.t M.t

  let initial : astate = M.empty

  let (<=) : lhs:astate -> rhs:astate -> bool
  = fun ~lhs ~rhs ->
    let is_in_rhs k v =
      match M.find k rhs with
      | v' -> Pvar.equal v v'
      | exception Not_found -> false
    in
    M.for_all is_in_rhs lhs

  let join : astate -> astate -> astate
  = fun x y ->
    let join_v _ v1_opt v2_opt =
      match v1_opt, v2_opt with
      | None, None -> None
      | Some v, None
      | None, Some v -> Some v
      | Some v1, Some v2 -> if Pvar.equal v1 v2 then Some v1 else None
    in
    M.merge join_v x y

  let widen : prev:astate -> next:astate -> num_iters:int -> astate
  = fun ~prev ~next ~num_iters:_ ->
    join prev next

  let pp : F.formatter -> astate -> unit
  = fun fmt x ->
    let pp_sep fmt () = F.fprintf fmt ", @," in
    let pp1 fmt (k, v) =
      F.fprintf fmt "%a=%a" (Ident.pp Utils.pe_text) k (Pvar.pp Utils.pe_text) v
    in
    F.fprintf fmt "@[<hov 0>";
    F.pp_print_list ~pp_sep pp1 fmt (M.bindings x);
    F.fprintf fmt "@]"

  let load : Ident.t -> Exp.t -> astate -> astate
  = fun id exp m ->
    match exp with
    | Exp.Lvar x -> M.add id x m
    | _ -> m

  let store : Exp.t -> Exp.t -> astate -> astate
  = fun e _ m ->
    match e with
    | Exp.Lvar x -> M.filter (fun _ y -> not (Pvar.equal x y)) m
    | _ -> m

  let find : Ident.t -> astate -> Pvar.t option
  = fun k m ->
    try Some (M.find k m) with Not_found -> None
end

include AbstractDomain.Pair3(Mem)(ConditionSet)(TempAlias)

let pp fmt (m, c, ta) =
  F.fprintf fmt "@[<v 2>( %a,@,%a,@,%a )@]" Mem.pp m ConditionSet.pp c
    TempAlias.pp ta

let get_mem : astate -> Mem.astate = fst

let get_conds : astate -> ConditionSet.astate = snd

let get_temp_alias : astate -> TempAlias.astate = trd
