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

  let plus : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.plus n1 n2, x1, a1)

  let minus : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.minus n1 n2, x1, a1)

  let mult : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.mult n1 n2, x1, a1)

  let div : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.div n1 n2, x1, a1)

  let mod_sem : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.mod_sem n1 n2, x1, a1)

  let shiftlt : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.shiftlt n1 n2, x1, a1)

  let shiftrt : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.shiftrt n1 n2, x1, a1)

  let lt_sem : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.lt_sem n1 n2, x1, a1)

  let gt_sem : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.gt_sem n1 n2, x1, a1)

  let le_sem : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.le_sem n1 n2, x1, a1)

  let ge_sem : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.ge_sem n1 n2, x1, a1)

  let eq_sem : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.eq_sem n1 n2, x1, a1)

  let ne_sem : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.ne_sem n1 n2, x1, a1)

  let land_sem : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.land_sem n1 n2, x1, a1)

  let lor_sem : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.lor_sem n1 n2, x1, a1)

  let prune : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.prune n1 n2, x1, a1)

  let prune_comp : Binop.t -> astate -> astate -> astate
  = fun c (n1, x1, a1) (n2, _, _) ->
    (Itv.prune_comp c n1 n2, x1, a1)

  let prune_eq : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.prune_eq n1 n2, x1, a1)

  let prune_ne : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.prune_ne n1 n2, x1, a1)
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
  let find l m = try find l m with Not_found -> Val.bot

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

include AbstractDomain.Pair(Mem)(ConditionSet)

let pp fmt (m, c) =
  F.fprintf fmt "@[<v 2>( %a,@,%a )@]" Mem.pp m ConditionSet.pp c

let get_mem : astate -> Mem.astate
= fun s ->
  fst s

let get_conds : astate -> ConditionSet.astate
= fun s ->
  snd s
