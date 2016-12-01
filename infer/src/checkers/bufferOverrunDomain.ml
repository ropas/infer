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
  type t = { idx : Itv.astate; size : Itv.astate; 
             proc_desc : Procdesc.t; loc : Location.t; id : string }

  and astate = t

  let compare : t -> t -> int
  = fun x y ->
    let i = Itv.compare x.idx y.idx in
    if i <> 0 then i else
      let i = Itv.compare x.size y.size in
      if i <> 0 then i else
        let i = Location.compare x.loc y.loc in
        if i <> 0 then i else
          String.compare x.id y.id

  let set_size_pos s =
    if Itv.Bound.le (Itv.lb s) Itv.Bound.zero
    then Itv.make Itv.Bound.zero (Itv.ub s)
    else s

  let pp fmt e = 
    let size = set_size_pos e.size in
    F.fprintf fmt "%a < %a at %a in %s" Itv.pp e.idx Itv.pp size 
      Location.pp e.loc 
      (DB.source_file_to_string e.loc.Location.file)

  let get_location e = e.loc
  let get_proc_desc e = e.proc_desc
  let get_proc_name e = Procdesc.get_proc_name e.proc_desc
  let make proc_desc id ~idx ~size loc = { proc_desc; idx; size; loc ; id }

  let check c = 
    let size = set_size_pos c.size in
    if not Config.debug_mode && (Itv.is_symbolic c.idx || Itv.is_symbolic size) then true
    else 
      let not_overrun = Itv.lt_sem c.idx size in
      let not_underrun = Itv.le_sem Itv.zero c.idx in
      (not_overrun = Itv.one) && (not_underrun = Itv.one)
  
  let subst x subst_map = 
    { x with idx = Itv.subst x.idx subst_map; size = Itv.subst x.size subst_map; }

  let to_string x =
    let size = set_size_pos x.size in
    "Offset : " ^ Itv.to_string x.idx ^ " Size : " ^ Itv.to_string size
end

module ConditionSet = 
struct
  module PPSet = PrettyPrintable.MakePPSet(struct include Condition let pp_element = pp end)
  include AbstractDomain.FiniteSet (PPSet)
 
  let add_bo_safety pdesc id ~idx ~size loc cond = 
    add (Condition.make pdesc id ~idx ~size loc) cond

  module Map = Map.Make(struct
      type t = string * Location.t
      let compare (s1, l1) (s2, l2) =
        let i = String.compare s1 s2 in
        if i <> 0 then i else Location.compare l1 l2
    end)

  let merge : t -> t 
  = fun conds ->
    let map = fold (fun e map -> 
        let old_cond : Condition.t= try Map.find (e.id, e.loc) map with _ -> e in 
        let new_cond = Condition.make old_cond.proc_desc old_cond.id 
              ~idx:(Itv.join old_cond.idx e.idx) ~size:(Itv.join old_cond.size e.size) 
              old_cond.loc in
        Map.add (e.id,e.loc) new_cond map) conds Map.empty
    in
    Map.fold (fun _ v conds -> add v conds) map empty

  let subst : astate -> Itv.Bound.t Itv.SubstMap.t -> astate
  = fun x subst_map -> 
    fold (fun e -> add (Condition.subst e subst_map)) x empty

  let pp fmt x = 
    let pp_sep fmt () = F.fprintf fmt ", @," in
    let pp_element fmt v = Condition.pp fmt v in
    F.fprintf fmt "@[<v 0>Safety Conditions :@,";
    F.fprintf fmt "@[<hov 2>{ ";
    F.pp_print_list ~pp_sep pp_element fmt (elements x);
    F.fprintf fmt " }@]";
    F.fprintf fmt "@]"

  let pp_summary fmt x =
    let pp_sep fmt () = F.fprintf fmt ", @," in
    let pp_element fmt v = Condition.pp fmt v in
    F.fprintf fmt "@[<v 2>Safety Conditions :@,@,";
    F.fprintf fmt "@[<hov 1>{";
    F.pp_print_list ~pp_sep pp_element fmt (elements x);
    F.fprintf fmt " }@]";
    F.fprintf fmt "@]"
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
  let pos_itv = (Itv.pos, PowLoc.bot, ArrayBlk.bot)

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

  let prune : astate -> astate -> astate
  = lift_itv_func_preserve Itv.prune

  let prune_comp : Binop.t -> astate -> astate -> astate
  = fun c ->
    lift_itv_func_preserve (Itv.prune_comp c)

  let prune_eq : astate -> astate -> astate
  = lift_itv_func_preserve Itv.prune_eq

  let prune_ne : astate -> astate -> astate
  = lift_itv_func_preserve Itv.prune_ne

  let plus_pi : astate -> astate -> astate
  = fun (_, _, a1) (n2, _, _) ->
    (Itv.bot, PowLoc.bot, ArrayBlk.plus_offset a1 n2)

  let minus_pi : astate -> astate -> astate
  = fun (_, _, a1) (n2, _, _) ->
    (Itv.bot, PowLoc.bot, ArrayBlk.minus_offset a1 n2)

  let minus_pp : astate -> astate -> astate
  = fun (_, _, a1) (_, _, a2) ->
    (ArrayBlk.diff a1 a2, PowLoc.bot, ArrayBlk.bot)

  let subst (i,p,a) subst_map = 
    (Itv.subst i subst_map, p, ArrayBlk.subst a subst_map)
end

module Stack = 
struct
  module PPMap = 
  struct 
    module Ord = struct include Loc let pp_key = pp end

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
  include AbstractDomain.Map(PPMap)(Val)
  let find l m =
      try find l m with
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

  let pp_summary fmt mem =
    let pp_not_logical_var k v =
      if Loc.is_logical_var k then () else
        F.fprintf fmt "%a -> %a@," Loc.pp k Val.pp v
    in
    iter pp_not_logical_var mem
end

module Heap = 
struct
  module PPMap = 
  struct 
    module Ord = struct include Loc let pp_key = pp end

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

  include AbstractDomain.Map(PPMap)(Val)
  let find l m =
      try find l m with
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

  let pp_summary fmt mem =
    iter (fun k v -> F.fprintf fmt "%a -> %a@," Loc.pp k Val.pp v) mem
end

module Alias =
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
      | Some v1, Some v2 -> if Pvar.equal v1 v2 then Some v1 else assert false
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
(*    F.fprintf fmt "@[<v 0>Logical Variables :@,";*)
    F.fprintf fmt "@[<hov 2>{ @,";
    F.pp_print_list ~pp_sep pp1 fmt (M.bindings x);
    F.fprintf fmt " }@]";
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

module Mem = 
struct
  include AbstractDomain.Pair3(Stack)(Heap)(Alias)
  let pp : F.formatter -> astate -> unit
  = fun fmt (stack, heap, alias) ->
    F.fprintf fmt "Stack : @ %a, @ Heap : @ %a, @ Alias : @ %a" 
      Stack.pp stack Heap.pp heap Alias.pp alias
  let pp_summary : F.formatter -> astate -> unit
  = fun fmt (stack, heap, _) ->
    F.fprintf fmt "@[<v 2>Abstract Memory :@,@,";
    F.fprintf fmt "%a" Stack.pp_summary stack;
    F.fprintf fmt "%a" Heap.pp_summary heap ;
    F.fprintf fmt "@]"
  let find_stack k m = Stack.find k (fst m)
  let find_stack_set k m = Stack.find_set k (fst m)
  let find_heap k m = Heap.find k (snd m)
  let find_heap_set k m = Heap.find_set k (snd m)
  let find_alias k m = Alias.find k (trd m)
  let load_alias id e m = (fst m, snd m, Alias.load id e (trd m))
  let store_alias e1 e2 m = (fst m, snd m, Alias.store e1 e2 (trd m))
  let add_stack k v m = (Stack.add k v (fst m), snd m, trd m)
  let add_heap k v m = (fst m, Heap.add k v (snd m), trd m)
  let strong_update_stack p v m = (Stack.strong_update p v (fst m), snd m, trd m)
  let strong_update_heap p v m = (fst m, Heap.strong_update p v (snd m), trd m)
  let weak_update_stack p v m = (Stack.weak_update p v (fst m), snd m, trd m)
  let weak_update_heap p v m = (fst m, Heap.weak_update p v (snd m), trd m)
end


(* TODO: what about removing the conditionset from the domain? *)
include AbstractDomain.Pair(Mem)(ConditionSet)

let (<=) ~lhs ~rhs =
  if lhs == rhs then true else
    Mem.(<=) ~lhs:(fst lhs) ~rhs:(fst rhs)

let pp fmt (m, c) =
  F.fprintf fmt "@[<v 2>( %a,@,%a )@]" Mem.pp m ConditionSet.pp c

let pp_summary fmt (m, c) =
  F.fprintf fmt "%a@,%a" Mem.pp_summary m ConditionSet.pp_summary c

let get_mem : astate -> Mem.astate = fst

let get_conds : astate -> ConditionSet.astate = snd

type summary = astate * astate
let pp_summary_ fmt (entry_mem, exit_mem) = 
  F.fprintf fmt "%a@,%a" pp entry_mem pp exit_mem
