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

open! Utils
open BasicDom

module F = Format
module L = Logging

module Condition =
struct
  type t =
    { taint : FSTaintSet.t;
      proc_name : Procname.t;
      loc : Location.t;
      trace : trace }

  and trace = Intra of Procname.t
            | Inter of Procname.t * Procname.t * Location.t

  and astate = t

  let trace_compare x y =
    match x, y with
    | Intra _, Inter _ -> 1
    | Inter _, Intra _ -> -1
    | Intra p1, Intra p2 -> Procname.compare p1 p2
    | Inter (caller1, callee1, l1), Inter (caller2, callee2, l2) ->
        let i = Procname.compare caller1 caller2 in
        if i <> 0 then i else
          let i = Procname.compare callee1 callee2 in
          if i <> 0 then i else
            Location.compare l1 l2

  let compare x y =
    let i = FSTaintSet.compare x.taint y.taint in
    if i <> 0 then i else
      let i = Procname.compare x.proc_name y.proc_name in
      if i <> 0 then i else
        let i = Location.compare x.loc y.loc in
        if i <> 0 then i else
          trace_compare x.trace y.trace


  let string_of_location : Location.t -> string
  = fun loc -> 
    let fname = DB.source_file_to_string loc.Location.file in
    let pos = Location.to_string loc in
    F.fprintf F.str_formatter "%s:%s" fname pos;
    F.flush_str_formatter ()
   
  let pp_location : F.formatter -> t -> unit
  = fun fmt c ->
    F.fprintf fmt "%s" (string_of_location c.loc)

  let pp : F.formatter -> t -> unit
  = fun fmt c ->
    if Config.ropas_debug <= 1 then 
      F.fprintf fmt "%a at %a" FSTaintSet.pp c.taint pp_location c
    else
      match c.trace with 
      | Inter (_, pname, loc) ->
          let pname = Procname.to_string pname in
          F.fprintf fmt "%a at %a by call %s() at %s" 
            FSTaintSet.pp c.taint pp_location c pname (string_of_location loc)
      | Intra _ ->
          F.fprintf fmt "%a at %a" FSTaintSet.pp c.taint pp_location c

  let pp_element : F.formatter -> t -> unit
  = pp

  let get_location : t -> Location.t
  = fun c -> c.loc

  let get_trace : t -> trace
  = fun c -> c.trace

  let get_proc_name : t -> Procname.t
  = fun c -> c.proc_name

  let make proc_name loc taint =
    { proc_name; taint; loc; trace = Intra proc_name }

  let check c = not (FSTaintSet.is_unsafe c.taint)

  let subst c subst_map caller_pname callee_pname loc =
    match FSTaintSet.has_symbol c.taint, c.trace with
    | true, Intra _ ->
        { c with taint = FSTaintSet.subst c.taint subst_map;
                 trace = Inter (caller_pname, callee_pname, loc) }
    | true, Inter (_, callee_pname, loc) ->
        { c with taint = FSTaintSet.subst c.taint subst_map;
                 trace = Inter (caller_pname, callee_pname, loc) }
    | false, _ -> c

  let to_string c =
    pp F.str_formatter c;
    F.flush_str_formatter ()
end

module ConditionSet =
struct
  module PPSet = PrettyPrintable.MakePPSet (Condition)
  include AbstractDomain.FiniteSet (PPSet)

  let map f s = fold (fun e -> add (f e)) s empty

  let add_fs_safety pname loc taint cond =
    add (Condition.make pname loc taint) cond

  let subst x subst_map caller callee loc =
    map (fun c -> Condition.subst c subst_map caller callee loc) x

  let pp_summary : F.formatter -> t -> unit
  = fun fmt x ->
    let pp_sep fmt () = F.fprintf fmt ", @," in
    let pp_element fmt v = Condition.pp fmt v in
    F.fprintf fmt "@[<v 0>Safety conditions:@,";
    F.fprintf fmt "@[<hov 2>{ ";
    F.pp_print_list ~pp_sep pp_element fmt (elements x);
    F.fprintf fmt " }@]";
    F.fprintf fmt "@]"

  let pp : Format.formatter -> t -> unit
  = fun fmt x ->
    let pp_sep fmt () = F.fprintf fmt ", @," in
    let pp_element fmt v = Condition.pp fmt v in
    F.fprintf fmt "@[<v 2>Safety conditions :@,";
    F.fprintf fmt "@[<hov 1>{";
    F.pp_print_list ~pp_sep pp_element fmt (elements x);
    F.fprintf fmt " }@]";
    F.fprintf fmt "@]"
end

module Val =
struct
  include AbstractDomain.Pair4 (Itv) (FSTaintSet) (PowLoc) (ArrayBlk)

  type t = astate

  let bot : t
  = initial

  let rec joins : t list -> t
  = function
    | [] -> bot
    | [a] -> a
    | a :: b -> join a (joins b)

  let get_itv = fst

  let get_taint = snd

  let get_pow_loc = trd

  let get_array_blk = frt

  let get_all_locs : t -> PowLoc.t
  = fun (_, _, p, a) -> ArrayBlk.get_pow_loc a |> PowLoc.join p

  let top_itv : t
  = (Itv.top, FSTaintSet.bot, PowLoc.bot, ArrayBlk.bot)

  let pos_itv : t
  = (Itv.pos, FSTaintSet.bot, PowLoc.bot, ArrayBlk.bot)

  let nat_itv : t
  = (Itv.nat, FSTaintSet.bot, PowLoc.bot, ArrayBlk.bot)

  let of_int : int -> t
  = fun n -> (Itv.of_int n, FSTaintSet.bot, PowLoc.bot, ArrayBlk.bot)

  let of_taint t = (Itv.bot, t, PowLoc.bot, ArrayBlk.bot)

  let of_pow_loc : PowLoc.t -> t
  = fun x -> (Itv.bot, FSTaintSet.bot, x, ArrayBlk.bot)

  let of_array_blk : ArrayBlk.astate -> t
  = fun a -> (Itv.bot, FSTaintSet.bot, PowLoc.bot, a)

  let zero : t
  = of_int 0

  let make_sym pname i =
    let itv_v = Itv.make_sym pname i in
    let i = i + 2 in          (* TODO: return i on Itv.make_sym *)
    let (t_v, i) = FSTaintSet.make_sym pname i in
    ((itv_v, t_v, PowLoc.bot, ArrayBlk.bot), i)

  let unknown_bit : t -> t
  = fun (_, t, x, a) -> (Itv.top, t, x, a)

  let neg : t -> t
  = fun (n, t, x, a) -> (Itv.neg n, t, x, a)

  let lnot : t -> t
  = fun (n, t, x, a) -> (Itv.lnot n, t, x, a)

  let lift_bop_func
  = fun f (n1, t1, _, _) (n2, t2, _, _) ->
    (f n1 n2, FSTaintSet.join t1 t2, PowLoc.bot, ArrayBlk.bot)

  let plus : t -> t -> t
  = fun (n1, t1, _, a1) (n2, t2, _, _) ->
    let n = Itv.plus n1 n2 in
    let t = FSTaintSet.join t1 t2 in
    let a = ArrayBlk.plus_offset a1 n2 in
    (n, t, PowLoc.bot, a)

  let minus : t -> t -> t
  = fun (n1, t1, _, a1) (n2, t2, _, a2) ->
    let n = Itv.join (Itv.minus n1 n2) (ArrayBlk.diff a1 a2) in
    let t = FSTaintSet.join t1 t2 in
    let a = ArrayBlk.minus_offset a1 n2 in
    (n, t, PowLoc.bot, a)

  let mult : t -> t -> t
  = lift_bop_func Itv.mult

  let div : t -> t -> t
  = lift_bop_func Itv.div

  let mod_sem : t -> t -> t
  = lift_bop_func Itv.mod_sem

  let shiftlt : t -> t -> t
  = lift_bop_func Itv.shiftlt

  let shiftrt : t -> t -> t
  = lift_bop_func Itv.shiftrt

  let lt_sem : t -> t -> t
  = lift_bop_func Itv.lt_sem

  let gt_sem : t -> t -> t
  = lift_bop_func Itv.gt_sem

  let le_sem : t -> t -> t
  = lift_bop_func Itv.le_sem

  let ge_sem : t -> t -> t
  = lift_bop_func Itv.ge_sem

  let eq_sem : t -> t -> t
  = lift_bop_func Itv.eq_sem

  let ne_sem : t -> t -> t
  = lift_bop_func Itv.ne_sem

  let land_sem : t -> t -> t
  = lift_bop_func Itv.land_sem

  let lor_sem : t -> t -> t
  = lift_bop_func Itv.lor_sem

  let lift_prune1 : (Itv.t -> Itv.t) -> t -> t
  = fun f (n, t, x, a) -> (f n, t, x, a)

  let lift_prune2
    : (Itv.t -> Itv.t -> Itv.t)
      -> (ArrayBlk.astate -> ArrayBlk.astate -> ArrayBlk.astate) -> t -> t -> t
  = fun f g (n1, t1, x1, a1) (n2, _, _, a2) -> (f n1 n2, t1, x1, g a1 a2)

  let prune_zero : t -> t
  = lift_prune1 Itv.prune_zero

  let prune_comp : Binop.t -> t -> t -> t
  = fun c -> lift_prune2 (Itv.prune_comp c) (ArrayBlk.prune_comp c)

  let prune_eq : t -> t -> t
  = lift_prune2 Itv.prune_eq ArrayBlk.prune_eq

  let prune_ne : t -> t -> t
  = lift_prune2 Itv.prune_ne ArrayBlk.prune_eq

  let plus_pi : t -> t -> t
  = fun (_, _, _, a1) (n2, _, _, _) ->
    (Itv.bot, FSTaintSet.bot, PowLoc.bot, ArrayBlk.plus_offset a1 n2)

  let minus_pi : t -> t -> t
  = fun (_, _, _, a1) (n2, _, _, _) ->
    (Itv.bot, FSTaintSet.bot, PowLoc.bot, ArrayBlk.minus_offset a1 n2)

  let minus_pp : t -> t -> t
  = fun (_, _, _, a1) (_, _, _, a2) ->
    (ArrayBlk.diff a1 a2, FSTaintSet.bot, PowLoc.bot, ArrayBlk.bot)

  let subst
  = fun (i, t, p, a) itv_subst_map taint_subst_map ->
    let i = Itv.subst i itv_subst_map in
    let t = FSTaintSet.subst t taint_subst_map in
    let a = ArrayBlk.subst a itv_subst_map in
    (i, t, p, a)

  let get_symbols : t -> Symbol.t list
  = fun (i, t, _, a) ->
    IList.flatten
      [Itv.get_symbols i;
       FSTaintSet.get_symbols t;
       ArrayBlk.get_symbols a]

  let normalize : t -> t
  = fun (i, t, l, a) -> (Itv.normalize i, t, l, ArrayBlk.normalize a)

  let pp_summary : F.formatter -> t -> unit
  = fun fmt (i, t, _, a) ->
    F.fprintf fmt "(%a, %a, %a)" Itv.pp i FSTaintSet.pp t ArrayBlk.pp a

  let add_taint loc (i, t, p, a) = (i, FSTaintSet.add_taint loc t, p, a)
end

module Stack =
struct
  module PPMap =
  struct
    module Ord = struct include Loc let pp_key = pp end
    include PrettyPrintable.MakePPMap (Ord)

    let pp_collection
      : pp_item:(F.formatter -> 'a -> unit) -> F.formatter -> 'a list -> unit
    = fun ~pp_item fmt c ->
      let pp_sep fmt () = F.fprintf fmt ",@," in
      F.pp_print_list ~pp_sep pp_item fmt c

    let pp
      : pp_value:(F.formatter -> 'a -> unit) -> F.formatter -> 'a t -> unit
    = fun ~pp_value fmt m ->
      let pp_item fmt (k, v) =
        F.fprintf fmt "%a -> %a" Ord.pp_key k pp_value v
      in
      F.fprintf fmt "@[<v 2>{ ";
      pp_collection ~pp_item fmt (bindings m);
      F.fprintf fmt " }@]"
  end

  include AbstractDomain.Map (PPMap) (Val)

  let find : Loc.t -> astate -> Val.t
  = fun l m ->
    try find l m with
    | Not_found -> Val.bot

  let find_set : PowLoc.t -> astate -> Val.t
  = fun locs mem ->
    let find_join loc acc = Val.join acc (find loc mem) in
    PowLoc.fold find_join locs Val.bot

  let strong_update : PowLoc.t -> Val.astate -> astate -> astate
  = fun locs v mem ->
    PowLoc.fold (fun x -> add x v) locs mem

  let weak_update : PowLoc.t -> Val.astate -> astate -> astate
  = fun locs v mem ->
    PowLoc.fold (fun x -> add x (Val.join v (find x mem))) locs mem

  let pp_summary : F.formatter -> astate -> unit
  = fun fmt mem ->
    let pp_not_logical_var k v =
      if Loc.is_logical_var k then () else
        F.fprintf fmt "%a -> %a@," Loc.pp k Val.pp_summary v
    in
    iter pp_not_logical_var mem
end

module Heap =
struct
  module PPMap =
  struct
    module Ord = struct include Loc let pp_key = pp end
    include PrettyPrintable.MakePPMap (Ord)

    let pp_collection
      : pp_item:(F.formatter -> 'a -> unit) -> F.formatter -> 'a list -> unit
    = fun ~pp_item fmt c ->
      let pp_sep fmt () = F.fprintf fmt ",@," in
      F.pp_print_list ~pp_sep pp_item fmt c

    let pp : pp_value:(F.formatter -> 'a -> unit) -> F.formatter -> 'a t -> unit
    = fun ~pp_value fmt m ->
      let pp_item fmt (k, v) =
        F.fprintf fmt "%a -> %a" Ord.pp_key k pp_value v
      in
      F.fprintf fmt "@[<v 2>{ ";
      pp_collection ~pp_item fmt (bindings m);
      F.fprintf fmt " }@]"
  end

  include AbstractDomain.Map (PPMap) (Val)

  let find : Loc.t -> astate -> Val.t
  = fun l m ->
    try find l m with
    | Not_found -> Val.bot

  let find_set : PowLoc.t -> astate -> Val.t
  = fun locs mem ->
    let find_join loc acc = Val.join acc (find loc mem) in
    PowLoc.fold find_join locs Val.bot

  let strong_update : PowLoc.t -> Val.t -> astate -> astate
  = fun locs v mem ->
    PowLoc.fold (fun x -> add x v) locs mem

  let weak_update : PowLoc.t -> Val.t -> astate -> astate
  = fun locs v mem ->
    PowLoc.fold (fun x -> add x (Val.join v (find x mem))) locs mem

  let pp_summary : F.formatter -> astate -> unit
  = fun fmt mem ->
    let pp_map fmt (k, v) = F.fprintf fmt "%a -> %a" Loc.pp k Val.pp_summary v in
    F.fprintf fmt "@[<v 2>{ ";
    F.pp_print_list pp_map fmt (bindings mem);
    F.fprintf fmt " }@]"

  let get_symbols : astate -> Symbol.t list
  = fun mem ->
    IList.flatten (IList.map (fun (_, v) -> Val.get_symbols v) (bindings mem))

  let get_return : astate -> Val.t
  = fun mem ->
    let mem = filter (fun l _ -> Loc.is_return l) mem in
    if is_empty mem then Val.bot else snd (choose mem)
end

module Alias =
struct
  module M = Map.Make (Ident)

  type t = Pvar.t M.t

  type astate = t

  let initial : t
  = M.empty

  let (<=) : lhs:t -> rhs:t -> bool
  = fun ~lhs ~rhs ->
    let is_in_rhs k v =
      match M.find k rhs with
      | v' -> Pvar.equal v v'
      | exception Not_found -> false
    in
    M.for_all is_in_rhs lhs

  let join : t -> t -> t
  = fun x y ->
    let join_v _ v1_opt v2_opt =
      match v1_opt, v2_opt with
      | None, None -> None
      | Some v, None
      | None, Some v -> Some v
      | Some v1, Some v2 -> if Pvar.equal v1 v2 then Some v1 else assert false
    in
    M.merge join_v x y

  let widen : prev:t -> next:t -> num_iters:int -> t
  = fun ~prev ~next ~num_iters:_ -> join prev next

  let pp : F.formatter -> t -> unit
  = fun fmt x ->
    let pp_sep fmt () = F.fprintf fmt ", @," in
    let pp1 fmt (k, v) =
      F.fprintf fmt "%a=%a" (Ident.pp pe_text) k (Pvar.pp pe_text) v
    in
    (* F.fprintf fmt "@[<v 0>Logical Variables :@,"; *)
    F.fprintf fmt "@[<hov 2>{ @,";
    F.pp_print_list ~pp_sep pp1 fmt (M.bindings x);
    F.fprintf fmt " }@]";
    F.fprintf fmt "@]"

  let load : Ident.t -> Exp.t -> t -> t
  = fun id exp m ->
    match exp with
    | Exp.Lvar x -> M.add id x m
    | _ -> m

  let store : Exp.t -> Exp.t -> t -> t
  = fun e _ m ->
    match e with
    | Exp.Lvar x -> M.filter (fun _ y -> not (Pvar.equal x y)) m
    | _ -> m

  let find : Ident.t -> t -> Pvar.t option
  = fun k m -> try Some (M.find k m) with Not_found -> None
end

module Mem =
struct
  include AbstractDomain.Pair3 (Stack) (Heap) (Alias)

  type t = astate

  let pp : F.formatter -> t -> unit
  = fun fmt (stack, heap, _) ->
    F.fprintf fmt "Stack :@,";
    F.fprintf fmt "%a@," Stack.pp stack;
    F.fprintf fmt "Heap :@,";
    F.fprintf fmt "%a" Heap.pp heap

  let pp_summary : F.formatter -> t -> unit
  = fun fmt (_, heap, _) ->
    F.fprintf fmt "@[<v 0>Parameters :@,";
    F.fprintf fmt "%a" Heap.pp_summary heap ;
    F.fprintf fmt "@]"

  let find_stack : Loc.t -> t -> Val.t
  = fun k m -> Stack.find k (fst m)

  let find_stack_set : PowLoc.t -> t -> Val.t
  = fun k m -> Stack.find_set k (fst m)

  let find_heap : Loc.t -> t -> Val.t
  = fun k m -> Heap.find k (snd m)

  let find_heap_set : PowLoc.t -> t -> Val.t
  = fun k m -> Heap.find_set k (snd m)

  let find_alias : Ident.t -> t -> Pvar.t option
  = fun k m -> Alias.find k (trd m)

  let load_alias : Ident.t -> Exp.t -> t -> t
  = fun id e m -> (fst m, snd m, Alias.load id e (trd m))

  let store_alias : Exp.t -> Exp.t -> t -> t
  = fun e1 e2 m -> (fst m, snd m, Alias.store e1 e2 (trd m))

  let add_stack : Loc.t -> Val.t -> t -> t
  = fun k v m -> (Stack.add k v (fst m), snd m, trd m)

  let add_heap : Loc.t -> Val.t -> t -> t
  = fun k v m -> (fst m, Heap.add k v (snd m), trd m)

  let strong_update_stack : PowLoc.t -> Val.t -> t -> t
  = fun p v m -> (Stack.strong_update p v (fst m), snd m, trd m)

  let strong_update_heap : PowLoc.t -> Val.t -> t -> t
  = fun p v m -> (fst m, Heap.strong_update p v (snd m), trd m)

  let weak_update_stack : PowLoc.t -> Val.t -> t -> t
  = fun p v m -> (Stack.weak_update p v (fst m), snd m, trd m)

  let weak_update_heap : PowLoc.t -> Val.t -> t -> t
  = fun p v m -> (fst m, Heap.weak_update p v (snd m), trd m)

  let get_heap_symbols : t -> Symbol.t list
  = fun (_, m, _) -> Heap.get_symbols m

  let get_return : t -> Val.t
  = fun (_, m, _) -> Heap.get_return m

  let can_strong_update : PowLoc.t -> bool
  = fun ploc ->
    if PowLoc.cardinal ploc = 1 then Loc.is_var (PowLoc.choose ploc) else false

  let update_mem : PowLoc.t -> Val.t -> t -> t
  = fun ploc v s ->
    if can_strong_update ploc
    then strong_update_heap ploc v s
    else weak_update_heap ploc v s
end

module Summary =
struct
  type t = Mem.t * Mem.t * ConditionSet.t

  let get_input : t -> Mem.t
  = fst3

  let get_output : t -> Mem.t
  = snd3

  let get_cond_set : t -> ConditionSet.t
  = trd3

  let get_symbols : t -> Symbol.t list
  = fun s -> Mem.get_heap_symbols (get_input s)

  let get_return : t -> Val.t
  = fun s -> Mem.get_return (get_output s)

  let pp_symbols : F.formatter -> t -> unit
  = fun fmt s ->
    let pp_sep fmt () = F.fprintf fmt ", @," in
    F.fprintf fmt "@[<hov 2>Symbols: {";
    F.pp_print_list ~pp_sep Symbol.pp fmt (get_symbols s);
    F.fprintf fmt "}@]"

  let pp_symbol_map : F.formatter -> t -> unit
  = fun fmt s -> Mem.pp_summary fmt (get_input s)

  let pp_return : F.formatter -> t -> unit
  = fun fmt s -> F.fprintf fmt "Return value: %a" Val.pp_summary (get_return s)

  let pp_summary : F.formatter -> t -> unit
  = fun fmt s ->
    F.fprintf fmt "%a@,%a@,%a" pp_symbol_map s pp_return s
      ConditionSet.pp_summary (get_cond_set s)

  let pp : F.formatter -> t -> unit
  = fun fmt (entry_mem, exit_mem, condition_set) ->
    F.fprintf fmt "%a@,%a@,%a@"
      Mem.pp entry_mem Mem.pp exit_mem ConditionSet.pp condition_set
end

include Mem
