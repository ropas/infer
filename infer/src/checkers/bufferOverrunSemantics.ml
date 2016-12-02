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

module Domain = BufferOverrunDomain
module Make(CFG : ProcCfg.S) =
struct 
  exception Not_implemented 

  let eval_const : Const.t -> Domain.Val.astate = function 
    | Const.Cint intlit -> 
        Domain.Val.of_int (IntLit.to_int intlit)
    | Const.Cfloat f -> f |> int_of_float |> Domain.Val.of_int 
    | _ -> Domain.Val.bot (* TODO *)

  let sizeof_ikind : Typ.ikind -> int = function 
    | Typ.IChar | Typ.ISChar | Typ.IUChar | Typ.IBool -> 1
    | Typ.IInt | Typ.IUInt -> 4
    | Typ.IShort | Typ.IUShort -> 2
    | Typ.ILong | Typ.IULong -> 4
    | Typ.ILongLong | Typ.IULongLong -> 8
    | Typ.I128 | Typ.IU128 -> 16

  let sizeof_fkind : Typ.fkind -> int = function
    | Typ.FFloat -> 4
    | Typ.FDouble | Typ.FLongDouble -> 8

  (* NOTE: assume 32bit machine *)
  let rec sizeof : Typ.t -> int = function
    | Typ.Tint ikind -> sizeof_ikind ikind
    | Typ.Tfloat fkind -> sizeof_fkind fkind
    | Typ.Tvoid -> 1
    | Typ.Tptr (_, _) -> 4
    | Typ.Tstruct _ -> 4 (* TODO *)
    | Typ.Tarray (typ, Some ilit) -> (sizeof typ) * (IntLit.to_int ilit)
    | _ -> 4

  let rec eval : Exp.t -> Domain.Mem.astate -> Location.t -> Domain.Val.astate
  = fun exp mem loc ->
    match exp with
    | Exp.Var id -> Domain.Mem.find_stack (Var.of_id id |> Loc.of_var) mem
    | Exp.Lvar pvar -> 
        let ploc = pvar |> Loc.of_pvar |> PowLoc.singleton in
        let arr = Domain.Mem.find_stack_set ploc mem in
        ploc |> Domain.Val.of_pow_loc |> Domain.Val.join arr
    | Exp.UnOp (uop, e, _) -> eval_unop uop e mem loc
    | Exp.BinOp (bop, e1, e2) -> eval_binop bop e1 e2 mem loc
    | Exp.Const c -> eval_const c
    | Exp.Cast (_, e) -> eval e mem loc
    | Exp.Lfield (e, fn, _) ->
        eval e mem loc |> Domain.Val.get_all_locs |> flip PowLoc.append_field fn |> Domain.Val.of_pow_loc
    | Exp.Lindex (e1, _) -> 
        let arr = eval e1 mem loc in  (* must have array blk *)
(*        let idx = eval e2 mem loc in*)
        let ploc = arr |> Domain.Val.get_array_blk |> ArrayBlk.get_pow_loc in
        (* if nested array, add the array blk *)
        let arr = Domain.Mem.find_heap_set ploc mem in
        Domain.Val.join (Domain.Val.of_pow_loc ploc) arr
    | Exp.Sizeof (typ, _, _) -> Domain.Val.of_int (sizeof typ)
    | Exp.Exn _ 
    | Exp.Closure _ -> Domain.Val.bot
 and eval_unop
    : Unop.t -> Exp.t -> Domain.Mem.astate -> Location.t -> Domain.Val.astate
  = fun unop e mem loc ->
    let v = eval e mem loc in
    match unop with
    | Unop.Neg -> Domain.Val.neg v
    | Unop.BNot -> Domain.Val.unknown_bit v
    | Unop.LNot -> Domain.Val.lnot v

  and eval_binop
    : Binop.t -> Exp.t -> Exp.t -> Domain.Mem.astate -> Location.t
      -> Domain.Val.astate
  = fun binop e1 e2 mem loc ->
    let v1 = eval e1 mem loc in
    let v2 = eval e2 mem loc in
    match binop with
    | Binop.PlusA ->
        Domain.Val.join (Domain.Val.plus v1 v2) (Domain.Val.plus_pi v1 v2)
    | Binop.PlusPI -> Domain.Val.plus_pi v1 v2
    | Binop.MinusA ->
        Domain.Val.joins
          [ Domain.Val.minus v1 v2
          ; Domain.Val.minus_pi v1 v2
          ; Domain.Val.minus_pp v1 v2 ]
    | Binop.MinusPI -> Domain.Val.minus_pi v1 v2
    | Binop.MinusPP -> Domain.Val.minus_pp v1 v2
    | Binop.Mult -> Domain.Val.mult v1 v2
    | Binop.Div -> Domain.Val.div v1 v2
    | Binop.Mod -> Domain.Val.mod_sem v1 v2
    | Binop.Shiftlt -> Domain.Val.shiftlt v1 v2
    | Binop.Shiftrt -> Domain.Val.shiftrt v1 v2
    | Binop.Lt -> Domain.Val.lt_sem v1 v2
    | Binop.Gt -> Domain.Val.gt_sem v1 v2
    | Binop.Le -> Domain.Val.le_sem v1 v2
    | Binop.Ge -> Domain.Val.ge_sem v1 v2
    | Binop.Eq -> Domain.Val.eq_sem v1 v2
    | Binop.Ne -> Domain.Val.ne_sem v1 v2
    | Binop.BAnd
    | Binop.BXor
    | Binop.BOr -> Domain.Val.unknown_bit v1
    | Binop.LAnd -> Domain.Val.land_sem v1 v2
    | Binop.LOr -> Domain.Val.lor_sem v1 v2
    | Binop.PtrFld -> raise Not_implemented

  let get_allocsite pdesc node inst_num dimension =
    Procname.to_string (Procdesc.get_attributes pdesc).ProcAttributes.proc_name
    ^ "-" ^ string_of_int (CFG.underlying_id node) ^ "-" ^ string_of_int inst_num ^ "-" ^ string_of_int dimension
    |> Allocsite.make

  let eval_array_alloc
    : Procdesc.t -> CFG.node -> Typ.t -> Itv.astate -> Itv.astate -> int -> int
      -> Domain.Val.astate
  = fun pdesc node typ offset size inst_num dimension ->
    let allocsite = get_allocsite pdesc node inst_num dimension in
    let stride = sizeof typ |> Itv.of_int in
    let nullpos = Itv.nat in
    ArrayBlk.make allocsite offset size stride nullpos
    |> Domain.Val.of_array_blk

  let prune_unop
    : Exp.t -> Domain.Mem.astate -> Domain.Mem.astate
  = fun e mem ->
    match e with
    | Exp.Var x ->
        (match Domain.Mem.find_alias x mem with
         | Some x' ->
             let lv = Loc.of_pvar x' in
             let v = Domain.Mem.find_heap lv mem in
             let v' = Domain.Val.prune v Domain.Val.zero in
             Domain.Mem.update_mem (PowLoc.singleton lv) v' mem
         | None -> mem)
    | Exp.UnOp (Unop.LNot, Exp.Var x, _) ->
        (match Domain.Mem.find_alias x mem with
         | Some x' ->
             let lv = Loc.of_pvar x' in
             let v = Domain.Mem.find_heap lv mem in
             let itv_v =
               if Itv.is_bot (Domain.Val.get_itv v) then Itv.bot else
                 Domain.Val.get_itv Domain.Val.zero
             in
             let v' = (itv_v,
                       Domain.Val.get_pow_loc v,
                       Domain.Val.get_array_blk v) in
             Domain.Mem.update_mem (PowLoc.singleton lv) v' mem
         | None -> mem)
    | _ -> mem

  let prune_binop_left
    : Exp.t -> Location.t -> Domain.Mem.astate
      -> Domain.Mem.astate
  = fun e loc mem ->
    match e with
    | Exp.BinOp (Binop.Lt as comp, Exp.Var x, e')
    | Exp.BinOp (Binop.Gt as comp, Exp.Var x, e')
    | Exp.BinOp (Binop.Le as comp, Exp.Var x, e')
    | Exp.BinOp (Binop.Ge as comp, Exp.Var x, e') ->
        (match Domain.Mem.find_alias x mem with
         | Some x' ->
             let lv = Loc.of_pvar x' in
             let v = Domain.Mem.find_heap lv mem in
             let v' = Domain.Val.prune_comp comp v (eval e' mem loc) in
             Domain.Mem.update_mem (PowLoc.singleton lv) v' mem
         | None -> mem)
    | Exp.BinOp (Binop.Eq, Exp.Var x, e') ->
        (match Domain.Mem.find_alias x mem with
         | Some x' ->
             let lv = Loc.of_pvar x' in
             let v = Domain.Mem.find_heap lv mem in
             let v' = Domain.Val.prune_eq v (eval e' mem loc) in
             Domain.Mem.update_mem (PowLoc.singleton lv) v' mem
         | None -> mem)
    | Exp.BinOp (Binop.Ne, Exp.Var x, e') ->
        (match Domain.Mem.find_alias x mem with
         | Some x' ->
             let lv = Loc.of_pvar x' in
             let v = Domain.Mem.find_heap lv mem in
             let v' = Domain.Val.prune_ne v (eval e' mem loc) in
             Domain.Mem.update_mem (PowLoc.singleton lv) v' mem
         | None -> mem)
    | _ -> mem

  let comp_rev : Binop.t -> Binop.t
  = function
    | Binop.Lt -> Binop.Gt
    | Binop.Gt -> Binop.Lt
    | Binop.Le -> Binop.Ge
    | Binop.Ge -> Binop.Le
    | Binop.Eq -> Binop.Eq
    | Binop.Ne -> Binop.Ne
    | _ -> assert (false)

  let comp_not : Binop.t -> Binop.t
  = function
    | Binop.Lt -> Binop.Ge
    | Binop.Gt -> Binop.Le
    | Binop.Le -> Binop.Gt
    | Binop.Ge -> Binop.Lt
    | Binop.Eq -> Binop.Ne
    | Binop.Ne -> Binop.Eq
    | _ -> assert (false)

  let prune_binop_right
    : Exp.t -> Location.t -> Domain.Mem.astate
      -> Domain.Mem.astate
  = fun e loc mem ->
    match e with
    | Exp.BinOp (Binop.Lt as c, e', Exp.Var x)
    | Exp.BinOp (Binop.Gt as c, e', Exp.Var x)
    | Exp.BinOp (Binop.Le as c, e', Exp.Var x)
    | Exp.BinOp (Binop.Ge as c, e', Exp.Var x)
    | Exp.BinOp (Binop.Eq as c, e', Exp.Var x)
    | Exp.BinOp (Binop.Ne as c, e', Exp.Var x) ->
        prune_binop_left (Exp.BinOp (comp_rev c, Exp.Var x, e')) loc mem
    | _ -> mem

  let rec prune
    : Exp.t -> Location.t -> Domain.Mem.astate
      -> Domain.Mem.astate
  = fun e loc mem ->
    let mem =
      mem
      |> prune_unop e
      |> prune_binop_left e loc
      |> prune_binop_right e loc
    in
    match e with
    | Exp.BinOp (Binop.Ne, e, Exp.Const (Const.Cint i)) when IntLit.iszero i ->
        prune e loc mem
    | Exp.BinOp (Binop.Eq, e, Exp.Const (Const.Cint i)) when IntLit.iszero i ->
        prune (Exp.UnOp (Unop.LNot, e, None)) loc mem
    | Exp.UnOp (Unop.Neg, Exp.Var x, _) -> prune (Exp.Var x) loc mem
    | Exp.BinOp (Binop.LAnd, e1, e2) ->
        mem |> prune e1 loc |> prune e2 loc
    | Exp.UnOp (Unop.LNot, Exp.BinOp (Binop.LOr, e1, e2), t) ->
        mem
        |> prune (Exp.UnOp (Unop.LNot, e1, t)) loc
        |> prune (Exp.UnOp (Unop.LNot, e2, t)) loc
    | Exp.UnOp (Unop.LNot, Exp.BinOp (Binop.Lt as c, e1, e2), _)
    | Exp.UnOp (Unop.LNot, Exp.BinOp (Binop.Gt as c, e1, e2), _)
    | Exp.UnOp (Unop.LNot, Exp.BinOp (Binop.Le as c, e1, e2), _)
    | Exp.UnOp (Unop.LNot, Exp.BinOp (Binop.Ge as c, e1, e2), _)
    | Exp.UnOp (Unop.LNot, Exp.BinOp (Binop.Eq as c, e1, e2), _)
    | Exp.UnOp (Unop.LNot, Exp.BinOp (Binop.Ne as c, e1, e2), _) ->
        prune (Exp.BinOp (comp_not c, e1, e2)) loc mem
    | _ -> mem

  let get_formals : Procdesc.t -> (Pvar.t * Typ.t) list
  = fun pdesc ->
    let proc_name = Procdesc.get_proc_name pdesc in
    Procdesc.get_formals pdesc |> IList.map (fun (name, typ) -> (Pvar.mk name proc_name, typ))

  let get_matching_pairs : Tenv.t -> Domain.Val.astate -> Domain.Val.astate -> Typ.t -> Domain.Mem.astate -> Domain.Mem.astate -> (Itv.Bound.t * Itv.Bound.t) list
  = fun tenv formal actual typ caller_mem callee_mem ->
    let add_pair itv1 itv2 l =
      if itv1 <> Itv.bot && itv2 <> Itv.bot then
        (Itv.lb itv1, Itv.lb itv2) 
        :: (Itv.ub itv1, Itv.ub itv2) :: l
      else l
    in
    let add_pair_val formal actual = 
      let formal_itv = Domain.Val.get_itv formal in
      let actual_itv = Domain.Val.get_itv actual in
      let formal_arr = Domain.Val.get_array_blk formal in
      let actual_arr = Domain.Val.get_array_blk actual in
      let formal_arr_offset = formal_arr |> ArrayBlk.offsetof in
      let formal_arr_size = formal_arr |> ArrayBlk.sizeof in
      let actual_arr_offset = actual_arr |> ArrayBlk.offsetof in
      let actual_arr_size = actual_arr |> ArrayBlk.sizeof in
      add_pair formal_itv actual_itv [] 
      |> add_pair formal_arr_offset actual_arr_offset 
      |> add_pair formal_arr_size actual_arr_size
    in
    let pairs = add_pair_val formal actual in
    match typ with 
      Typ.Tptr (Typ.Tstruct typename, _) ->
      begin
        match Tenv.lookup tenv typename with
          Some str -> 
            IList.fold_left (fun pairs (fn, _, _) ->
              let formal_loc = formal |> Domain.Val.get_all_locs in
              let actual_loc = actual |> Domain.Val.get_all_locs in
              let formal_fields = PowLoc.append_field formal_loc fn in
              let actual_fields = PowLoc.append_field actual_loc fn in
              let formal = Domain.Mem.find_heap_set formal_fields callee_mem in
              let actual = Domain.Mem.find_heap_set actual_fields caller_mem in
              (* (get_matching_pairs tenv formal actual typ caller_mem callee_mem) @ pairs *)
              add_pair_val formal actual @ pairs
            ) pairs str.StructTyp.fields
        | _ -> pairs
      end
    | _ -> pairs

  let get_subst_map tenv callee_pdesc params caller_mem callee_entry_mem loc =
    let pairs = 
      IList.fold_left2 (fun l (formal, typ) (actual,_) ->
        let formal = Domain.Mem.find_heap (Loc.of_pvar formal) callee_entry_mem in
        let actual = eval actual caller_mem loc in
        (get_matching_pairs tenv formal actual typ caller_mem callee_entry_mem) @ l
      ) [] (get_formals callee_pdesc) params
    in
    IList.fold_left (fun map (formal, actual) ->
      match formal with 
      | Itv.Bound.Linear (0, se1) when Itv.SymExp.cardinal se1 > 0 ->
          let (symbol, coeff) = Itv.SymExp.choose se1 in
          if coeff = 1 then
            Itv.SubstMap.add symbol actual map
          else (* impossible *) map
      | _ -> (* impossible *) map) Itv.SubstMap.empty pairs
end 
