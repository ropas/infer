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
open BufferOverrunSemantics

module F = Format
module L = Logging

module Summary = Summary.Make (struct
    type summary = BufferOverrunDomain.summary 

    let update_payload astate payload = 
      { payload with Specs.buffer_overrun = Some astate }

    let read_from_payload payload =
      payload.Specs.buffer_overrun
  end)

module SubstMap = Map.Make(struct type t = Itv.Bound.t let compare = Itv.Bound.compare end)

module TransferFunctions (CFG : ProcCfg.S) = 
struct
  module CFG = CFG
  module Domain = BufferOverrunDomain
  module Semantics = BufferOverrunSemantics.Make(CFG)
  type extras = Procname.t -> Procdesc.t option
  exception Not_implemented 

 
  (* heuristic *)
  let get_malloc_info = function
    | Exp.BinOp (Binop.Mult, Exp.Sizeof (typ, _, _), ((Exp.Const _) as size))
    | Exp.BinOp (Binop.Mult, ((Exp.Const _) as size), Exp.Sizeof (typ, _, _)) -> (typ, size)
    | Exp.Sizeof (typ, _, _) -> (typ, Exp.one)
    | x -> (Typ.Tint Typ.IChar, x)

  let model_malloc pdesc ret params node mem = 
    match ret with 
      Some (id, _) -> 
        let (typ, size) = get_malloc_info (IList.hd params |> fst) in
        let size = Semantics.eval size mem (CFG.loc node) |> Domain.Val.get_itv in
        Domain.Mem.add_stack (Loc.of_id id) (Semantics.eval_array_alloc pdesc node typ Itv.zero size 0 1) mem
    | _ -> mem

  let model_realloc pdesc ret params node mem = 
    match ret with 
      Some (_, _) -> model_malloc pdesc ret (IList.tl params) node mem
    | _ -> mem

  let model_positive_itv ret mem =
    match ret with 
      Some (id, _) -> Domain.Mem.add_stack (Loc.of_id id) Domain.Val.pos_itv mem
    | _ -> mem 

  let handle_unknown_call pdesc ret callee_pname params node mem =
    match Procname.get_method callee_pname with
    | "malloc" | "__new_array" -> model_malloc pdesc ret params node mem
    | "realloc" -> model_realloc pdesc ret params node mem
    | "strlen" -> model_positive_itv ret mem
    | _ ->
        (match ret with
           Some (id, _) ->
             Domain.Mem.add_stack (Loc.of_id id) Domain.Val.top_itv mem
         | None -> mem)

  let rec declare_array pdesc node loc typ len inst_num dimension mem = 
    let size = IntLit.to_int len |> Itv.of_int in
    let arr = Semantics.eval_array_alloc pdesc node typ Itv.zero size inst_num dimension in
    let mem = if dimension = 1 then Domain.Mem.add_stack loc arr mem else Domain.Mem.add_heap loc arr mem 
    in
    let loc = Loc.of_allocsite (Semantics.get_allocsite pdesc node inst_num dimension) in
    match typ with 
      Typ.Tarray (typ, Some len) -> 
        declare_array pdesc node loc typ len inst_num (dimension + 1) mem
    | _ -> mem

  let declare_symbolic_array pdesc tenv node loc typ inst_num dimension mem =
    let (offset, size) = (Itv.get_new_sym (), Itv.get_new_sym ()) in
    let mem = Domain.Mem.add_heap loc (Semantics.eval_array_alloc pdesc node typ offset size inst_num dimension) mem in
    match typ with 
      Typ.Tstruct typename ->
      begin
        match Tenv.lookup tenv typename with
          Some str -> 
            IList.fold_left (fun mem (fn, typ, _) ->
              let loc = Domain.Mem.find_heap loc mem |> Domain.Val.get_all_locs |> PowLoc.choose in
              let field = Loc.append_field loc fn in
              match typ with 
                Typ.Tint _ | Typ.Tfloat _ -> 
                  Domain.Mem.add_heap field (Domain.Val.get_new_sym ()) mem
              | Typ.Tptr (typ, _) -> 
                  Domain.Mem.add_heap field (Semantics.eval_array_alloc pdesc node typ offset size inst_num dimension) mem
                  (*declare_symbolic_array pdesc tenv node field typ (inst_num+1) dimension mem*)
              | _ -> mem
            ) mem str.StructTyp.fields
        | _ -> mem
      end
    | _ -> mem

     
  let can_strong_update ploc =
    if PowLoc.cardinal ploc = 1 then 
      let lv = PowLoc.choose ploc in
      Loc.is_var lv 
    else false

  let update_mem : PowLoc.t -> Domain.Val.t -> Domain.Mem.astate -> Domain.Mem.astate
  = fun ploc v s ->
    if can_strong_update ploc then Domain.Mem.strong_update_heap ploc v s
    else Domain.Mem.weak_update_heap ploc v s

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
             update_mem (PowLoc.singleton lv) v' mem
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
             update_mem (PowLoc.singleton lv) v' mem
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
             let v' = Domain.Val.prune_comp comp v (Semantics.eval e' mem loc) in
             update_mem (PowLoc.singleton lv) v' mem
         | None -> mem)
    | Exp.BinOp (Binop.Eq, Exp.Var x, e') ->
        (match Domain.Mem.find_alias x mem with
         | Some x' ->
             let lv = Loc.of_pvar x' in
             let v = Domain.Mem.find_heap lv mem in
             let v' = Domain.Val.prune_eq v (Semantics.eval e' mem loc) in
             update_mem (PowLoc.singleton lv) v' mem
         | None -> mem)
    | Exp.BinOp (Binop.Ne, Exp.Var x, e') ->
        (match Domain.Mem.find_alias x mem with
         | Some x' ->
             let lv = Loc.of_pvar x' in
             let v = Domain.Mem.find_heap lv mem in
             let v' = Domain.Val.prune_ne v (Semantics.eval e' mem loc) in
             update_mem (PowLoc.singleton lv) v' mem
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

(*  let init_conditions astate = conditions := Domain.get_conds astate
  let get_conditions () = !conditions
*)
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
   
  let instantiate tenv callee_pdesc callee_pname params caller_mem summary loc =
(*    try *)
    (* TODO: remove fold_left2 exception catch by addressing variable arguments *)
    let (callee_entry_mem, callee_mem, _) = summary in
    prerr_endline "instantiate";
    match callee_pdesc with 
      Some pdesc ->
        let pairs = 
          IList.fold_left2 (fun l (formal, typ) (actual,_) ->
              let formal = Domain.Mem.find_heap (Loc.of_pvar formal) callee_entry_mem in
              let actual = Semantics.eval actual caller_mem loc in
              (get_matching_pairs tenv formal actual typ caller_mem callee_entry_mem) @ l
          ) [] (get_formals pdesc) params
        in
        let subst_map : Itv.Bound.t Itv.SubstMap.t = 
            IList.fold_left (fun map (formal, actual) ->
              match formal with 
              | Itv.Bound.Linear (0, se1) when Itv.SymExp.cardinal se1 > 0 ->
                  let (symbol, coeff) = Itv.SymExp.choose se1 in
                  if coeff = 1 then
                    Itv.SubstMap.add symbol actual map
                  else (* impossible *) map
              | _ -> (* impossible *) map) Itv.SubstMap.empty pairs
        in
        let ret_loc = Loc.of_pvar (Pvar.get_ret_pvar callee_pname) in
        let ret_val = Domain.Mem.find_heap ret_loc callee_mem in
        let new_ret_val = Domain.Val.subst ret_val subst_map in
        let new_mem = 
          Domain.Mem.add_heap ret_loc new_ret_val callee_mem
(*           , Domain.ConditionSet.subst callee_conds subst_map)*)
        in
(*        (if Config.debug_mode then 
        begin
          F.fprintf F.err_formatter "Callsite Mem : @.";
          Domain.Mem.pp F.err_formatter caller_mem; 
          F.fprintf F.err_formatter "@.@.";
          F.fprintf F.err_formatter "Old Conditions : @.";
          Domain.ConditionSet.pp F.err_formatter callee_conds;
          F.fprintf F.err_formatter "@.@.";
          F.fprintf F.err_formatter "New Conditions : @.";
          Domain.ConditionSet.pp F.err_formatter new_cond;
          F.fprintf F.err_formatter "@.@."
        end);*)
        new_mem
    | _ -> callee_mem
(*  with _ -> (callee_mem, callee_conds)*)

  let print_debug_info instr pre post = 
    if Config.debug_mode then 
    begin
      F.fprintf F.err_formatter "Pre-state : @.";
      Domain.pp F.err_formatter pre;
      F.fprintf F.err_formatter "@.@.";
      Sil.pp_instr pe_text F.err_formatter instr;
      F.fprintf F.err_formatter "@.@.";
      F.fprintf F.err_formatter "Post-state : @.";
      Domain.pp F.err_formatter post;
      F.fprintf F.err_formatter "@.@."
    end
   
  let exec_instr (mem as astate) { ProcData.pdesc; tenv; extras }
      node (instr : Sil.instr) =
(*    init_conditions astate;*)
    let output_astate =
      match instr with
      | Load (id, exp, _, loc) ->
(*          add_condition pdesc node exp loc mem;*)
          let locs = Semantics.eval exp mem loc |> Domain.Val.get_all_locs in
          let v = Domain.Mem.find_heap_set locs mem in
          Domain.Mem.add_stack (Loc.of_var (Var.of_id id)) v mem
          |> Domain.Mem.load_alias id exp
      | Store (exp1, _, exp2, loc) ->
(*          add_condition pdesc node exp1 loc mem;*)
(*          add_condition pdesc node exp2 loc mem;*)
          let locs = Semantics.eval exp1 mem loc |> Domain.Val.get_all_locs in
          update_mem locs (Semantics.eval exp2 mem loc) mem
          |> Domain.Mem.store_alias exp1 exp2
      | Prune (exp, loc, _, _) -> prune exp loc mem
      | Call (ret, Const (Cfun callee_pname), params, loc, _) ->
          let callee = extras callee_pname in
(*          let old_conds = get_conditions () in*)
          begin
            match Summary.read_summary tenv pdesc callee_pname with
            | Some summary ->
              let new_mem = instantiate tenv callee callee_pname params mem summary loc in
              let new_mem = 
                match ret with Some (id,_) -> 
                  Domain.Mem.add_stack (Loc.of_var (Var.of_id id))
                   (Domain.Mem.find_heap (Loc.of_pvar (Pvar.get_ret_pvar callee_pname)) new_mem) mem
                | _ -> mem
              in
              new_mem(*, Domain.ConditionSet.join old_conds new_conds)*)
            | None -> handle_unknown_call pdesc ret callee_pname params node mem
          end
      | Call (_, _, _, _, _) -> astate
      | Declare_locals (locals, _) ->
          (* static array allocation *)
          let mem = IList.fold_left (fun (mem, c) (pvar, typ) ->
              match typ with
                Typ.Tarray (typ, Some len) ->
                  (declare_array pdesc node (Loc.of_var (Var.of_pvar pvar)) typ len c 1 mem, c+1)
              | _ -> (mem, c)) (mem, 1) locals |> fst
          in
          (* formal parameters *)
          IList.fold_left (fun (mem, c) (pvar, typ) ->
              match typ with
                Typ.Tint _ -> (Domain.Mem.add_heap (Loc.of_pvar pvar) (Domain.Val.get_new_sym ()) mem, c+1)
              | Typ.Tptr (typ, _) ->
                  (declare_symbolic_array pdesc tenv node (Loc.of_pvar pvar) typ c 1 mem, c+1)
              | _ -> (mem, c) (* TODO *)) (mem, 0) (get_formals pdesc)
          |> fst
      | Remove_temps _ | Abstract _ | Nullify _ -> astate
    in
    print_debug_info instr astate output_astate;
    output_astate
end

module Analyzer =
  AbstractInterpreter.Make
    (ProcCfg.Normal)
    (Scheduler.ReversePostorder)
    (TransferFunctions)

(*module Interprocedural = Analyzer.Interprocedural (Summary)*)
module Domain = BufferOverrunDomain

module Report =
struct 
  module CFG = ProcCfg.Normal
  module Semantics = BufferOverrunSemantics.Make(CFG)
  module TransferFunctions = TransferFunctions(CFG)
let add_condition : Procdesc.t -> CFG.node -> Exp.t -> Location.t -> Domain.Mem.astate 
  -> Domain.ConditionSet.t -> Domain.ConditionSet.t
= fun pdesc node exp loc mem cond_set ->
  F.fprintf F.err_formatter "Add cond @ %a" Domain.Mem.pp mem;
  let array_access = 
    match exp with 
    | Exp.Var _ -> 
      Some (Semantics.eval exp mem loc |> Domain.Val.get_array_blk, 
            Itv.zero)
    | Exp.Lindex (e1, e2)
    | Exp.BinOp (Binop.PlusA, e1, e2) 
    | Exp.BinOp (Binop.MinusA, e1, e2) -> 
        Some (Semantics.eval e1 mem loc |> Domain.Val.get_array_blk, 
         Semantics.eval e2 mem loc |> Domain.Val.get_itv)
    | _ -> None
  in
  match array_access with
    Some (arr, idx) -> 
      let site = Semantics.get_allocsite pdesc node 0 0 in
      let size = ArrayBlk.sizeof arr in
      let offset = ArrayBlk.offsetof arr in
      let idx = Itv.plus offset idx in
      prerr_endline "Some array";
        (if Config.debug_mode then
           (F.fprintf F.err_formatter "@[<v 2>Add condition :@,";
            F.fprintf F.err_formatter "array: %a@," ArrayBlk.pp arr;
            F.fprintf F.err_formatter "  idx: %a@," Itv.pp idx;
            F.fprintf F.err_formatter "@]@."));
      if size <> Itv.bot && idx <> Itv.bot then 
      (
        prerr_endline "add bo safety";
         Domain.ConditionSet.add_bo_safety pdesc site ~size ~idx loc cond_set
      )
      else cond_set
  | None -> prerr_endline "None array"; cond_set

let collect ({ Callbacks.proc_desc; tenv; get_proc_desc } as callbacks) node (instrs: Sil.instr list) mem cond_set = 
  IList.fold_left (fun (cond_set, mem) instr ->
      F.fprintf F.err_formatter "Pre-state : @.";
      Domain.pp F.err_formatter mem;
      F.fprintf F.err_formatter "@.@.";
      Sil.pp_instr pe_text F.err_formatter instr;
      F.fprintf F.err_formatter "@.@.";
  match instr with
  | Sil.Load (id, exp, _, loc) -> 
      (add_condition proc_desc node exp loc mem cond_set, 
       TransferFunctions.exec_instr mem { pdesc = proc_desc; tenv = tenv; extras = get_proc_desc}
       node instr)
  | Sil.Store (exp1, _, exp2, loc) -> prerr_endline "store report"; 
      let cond_set = add_condition proc_desc node exp1 loc mem cond_set in
      F.fprintf F.err_formatter "Store Condition %a" Domain.ConditionSet.pp cond_set;
      (cond_set,
       TransferFunctions.exec_instr mem { pdesc = proc_desc; tenv = tenv; extras = get_proc_desc}
       node instr)
(*    add_condition pdesc node exp2 loc mem;*)
  | Sil.Call (ret, Const (Cfun callee_pname), params, loc, _) -> (cond_set, mem)
(*          let callee = extras callee_pname in
(*          let old_conds = get_conditions () in*)
          begin
            match Summary.read_summary tenv pdesc callee_pname with
            | Some summary ->
              let new_mem = instantiate tenv callee callee_pname params mem summary loc in
              let new_mem = 
                match ret with Some (id,_) -> 
                  Domain.Mem.add_stack (Loc.of_var (Var.of_id id))
                   (Domain.Mem.find_heap (Loc.of_pvar (Pvar.get_ret_pvar callee_pname)) new_mem) mem
                | _ -> mem
              in
              new_mem(*, Domain.ConditionSet.join old_conds new_conds)*)
            | None -> handle_unknown_call pdesc ret callee_pname params node mem
          end*)
  | _ -> (cond_set, mem)
  ) (cond_set, mem) instrs
|> fst
  let report_error : Tenv.t -> Procdesc.t -> Domain.ConditionSet.t -> unit 
  = fun tenv proc_desc conds -> 
    let proc_name = Procdesc.get_proc_name proc_desc in
    F.fprintf F.err_formatter "@.Conditions of %a :@,@," Procname.pp proc_name;
    Domain.ConditionSet.pp F.err_formatter conds;
    Domain.ConditionSet.iter (fun cond ->
        let safe = Domain.Condition.check cond in
        (* report symbol-related alarms only in debug mode *)
        if not safe then
        (
          Checkers.ST.report_error tenv
  (*          proc_name*)
            (Domain.Condition.get_proc_name cond)
  (*          proc_desc*)
            (Domain.Condition.get_proc_desc cond)
            "BUFFER-OVERRUN CHECKER"
            (Domain.Condition.get_location cond)
            (Domain.Condition.to_string cond))
        else ()) conds

  let my_report_error : Tenv.t -> Procdesc.t -> Domain.ConditionSet.t -> unit 
  = fun _ _ conds -> 
    F.fprintf F.err_formatter "@.== Alarms ==@.";
    let k = Domain.ConditionSet.fold (fun cond k ->
        let safe = Domain.Condition.check cond in
        (* report symbol-related alarms only in debug mode *)
        if not safe then
        (
          let loc = Domain.Condition.get_location cond in
          let loc_str = Location.to_string loc in
          let file_name = DB.source_file_to_string cond.loc.Location.file in
          let proc_name = Domain.Condition.get_proc_name cond |> Procname.to_string in
          F.fprintf F.err_formatter "@.%d. %s:%s: {%s} error: BUFFER-OVERRUN @. %s @." 
            k file_name loc_str proc_name (Domain.Condition.to_string cond);
          k + 1
        )
        else k) conds 1
    in
    F.fprintf F.err_formatter "@.@.%d issues found@." (k-1)
end

module Interprocedural = 
struct 
  let checker ({ Callbacks.get_proc_desc; proc_desc; proc_name; tenv; } as callback) extras =
    let analyze_ondemand_ _ pdesc =
      let cfg = Analyzer.CFG.from_pdesc pdesc in
      let inv_map = Analyzer.exec_pdesc (ProcData.make pdesc tenv extras) in
      let (entry_mem, exit_mem) = 
            (Analyzer.extract_post (Analyzer.CFG.id (Analyzer.CFG.start_node cfg)) inv_map,
             Analyzer.extract_post (Analyzer.CFG.id (Analyzer.CFG.exit_node cfg)) inv_map)
      in
      let cond_set = 
        Procdesc.fold_nodes (fun cond_set node ->
          let instrs = Analyzer.CFG.instr_ids node |> IList.map fst in 
          let pre = Analyzer.extract_pre (Analyzer.CFG.id node) inv_map in
          match pre with 
            Some mem -> Report.collect callback node instrs mem cond_set
          | _ -> cond_set) Domain.ConditionSet.empty proc_desc
      in
      F.fprintf F.err_formatter "Cond Set @ %a" Domain.ConditionSet.pp cond_set;
      match entry_mem, exit_mem with
      | Some entry_mem, Some exit_mem -> 
          Summary.write_summary (Procdesc.get_proc_name pdesc) 
            (entry_mem, exit_mem, cond_set);
          Some (entry_mem, exit_mem, cond_set)
      | _ -> None 
    in
    let analyze_ondemand source pdesc =
      ignore (analyze_ondemand_ source pdesc) in
    let callbacks =
      {
        Ondemand.analyze_ondemand;
        get_proc_desc;
      } in
    if Ondemand.procedure_should_be_analyzed proc_name
    then
      begin
        Ondemand.set_callbacks callbacks;
        let post_opt = analyze_ondemand_ DB.source_file_empty proc_desc in
        Ondemand.unset_callbacks ();
        post_opt
      end
    else
      Summary.read_summary tenv proc_desc proc_name
end 

let checker ({ Callbacks.get_proc_desc; Callbacks.tenv; proc_desc } as callback) =
  let post = Interprocedural.checker callback get_proc_desc in
  match post with 
  | Some (_, post, cond_set) ->
      let proc_name = Procdesc.get_proc_name proc_desc in
      F.fprintf F.err_formatter "@.@[<v 2>Summary of %a :@,@," Procname.pp proc_name;
      Domain.pp_summary F.err_formatter post;
      F.fprintf F.err_formatter "@]@.";
      if Procname.to_string proc_name = "main" then
        Report.report_error tenv proc_desc cond_set
        (*(Domain.get_conds post |> Domain.ConditionSet.merge)*)
(*        my_report_error tenv proc_desc (Domain.get_conds post |> Domain.ConditionSet.merge)        *)
  | _ -> ()
