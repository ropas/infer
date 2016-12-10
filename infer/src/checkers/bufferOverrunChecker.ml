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

module Summary = Summary.Make (struct
    type summary = BufferOverrunDomain.Summary.t

    let update_payload astate payload = 
      { payload with Specs.buffer_overrun = Some astate }

    let read_from_payload payload =
      payload.Specs.buffer_overrun
  end)

module SubstMap = Map.Make(struct 
    type t = Itv.Bound.t 
    let compare = Itv.Bound.compare 
  end)

module TransferFunctions (CFG : ProcCfg.S) = 
struct
  module CFG = CFG
  module Domain = Domain
  module Semantics = BufferOverrunSemantics.Make(CFG)
  type extras = Procname.t -> Procdesc.t option

  (* heuristic *)
  let get_malloc_info = function
    | Exp.BinOp (Binop.Mult, Exp.Sizeof (typ, _, _), size)
    | Exp.BinOp (Binop.Mult, size, Exp.Sizeof (typ, _, _)) -> (typ, size)
    | Exp.Sizeof (typ, _, _) -> (typ, Exp.one)
    | x -> (Typ.Tint Typ.IChar, x)

  let model_malloc pname ret params node mem =
    match ret with 
      Some (id, _) -> 
        let (typ, size) = get_malloc_info (IList.hd params |> fst) in
        let size = Semantics.eval size mem (CFG.loc node) |> Domain.Val.get_itv in
        Domain.Mem.add_stack (Loc.of_id id) (Semantics.eval_array_alloc pname node typ Itv.zero size 0 1) mem
    | _ -> mem

  let model_realloc pname ret params node mem =
    match ret with 
      Some (_, _) -> model_malloc pname ret (IList.tl params) node mem
    | _ -> mem

  let model_natual_itv ret mem =
    match ret with 
      Some (id, _) -> Domain.Mem.add_stack (Loc.of_id id) Domain.Val.nat_itv mem
    | _ -> mem 

  let model_unknown_itv ret mem = 
    match ret with
      Some (id, _) -> Domain.Mem.add_stack (Loc.of_id id) Domain.Val.top_itv mem
    | None -> mem
    
  let model_infer_print params mem loc =
    match params with 
      (e, _)::_ -> 
        F.fprintf F.err_formatter "<v>=== Infer Print === at %a@," Location.pp loc;
        Domain.Val.pp F.err_formatter (Semantics.eval e mem loc); mem
    | _ -> mem 
    
  let handle_unknown_call pname ret callee_pname params node mem loc =
    match Procname.get_method callee_pname with
    | "malloc" | "__new_array" -> model_malloc pname ret params node mem
    | "realloc" -> model_realloc pname ret params node mem
    | "strlen" | "fgetc" -> model_natual_itv ret mem
    | "infer_print" -> model_infer_print params mem loc
    | _ -> model_unknown_itv ret mem

  let rec declare_array pname node loc typ len ~inst_num ~dimension mem =
    let size = IntLit.to_int len |> Itv.of_int in
    let arr = Semantics.eval_array_alloc pname node typ Itv.zero size inst_num dimension in
    let mem = 
      if dimension = 1 then Domain.Mem.add_stack loc arr mem 
      else Domain.Mem.add_heap loc arr mem 
    in
    let loc = Loc.of_allocsite (Semantics.get_allocsite pname node inst_num dimension) in
    match typ with 
      Typ.Tarray (typ, Some len) -> 
        declare_array pname node loc typ len ~inst_num ~dimension:(dimension + 1) mem
    | _ -> mem

  let declare_symbolic_array pname tenv node loc typ ~inst_num ~sym_num ~dimension mem =
    let offset = Itv.make_sym pname sym_num in
    let size = Itv.make_sym pname (sym_num + 2) in
    let arr = Semantics.eval_array_alloc pname node typ offset size inst_num dimension in
    let elem_val = Domain.Val.make_sym pname (sym_num + 4) in
    let mem = 
      Domain.Mem.add_heap loc arr mem 
      |> Domain.Mem.strong_update_heap 
          (arr |> Domain.Val.get_array_blk |> ArrayBlk.get_pow_loc) 
          elem_val
    in
    match typ with 
      Typ.Tstruct typename ->
      begin
        match Tenv.lookup tenv typename with
          Some str -> 
            IList.fold_left (fun (mem, sym_num) (fn, typ, _) ->
              let loc = Domain.Mem.find_heap loc mem 
                |> Domain.Val.get_all_locs 
                |> PowLoc.choose 
              in
              let field = Loc.append_field loc fn in
              match typ with 
                Typ.Tint _ | Typ.Tfloat _ -> 
                  (Domain.Mem.add_heap field (Domain.Val.make_sym pname sym_num) mem, sym_num + 2)
              | Typ.Tptr (typ, _) -> 
                  let (offset, size) = (Itv.make_sym pname sym_num, 
                                        Itv.make_sym pname (sym_num + 2)) 
                  in
                  (Domain.Mem.add_heap field 
                    (Semantics.eval_array_alloc pname node typ offset size
                      inst_num dimension) mem,
                   sym_num + 4)
                  (*declare_symbolic_array pdesc tenv node field typ (inst_num+1) dimension mem*)
              | _ -> (mem, sym_num)
            ) (mem, sym_num+6) str.StructTyp.fields
        | _ -> (mem, sym_num+6)
      end
    | _ -> (mem, sym_num+6)

  let declare_symbolic_parameter pdesc tenv node inst_num mem = 
    let pname = Procdesc.get_proc_name pdesc in
    (* formal parameters *)
    IList.fold_left (fun (mem, inst_num, sym_num) (pvar, typ) ->
      match typ with
        Typ.Tint _ -> 
          (Domain.Mem.add_heap (Loc.of_pvar pvar) 
              (Domain.Val.make_sym pname sym_num) mem, 
           inst_num + 1,
           sym_num + 2)
      | Typ.Tptr (typ, _) ->
          let (mem, sym_num) = declare_symbolic_array pname tenv node
              (Loc.of_pvar pvar) typ ~inst_num ~sym_num ~dimension:1 mem
          in
          (mem, inst_num+1, sym_num)
      | _ -> (mem, inst_num, sym_num) (* add other cases if necessary *)) 
    (mem, inst_num, 0) (Semantics.get_formals pdesc)
    |> fst3
      
  let instantiate_ret tenv callee_pdesc callee_pname params caller_mem summary loc =
    let (callee_entry_mem, callee_exit_mem) = 
      (Domain.Summary.get_input summary, Domain.Summary.get_output summary) in
    match callee_pdesc with
    | Some pdesc ->
        let subst_map =
          Semantics.get_subst_map tenv pdesc params caller_mem
            callee_entry_mem loc
        in
        let ret_loc = Loc.of_pvar (Pvar.get_ret_pvar callee_pname) in
        let ret_val = Domain.Mem.find_heap ret_loc callee_exit_mem in
        Domain.Val.subst ret_val subst_map
        |> Domain.Val.normalize (* normalize bottom *)
    | _ -> Domain.Val.bot

  let print_debug_info instr pre post = 
    if Config.ropas_debug >= 2 then 
    begin
      F.fprintf F.err_formatter "@.@.================================@.";
      F.fprintf F.err_formatter "@[<v 2>Pre-state : @,";
      Domain.pp F.err_formatter pre;
      F.fprintf F.err_formatter "@]@.@.";
      Sil.pp_instr pe_text F.err_formatter instr;
      F.fprintf F.err_formatter "@.@.";
      F.fprintf F.err_formatter "@[<v 2>Post-state : @,";
      Domain.pp F.err_formatter post;
      F.fprintf F.err_formatter "@]@.";
      F.fprintf F.err_formatter "================================@.@."
    end
   
  let exec_instr mem { ProcData.pdesc; tenv; extras } node (instr : Sil.instr) =
    let pname = Procdesc.get_proc_name pdesc in
    let output_mem =
      match instr with
      | Load (id, exp, _, loc) ->
          let locs = Semantics.eval exp mem loc |> Domain.Val.get_all_locs in
          let v = Domain.Mem.find_heap_set locs mem in
          Domain.Mem.add_stack (Loc.of_var (Var.of_id id)) v mem
          |> Domain.Mem.load_alias id exp
      | Store (exp1, _, exp2, loc) ->
          let locs = Semantics.eval exp1 mem loc |> Domain.Val.get_all_locs in
          Domain.Mem.update_mem locs (Semantics.eval exp2 mem loc) mem
          |> Domain.Mem.store_alias exp1 exp2
      | Prune (exp, loc, _, _) -> Semantics.prune exp loc mem
      | Call (ret, Const (Cfun callee_pname), params, loc, _) ->
          (match Summary.read_summary pdesc callee_pname with
           | Some summary ->
               let callee = extras callee_pname in
               let ret_val =
                 instantiate_ret tenv callee callee_pname params mem summary loc
               in
               (match ret with
                | Some (id,_) ->
                    Domain.Mem.add_stack (Loc.of_var (Var.of_id id)) ret_val mem
                | _ -> mem)
           | None -> handle_unknown_call pname ret callee_pname params node mem loc)
      | Declare_locals (locals, _) ->
          (* array allocation in stack e.g., int arr[10] *)
          let (mem, inst_num) = IList.fold_left (fun (mem, inst_num) (pvar, typ) ->
              match typ with
                Typ.Tarray (typ, Some len) ->
                  (declare_array pname node (Loc.of_var (Var.of_pvar pvar)) typ
                     len ~inst_num ~dimension:1 mem, 
                   inst_num+1)
              | _ -> (mem, inst_num)) (mem, 1) locals
          in
          declare_symbolic_parameter pdesc tenv node inst_num mem
      | Call (_, _, _, _, _) | Remove_temps _ | Abstract _ | Nullify _ -> mem
    in
    print_debug_info instr mem output_mem;
    output_mem
end

module Analyzer = AbstractInterpreter.Make
    (ProcCfg.Normal) (Scheduler.ReversePostorder) (TransferFunctions)

module Report =
struct 
  module CFG = ProcCfg.Normal
  module Semantics = BufferOverrunSemantics.Make(CFG)
  module TransferFunctions = TransferFunctions(CFG)
  type extras = Procname.t -> Procdesc.t option

  let add_condition : Procname.t -> CFG.node -> Exp.t -> Location.t
    -> Domain.Mem.astate -> Domain.ConditionSet.t -> Domain.ConditionSet.t
  = fun pname node exp loc mem cond_set ->
    let array_access = 
      match exp with 
      | Exp.Var _ -> 
          let arr = Semantics.eval exp mem loc |> Domain.Val.get_array_blk in
          Some (arr, Itv.zero, true)
      | Exp.Lindex (e1, e2)
      | Exp.BinOp (Binop.PlusA, e1, e2) ->
          let arr = Semantics.eval e1 mem loc |> Domain.Val.get_array_blk in
          let idx = Semantics.eval e2 mem loc |> Domain.Val.get_itv in
          Some (arr, idx, true)
      | Exp.BinOp (Binop.MinusA, e1, e2) ->
          let arr = Semantics.eval e1 mem loc |> Domain.Val.get_array_blk in
          let idx = Semantics.eval e2 mem loc |> Domain.Val.get_itv in
          Some (arr, idx, false)
      | _ -> None
    in
    match array_access with
      Some (arr, idx, is_plus) ->
        let site = Semantics.get_allocsite pname node 0 0 in
        let size = ArrayBlk.sizeof arr in
        let offset = ArrayBlk.offsetof arr in
        let idx = (if is_plus then Itv.plus else Itv.minus) offset idx in
          (if Config.ropas_debug >= 2 then
             (F.fprintf F.err_formatter "@[<v 2>Add condition :@,";
              F.fprintf F.err_formatter "array: %a@," ArrayBlk.pp arr;
              F.fprintf F.err_formatter "  idx: %a@," Itv.pp idx;
              F.fprintf F.err_formatter "@]@."));
        if size <> Itv.bot && idx <> Itv.bot then 
           Domain.ConditionSet.add_bo_safety pname loc site ~size ~idx cond_set
        else cond_set
    | None -> cond_set

  let instantiate_cond tenv caller_pname callee_pdesc params caller_mem summary loc =
    let (callee_entry_mem, callee_cond) = 
      (Domain.Summary.get_input summary, Domain.Summary.get_cond_set summary) in
    match callee_pdesc with
    | Some pdesc ->
        let subst_map = Semantics.get_subst_map tenv pdesc params caller_mem callee_entry_mem loc in
        let pname = Procdesc.get_proc_name pdesc in
        Domain.ConditionSet.subst callee_cond subst_map caller_pname pname loc
    | _ -> callee_cond

  let print_debug_info instr pre cond_set = 
    if Config.ropas_debug >= 2 then 
    begin
      F.fprintf F.err_formatter "@.@.================================@.";
      F.fprintf F.err_formatter "@[<v 2>Pre-state : @,";
      Domain.pp F.err_formatter pre;
      F.fprintf F.err_formatter "@]@.@.";
      Sil.pp_instr pe_text F.err_formatter instr;
      F.fprintf F.err_formatter "@[<v 2>@.@.";
      Domain.ConditionSet.pp F.err_formatter cond_set;
      F.fprintf F.err_formatter "@]@.";
      F.fprintf F.err_formatter "================================@.@."
    end

  let collect_instrs : extras ProcData.t -> CFG.node -> Sil.instr list -> Domain.Mem.astate 
      -> Domain.ConditionSet.t -> Domain.ConditionSet.t 
  = fun ({ ProcData.pdesc; tenv; extras } as proc_data) node instrs mem cond_set ->
    let pname = Procdesc.get_proc_name pdesc in
    IList.fold_left (fun (cond_set, mem) instr ->
        let cond_set = 
          match instr with
          | Sil.Load (_, exp, _, loc)
          | Sil.Store (exp, _, _, loc) -> add_condition pname node exp loc mem cond_set
          | Sil.Call (_, Const (Cfun callee_pname), params, loc, _) -> 
            begin
              match Summary.read_summary pdesc callee_pname with
              | Some summary ->
                  let callee = extras callee_pname in
                  instantiate_cond tenv pname callee params mem summary loc
                  |> Domain.ConditionSet.rm_invalid
                  |> Domain.ConditionSet.join cond_set
              | _ -> cond_set
            end
          | _ -> cond_set
        in
        let mem = TransferFunctions.exec_instr mem proc_data node instr in
        print_debug_info instr mem cond_set;
        (cond_set, mem)
    ) (cond_set, mem) instrs
    |> fst

  let collect ({ ProcData.pdesc; } as proc_data) inv_map = 
    Procdesc.fold_nodes (fun cond_set node ->
      let instrs = Analyzer.CFG.instr_ids node |> IList.map fst in 
      let pre = Analyzer.extract_pre (Analyzer.CFG.id node) inv_map in
      match pre with 
        Some mem -> collect_instrs proc_data node instrs mem cond_set
      | _ -> cond_set) Domain.ConditionSet.empty pdesc

  let report_error : Tenv.t -> Procdesc.t -> Domain.ConditionSet.t -> unit 
  = fun tenv pdesc conds -> 
    let pname = Procdesc.get_proc_name pdesc in
    Domain.ConditionSet.iter (fun cond ->
        let safe = Domain.Condition.check cond in
        let (caller_pname, _, loc) =
          match Domain.Condition.get_callsite cond with 
          | Some (caller_pname, callee_pname, loc) ->
              (caller_pname, callee_pname, loc)
          | None -> (pname, pname, Domain.Condition.get_location cond)
        in
        (* report symbol-related alarms only in debug mode *)
        if not safe && Procname.equal pname caller_pname then
          Checkers.ST.report_error tenv
            pname
            pdesc
            "BUFFER-OVERRUN CHECKER"
            loc
            (Domain.Condition.to_string cond)) conds

  let my_report_error : Tenv.t -> Procdesc.t -> Domain.ConditionSet.t -> unit 
  = fun _ _ conds -> 
    F.fprintf F.err_formatter "@.== Alarms ==@.";
    let k = 
      Domain.ConditionSet.Map.fold (fun loc cond_set k ->
        if Domain.ConditionSet.exists (fun cond -> not (Domain.Condition.check cond)) cond_set then
          let loc_str = Location.to_string loc in
          let file_name = DB.source_file_to_string loc.Location.file in
          let sample = Domain.ConditionSet.choose cond_set in
          let proc_name = Domain.Condition.get_proc_name sample |> Procname.to_string in
          F.fprintf F.err_formatter "@.%d. %s:%s: {%s} error: BUFFER-OVERRUN @." 
            k file_name loc_str proc_name;
          Domain.ConditionSet.iter (fun cond ->
            let safe = Domain.Condition.check cond in
            (* report symbol-related alarms only in debug mode *)
            if not safe then
              F.fprintf F.err_formatter "  %s @." (Domain.Condition.to_string cond)
          ) cond_set;
          k + 1
        else k) (Domain.ConditionSet.group conds) 1
    in
    F.fprintf F.err_formatter "@.@.%d issues found@." (k-1)
end

module Interprocedural = 
struct 
  let checker { Callbacks.get_proc_desc; proc_desc; proc_name; tenv; } extras =
    let analyze_ondemand_ _ pdesc =
      let cfg = Analyzer.CFG.from_pdesc pdesc in
      let inv_map = Analyzer.exec_pdesc (ProcData.make pdesc tenv extras) in
      let (entry_mem, exit_mem) = 
            (Analyzer.extract_post (Analyzer.CFG.id (Analyzer.CFG.start_node cfg)) inv_map,
             Analyzer.extract_post (Analyzer.CFG.id (Analyzer.CFG.exit_node cfg)) inv_map)
      in
      let cond_set = Report.collect (ProcData.make pdesc tenv extras) inv_map in
      match entry_mem, exit_mem with
      | Some _, Some _ 
          when (Procdesc.get_proc_name pdesc |> Procname.get_method) = "infer_print" -> 
          None
      | Some entry_mem, Some exit_mem -> 
          Summary.write_summary (Procdesc.get_proc_name pdesc) 
            (entry_mem, exit_mem, cond_set);
          Some (entry_mem, exit_mem, cond_set)
      | _ -> None 
    in
    (* below, copied from abstractIntepreter.ml *)
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
      Summary.read_summary proc_desc proc_name
end 

let checker ({ Callbacks.get_proc_desc; Callbacks.tenv; proc_desc } as callback) =
  let post = Interprocedural.checker callback get_proc_desc in
  match post with 
  | Some ((_, _, cond_set) as s) ->
      let proc_name = Procdesc.get_proc_name proc_desc in
      F.fprintf F.err_formatter "@.@[<v 2>Summary of %a :@," Procname.pp proc_name;
      Domain.Summary.pp_summary F.err_formatter s;
      F.fprintf F.err_formatter "@]@.";
(*      if Procname.to_string proc_name = "main" then
      begin*)
        if Config.ropas_report then
          Report.my_report_error tenv proc_desc cond_set    
        else
          Report.report_error tenv proc_desc cond_set
(*      end*)
  | _ -> ()
