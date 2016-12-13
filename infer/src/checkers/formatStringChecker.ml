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
module Dom = FormatStringDomain

module Summary = Summary.Make (struct
    type summary = Dom.Summary.t

    let update_payload astate payload =
      { payload with Specs.format_string = Some astate }

    let read_from_payload payload =
      payload.Specs.format_string
  end)

module TransferFunctions (CFG : ProcCfg.S) =
struct
  module CFG = CFG
  module Domain = Dom
  module Semantics = FormatStringSemantics.Make (CFG)
  module Sem = Semantics

  type extras = Procname.t -> Procdesc.t option

  (* NOTE: heuristic *)
  let get_malloc_info : Exp.t -> Typ.t * Exp.t
  = function
    | Exp.BinOp (Binop.Mult, Exp.Sizeof (typ, _, _), size)
    | Exp.BinOp (Binop.Mult, size, Exp.Sizeof (typ, _, _)) -> (typ, size)
    | Exp.Sizeof (typ, _, _) -> (typ, Exp.one)
    | x -> (Typ.Tint Typ.IChar, x)

  let model_malloc
    : Procname.t -> (Ident.t * Typ.t) option -> (Exp.t * Typ.t) list -> CFG.node
      -> Dom.Mem.t -> Dom.Mem.t
  = fun pname ret params node mem ->
    match ret with
    | Some (id, _) ->
        let (typ, size) = get_malloc_info (IList.hd params |> fst) in
        let size = Sem.eval size mem (CFG.loc node) |> Dom.Val.get_itv in
        let v = Sem.eval_array_alloc pname node typ Itv.zero size 0 1 in
        Dom.Mem.add_stack (Loc.of_id id) v mem
    | _ -> mem

  let model_realloc
    : Procname.t -> (Ident.t * Typ.t) option -> (Exp.t * Typ.t) list -> CFG.node
      -> Dom.Mem.t -> Dom.Mem.t
  = fun pname ret params node mem ->
    model_malloc pname ret (IList.tl params) node mem

  let model_natual_itv : (Ident.t * Typ.t) option -> Dom.Mem.t -> Dom.Mem.t
  = fun ret mem ->
    match ret with
    | Some (id, _) -> Dom.Mem.add_stack (Loc.of_id id) Dom.Val.nat_itv mem
    | _ -> mem

  let model_unknown_itv : (Ident.t * Typ.t) option -> Dom.Mem.t -> Dom.Mem.t
  = fun ret mem ->
    match ret with
      Some (id, _) -> Dom.Mem.add_stack (Loc.of_id id) Dom.Val.top_itv mem
    | None -> mem

  let model_infer_print
    : (Exp.t * Typ.t) list -> Dom.Mem.t -> Location.t -> Dom.Mem.t
  = fun params mem loc ->
    match params with
    | (e, _) :: _ ->
        (* TODO: only print when debug mode? *)
        F.fprintf F.err_formatter "@[<v>=== Infer Print === at %a@,"
          Location.pp loc;
        Dom.Val.pp F.err_formatter (Sem.eval e mem loc);
        F.fprintf F.err_formatter "@]";
        mem
    | _ -> mem

  let handle_unknown_call
    : Procname.t -> (Ident.t * Typ.t) option -> Procname.t
      -> (Exp.t * Typ.t) list -> CFG.node -> Dom.Mem.t -> Location.t
      -> Dom.Mem.t
  = fun pname ret callee_pname params node mem loc ->
    match Procname.get_method callee_pname with
    | "malloc"
    | "__new_array" -> model_malloc pname ret params node mem
    | "realloc" -> model_realloc pname ret params node mem
    | "strlen"
    | "fgetc" -> model_natual_itv ret mem
    | "infer_print" -> model_infer_print params mem loc
    | _ -> model_unknown_itv ret mem

  let rec declare_array
    : Procname.t -> CFG.node -> Loc.t -> Typ.t -> IntLit.t -> inst_num:int
      -> dimension:int -> Dom.Mem.astate -> Dom.Mem.astate
  = fun pname node loc typ len ~inst_num ~dimension mem ->
    let size = IntLit.to_int len |> Itv.of_int in
    let arr =
      Sem.eval_array_alloc pname node typ Itv.zero size inst_num dimension
    in
    let mem =
      if dimension = 1
      then Dom.Mem.add_stack loc arr mem
      else Dom.Mem.add_heap loc arr mem
    in
    let loc =
      Loc.of_allocsite (Sem.get_allocsite pname node inst_num dimension)
    in
    match typ with
    | Typ.Tarray (typ, Some len) ->
        declare_array pname node loc typ len ~inst_num
          ~dimension:(dimension + 1) mem
    | _ -> mem

  let declare_symbolic_array
    : Procname.t -> Tenv.t -> CFG.node -> Loc.t -> Typ.t -> inst_num:int
      -> sym_num:int -> dimension:int -> Dom.Mem.astate -> Dom.Mem.astate * int
  = fun pname tenv node loc typ ~inst_num ~sym_num ~dimension mem ->
    let decl_fld (mem, sym_num) (fn, typ, _) =
      let loc =
        mem |> Dom.Mem.find_heap loc |> Dom.Val.get_all_locs |> PowLoc.choose
      in
      let field = Loc.append_field loc fn in
      match typ with
      | Typ.Tint _
      | Typ.Tfloat _ ->
          let (v, sym_num) = Dom.Val.make_sym pname sym_num in
          (Dom.Mem.add_heap field v mem, sym_num)
      | Typ.Tptr (typ, _) ->
          let offset = Itv.make_sym pname sym_num in
          let sym_num = sym_num + 2 in (* TODO *)
          let size = Itv.make_sym pname sym_num in
          let sym_num = sym_num + 2 in (* TODO *)
          let v =
            Sem.eval_array_alloc pname node typ offset size inst_num dimension
          in
          (Dom.Mem.add_heap field v mem, sym_num)
      | _ -> (mem, sym_num)
    in
    let offset = Itv.make_sym pname sym_num in
    let sym_num = sym_num + 2 in (* TODO *)
    let size = Itv.make_sym pname sym_num in
    let sym_num = sym_num + 2 in (* TODO *)
    let arr =
      Sem.eval_array_alloc pname node typ offset size inst_num dimension
    in
    let (elem_val, sym_num) = Dom.Val.make_sym pname sym_num in
    let arr_loc = arr |> Dom.Val.get_array_blk |> ArrayBlk.get_pow_loc in
    let mem =
      mem
      |> Dom.Mem.add_heap loc arr
      |> Dom.Mem.strong_update_heap arr_loc elem_val
    in
    match typ with
    | Typ.Tstruct typename ->
        (match Tenv.lookup tenv typename with
         | Some str ->
             IList.fold_left decl_fld (mem, sym_num) str.StructTyp.fields
         | _ -> (mem, sym_num))
    | _ -> (mem, sym_num)

  let declare_symbolic_parameter
    : Procdesc.t -> Tenv.t -> CFG.node -> int -> Dom.Mem.t -> Dom.Mem.t
  = fun pdesc tenv node inst_num mem ->
    let pname = Procdesc.get_proc_name pdesc in
    let add_formal (mem, inst_num, sym_num) (pvar, typ) =
      match typ with
      | Typ.Tint _ ->
          let (v, sym_num) = Dom.Val.make_sym pname sym_num in
          let mem = Dom.Mem.add_heap (Loc.of_pvar pvar) v mem in
          (mem, inst_num + 1, sym_num)
      | Typ.Tptr (typ, _) ->
          let (mem, sym_num) =
            declare_symbolic_array pname tenv node (Loc.of_pvar pvar) typ
              ~inst_num ~sym_num ~dimension:1 mem
          in
          (mem, inst_num + 1, sym_num)
      | _ -> (mem, inst_num, sym_num) (* TODO: add other cases if necessary *)
    in
    IList.fold_left add_formal (mem, inst_num, 0) (Sem.get_formals pdesc)
    |> fst3

  let instantiate_ret
    : Tenv.t -> Procdesc.t option -> Procname.t -> (Exp.t * Typ.t) list
      -> Dom.Mem.t -> Dom.Summary.t -> Location.t -> Dom.Val.astate
  = fun tenv callee_pdesc callee_pname params caller_m summary loc ->
    let callee_entry_m = Dom.Summary.get_input summary in
    let callee_exit_m = Dom.Summary.get_output summary in
    match callee_pdesc with
    | Some pdesc ->
        let itv_subst_map =
          Sem.get_itv_subst tenv pdesc params caller_m callee_entry_m loc
        in
        let taint_subst_map =
          Sem.get_taint_subst tenv pdesc params caller_m callee_entry_m loc
        in
        let ret_loc = Loc.of_pvar (Pvar.get_ret_pvar callee_pname) in
        let ret_val = Dom.Mem.find_heap ret_loc callee_exit_m in
        Dom.Val.subst ret_val itv_subst_map taint_subst_map
        |> Dom.Val.normalize    (* normalize bottom *)
    | _ -> Dom.Val.bot

  let print_debug_info : Sil.instr -> Dom.Mem.t -> Dom.Mem.t -> unit
  = fun instr pre post ->
    if Config.ropas_debug >= 2 then
      begin
        F.fprintf F.err_formatter "@.@.================================@.";
        F.fprintf F.err_formatter "@[<v 2>Pre-state : @,";
        Dom.pp F.err_formatter pre;
        F.fprintf F.err_formatter "@]@.@.";
        Sil.pp_instr pe_text F.err_formatter instr;
        F.fprintf F.err_formatter "@.@.";
        F.fprintf F.err_formatter "@[<v 2>Post-state : @,";
        Dom.pp F.err_formatter post;
        F.fprintf F.err_formatter "@]@.";
        F.fprintf F.err_formatter "================================@.@."
      end

  let call_sem
      { ProcData.pdesc; tenv; extras } node loc callee_pname params ret mem =
    let pname = Procdesc.get_proc_name pdesc in
    match Summary.read_summary pdesc callee_pname with
    | Some summary ->
        let callee = extras callee_pname in
        let ret_val =
          instantiate_ret tenv callee callee_pname params mem summary loc
        in
        (match ret with
         | Some (id, _) ->
             Dom.Mem.add_stack (Loc.of_var (Var.of_id id)) ret_val mem
         | _ -> mem)
    | None -> handle_unknown_call pname ret callee_pname params node mem loc

  let source_call_sem loc callee_pname ret mem =
    match Procname.to_string callee_pname with
    | "getenv" ->
        (match ret with
         | Some (id, _) ->
             let ret_val = Dom.Mem.find_stack (Loc.of_var (Var.of_id id)) mem in
             let l = Dom.Val.get_all_locs ret_val in
             let v = Dom.Mem.find_heap_set l mem in
             let v = Dom.Val.add_taint loc v in
             Dom.Mem.weak_update_heap l v mem
         | _ -> mem)
    | _ -> mem

  let exec_instr
    : Dom.Mem.t -> extras ProcData.t -> CFG.node -> Sil.instr -> Dom.Mem.astate
  = fun mem ({ pdesc; tenv } as pdata) node instr ->
    let pname = Procdesc.get_proc_name pdesc in
    let try_decl_arr (mem, inst_num) (pvar, typ) =
      match typ with
      | Typ.Tarray (typ, Some len) ->
          let loc = Loc.of_var (Var.of_pvar pvar) in
          let mem =
            declare_array pname node loc typ len ~inst_num ~dimension:1 mem
          in
          (mem, inst_num + 1)
      | _ -> (mem, inst_num)
    in
    let output_mem =
      match instr with
      | Load (id, exp, _, loc) ->
          let locs = Sem.eval exp mem loc |> Dom.Val.get_all_locs in
          let v = Dom.Mem.find_heap_set locs mem in
          Dom.Mem.add_stack (Loc.of_var (Var.of_id id)) v mem
          |> Dom.Mem.load_alias id exp
      | Store (exp1, _, exp2, loc) ->
          let locs = Sem.eval exp1 mem loc |> Dom.Val.get_all_locs in
          Dom.Mem.update_mem locs (Sem.eval exp2 mem loc) mem
          |> Dom.Mem.store_alias exp1 exp2
      | Prune (exp, loc, _, _) -> Sem.prune exp loc mem
      | Call (ret, Const (Cfun callee_pname), params, loc, _) ->
          let mem = call_sem pdata node loc callee_pname params ret mem in
          source_call_sem loc callee_pname ret mem
      | Declare_locals (locals, _) ->
          (* array allocation in stack e.g., int arr[10] *)
          let (mem, inst_num) = IList.fold_left try_decl_arr (mem, 1) locals in
          declare_symbolic_parameter pdesc tenv node inst_num mem
      | Call _
      | Remove_temps _
      | Abstract _
      | Nullify _ -> mem
    in
    print_debug_info instr mem output_mem;
    output_mem
end

module Analyzer =
  AbstractInterpreter.Make (ProcCfg.Normal) (Scheduler.ReversePostorder)
    (TransferFunctions)

module Report =
struct
  module CFG = ProcCfg.Normal
  module Semantics = FormatStringSemantics.Make (CFG)
  module Sem = Semantics
  module TransferFunctions = TransferFunctions (CFG)

  type extras = Procname.t -> Procdesc.t option

  let instantiate_cond
  = fun tenv caller_pname callee_pdesc params caller_mem summary loc ->
    let callee_entry_mem = Dom.Summary.get_input summary in
    let callee_cond = Dom.Summary.get_cond_set summary in
    match callee_pdesc with
    | Some pdesc ->
        let taint_subst =
          Sem.get_taint_subst tenv pdesc params caller_mem callee_entry_mem loc
        in
        let pname = Procdesc.get_proc_name pdesc in
        Dom.ConditionSet.subst callee_cond taint_subst caller_pname pname loc
    | _ -> callee_cond

  let print_debug_info : Sil.instr -> Dom.t -> Dom.ConditionSet.t -> unit
  = fun instr pre cond_set ->
    if Config.ropas_debug >= 2 then
      (F.fprintf F.err_formatter "@.@.================================@.";
       F.fprintf F.err_formatter "@[<v 2>Pre-state : @,";
       Dom.pp F.err_formatter pre;
       F.fprintf F.err_formatter "@]@.@.";
       Sil.pp_instr pe_text F.err_formatter instr;
       F.fprintf F.err_formatter "@[<v 2>@.@.";
       Dom.ConditionSet.pp F.err_formatter cond_set;
       F.fprintf F.err_formatter "@]@.";
       F.fprintf F.err_formatter "================================@.@.")

  module SinkMap = Map.Make (String)

  let sink_funcs =
    SinkMap.empty
    |> SinkMap.add "printf" 0
    |> SinkMap.add "sprintf" 1

  let add_cond_n n pname loc params mem cond_set =
    match IList.nth params n with
    | (e, _) ->
        let p = Sem.eval e mem loc in
        let v = Dom.Mem.find_heap_set (Dom.Val.get_all_locs p) mem in
        let t = Dom.Val.get_taint v in
        (if Config.ropas_debug >= 2 then
           (F.fprintf F.err_formatter "@[<v 2>Add condition :@,";
            F.fprintf F.err_formatter "Pname: %s@," (Procname.to_string pname);
            F.fprintf F.err_formatter "Sink: %a@," FSTaintSet.pp t;
            F.fprintf F.err_formatter "@]@."));
        Dom.ConditionSet.add_fs_safety pname loc t cond_set
    | exception _ -> assert false

  let add_conds pname loc params mem cond_set =
    match SinkMap.find (Procname.to_string pname) sink_funcs with
    | n -> add_cond_n n pname loc params mem cond_set
    | exception Not_found -> cond_set

  let collect_instr
    : extras ProcData.t -> CFG.node -> Dom.ConditionSet.t * Dom.Mem.t
      -> Sil.instr -> Dom.ConditionSet.t * Dom.Mem.t
  = fun ({ pdesc; tenv; extras } as pdata) node (cond_set, mem) instr ->
    let pname = Procdesc.get_proc_name pdesc in
    let cond_set =
      match instr with
      | Sil.Call (_, Const (Cfun callee_pname), params, loc, _) ->
          let cond_set = add_conds callee_pname loc params mem cond_set in
          (match Summary.read_summary pdesc callee_pname with
           | Some summary ->
               let callee = extras callee_pname in
               instantiate_cond tenv pname callee params mem summary loc
               |> Dom.ConditionSet.join cond_set
           | _ -> cond_set)
      | _ -> cond_set
    in
    print_debug_info instr mem cond_set;
    let mem = TransferFunctions.exec_instr mem pdata node instr in
    (cond_set, mem)

  let collect_instrs
    : extras ProcData.t -> CFG.node -> Sil.instr list -> Dom.Mem.t
      -> Dom.ConditionSet.t -> Dom.ConditionSet.t
  = fun pdata node instrs mem cond_set ->
    IList.fold_left (collect_instr pdata node) (cond_set, mem) instrs
    |> fst

  let collect_node
    : extras ProcData.t -> Analyzer.invariant_map -> Dom.ConditionSet.t ->
      CFG.node -> Dom.ConditionSet.t
  = fun pdata inv_map cond_set node ->
    let instrs = CFG.instr_ids node |> IList.map fst in
    match Analyzer.extract_pre (CFG.id node) inv_map with
    | Some mem -> collect_instrs pdata node instrs mem cond_set
    | _ -> cond_set

  let collect
    : extras ProcData.t -> Analyzer.invariant_map -> Dom.ConditionSet.t
  = fun ({ pdesc } as pdata) inv_map ->
    let add_node1 acc node = collect_node pdata inv_map acc node in
    Procdesc.fold_nodes add_node1 Dom.ConditionSet.empty pdesc

  let report_error : Tenv.t -> Procdesc.t -> Dom.ConditionSet.t -> unit
  = fun tenv pdesc conds ->
    let pname = Procdesc.get_proc_name pdesc in
    let report1 cond =
      let safe = Dom.Condition.check cond in
      let (caller_pname, loc) =
        match Dom.Condition.get_trace cond with
        | Dom.Condition.Inter (caller_pname, _, loc) -> (caller_pname, loc)
        | Dom.Condition.Intra pname -> (pname, Dom.Condition.get_location cond)
      in
      (* report symbol-related alarms only in debug mode *)
      if not safe && Procname.equal pname caller_pname then
        let fs_kind = "FORMAT-STRING CHECKER" in
        let cond_str = Dom.Condition.to_string cond in
        Checkers.ST.report_error tenv pname pdesc fs_kind loc cond_str
    in
    Dom.ConditionSet.iter report1 conds

  let ropas_report_condset : Dom.Condition.t -> int -> int
  = fun cond k ->
    if not (Dom.Condition.check cond) then
      let loc_str = Location.to_string cond.loc in
      let file_name = DB.source_file_to_string cond.loc.Location.file in
      let pname = Dom.Condition.get_proc_name cond |> Procname.to_string in
      F.fprintf F.err_formatter "@.%d. %s:%s: {%s} error: FORMAT-STRING @."
        k file_name loc_str pname;
      F.fprintf F.err_formatter "  %s @." (Dom.Condition.to_string cond);
      k + 1
    else k

  let ropas_report_error : Dom.ConditionSet.t -> unit
  = fun conds ->
    F.fprintf F.err_formatter "@.== Alarms ==@.";
    let k = Dom.ConditionSet.fold ropas_report_condset conds 1 in
    F.fprintf F.err_formatter "@.@.%d issues found@." (k - 1)
end

module Interprocedural =
struct
  let analyze_ondemand_
    : Tenv.t -> Analyzer.TransferFunctions.extras -> Procdesc.t
      -> Dom.Summary.t option
  = fun tenv get_pdesc pdesc ->
    let cfg = Analyzer.CFG.from_pdesc pdesc in
    let pdata = ProcData.make pdesc tenv get_pdesc in
    let pname = Procdesc.get_proc_name pdesc in
    let inv_map = Analyzer.exec_pdesc pdata in
    let entry_mem =
      let entry_id = Analyzer.CFG.id (Analyzer.CFG.start_node cfg) in
      Analyzer.extract_post entry_id inv_map
    in
    let exit_mem =
      let exit_id = Analyzer.CFG.id (Analyzer.CFG.exit_node cfg) in
      Analyzer.extract_post exit_id inv_map
    in
    let cond_set = Report.collect pdata inv_map in
    if not Config.ropas_report then Report.report_error tenv pdesc cond_set;
    if Procname.get_method pname = "infer_print" then None else
      match entry_mem, exit_mem with
      | Some entry_mem, Some exit_mem ->
          Summary.write_summary pname (entry_mem, exit_mem, cond_set);
          Some (entry_mem, exit_mem, cond_set)
      | _ -> None

  let checker : Callbacks.proc_callback_args -> Dom.Summary.t option
  = fun { get_proc_desc; proc_desc; proc_name; tenv } ->
    let analyze_ondemand _ pdesc =
      ignore (analyze_ondemand_ tenv get_proc_desc pdesc)
    in
    let callbacks = { Ondemand.analyze_ondemand; get_proc_desc } in
    if Ondemand.procedure_should_be_analyzed proc_name then
      (Ondemand.set_callbacks callbacks;
       let post_opt = analyze_ondemand_ tenv get_proc_desc proc_desc in
       Ondemand.unset_callbacks ();
       post_opt)
    else Summary.read_summary proc_desc proc_name
end

let checker : Callbacks.proc_callback_args -> unit
= fun ({ proc_name } as callback) ->
  match Interprocedural.checker callback with
  | Some ((_, _, cond_set) as s) ->
      F.fprintf F.err_formatter "@.@[<v 2>Summary of %a :@,"
        Procname.pp proc_name;
      Dom.Summary.pp_summary F.err_formatter s;
      F.fprintf F.err_formatter "@]@.";
      if Config.ropas_report && Procname.to_string proc_name = "main" then 
        Report.ropas_report_error cond_set
  | _ -> ()
