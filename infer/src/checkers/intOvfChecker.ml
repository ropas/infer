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
open ApiModel

module F = Format
module L = Logging
module Dom = IntOvfDomain

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
  module Semantics = IntOvfSemantics.Make (CFG)
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
        let (typ, _) = get_malloc_info (IList.hd params |> fst) in
        let size = Itv.top in
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

  let eval_src src_typ loc mem arg_e =
    let v = Sem.eval arg_e mem loc in
    match src_typ with
    | Value -> v
    | Array -> Dom.Mem.find_heap_set (Dom.Val.get_all_locs v) mem

  let rec collect_src_vals arg_exps arg_typs loc mem =
    match arg_exps, arg_typs with
    | [], _ | _, [] -> [] (* if src empty *)
    | _, (Src (Variable, src_typ, _) :: []) ->
        IList.map (eval_src src_typ loc mem) arg_exps
    | _, (Src (Variable, _, _) :: _) ->
        failwith "API encoding error (Varg not at the last position)"
    | (arg_e :: arg_exps_left), (Src (Fixed, src_typ, _) :: arg_typs_left) ->
        let src_v = eval_src src_typ loc mem arg_e in
        src_v :: (collect_src_vals arg_exps_left arg_typs_left loc mem)
    | (_ :: arg_exps_left), (_ :: arg_typs_left) ->
        collect_src_vals arg_exps_left arg_typs_left loc mem

  let rec collect_dst_vals arg_exps arg_typs loc mem =
    match arg_exps, arg_typs with
    | [], _ | _, [] -> []
    | _, (Dst (Variable, _) :: []) ->
        IList.map (fun e -> Sem.eval e mem loc) arg_exps
    | _, (Dst (Variable, _) :: _) ->
        failwith "API encoding error (Varg not at the last position)"
    | (arg_e :: arg_exps_left), (Dst (Fixed, _) :: arg_typs_left) ->
        let dst_v = Sem.eval arg_e mem loc in
        dst_v :: (collect_dst_vals arg_exps_left arg_typs_left loc mem)
    | (_ :: arg_exps_left), (_ :: arg_typs_left) ->
        collect_dst_vals arg_exps_left arg_typs_left loc mem

  let rec collect_buf_vals arg_exps arg_typs loc mem =
    match arg_exps, arg_typs with
    | [], _ | _, [] -> []
    | _, (Buf (Variable, _) :: []) ->
        IList.map (fun e -> Sem.eval e mem loc) arg_exps
    | _, (Buf (Variable, _) :: _) ->
        failwith "API encoding error (Varg not at the last position)"
    | (arg_e :: arg_exps_left), (Buf (Fixed, _) :: arg_typs_left) ->
        let buf_v = Sem.eval arg_e mem loc in
        buf_v :: (collect_buf_vals arg_exps_left arg_typs_left loc mem)
    | (_ :: arg_exps_left), (_ :: arg_typs_left) ->
        collect_buf_vals arg_exps_left arg_typs_left loc mem

  let rec collect_size_vals arg_exps arg_typs node mem =
    match arg_exps, arg_typs with
    | [], _ | _, [] -> []
    | (arg_e :: arg_exps_left), (Size :: arg_typs_left) ->
        let size_v = Sem.eval arg_e mem node in
        size_v :: (collect_size_vals arg_exps_left arg_typs_left node mem)
    | (_ :: arg_exps_left), (_ :: arg_typs_left) ->
        collect_size_vals arg_exps_left arg_typs_left node mem

  let process_dst loc src_vals mem dst_e =
    let src_v = IList.fold_left Dom.Val.join Dom.Val.bot src_vals in
    let dst_loc = Dom.Val.get_all_locs (Sem.eval dst_e mem loc) in
    Dom.Mem.update_mem dst_loc src_v mem

  let process_buf loc mem dst_e =
    let buf_loc = Dom.Val.get_all_locs (Sem.eval dst_e mem loc) in
    let input_v = Dom.Val.of_taint_with_loc loc in
    Dom.Mem.update_mem buf_loc input_v mem

  let process_struct_ptr node pname (inst_num, dim) loc mem ptr_e =
    let struct_loc = Dom.Val.get_all_locs (Sem.eval ptr_e mem loc) in
    let allocsite = Sem.get_allocsite pname node inst_num dim in
    let ext_v = Dom.Val.extern_value allocsite loc in
    let ext_loc = Dom.Val.get_all_locs ext_v in
    let mem = Dom.Mem.update_mem struct_loc ext_v mem in
    Dom.Mem.update_mem ext_loc ext_v mem


  let rec process_args pname allocinfo loc node arg_exps arg_typs src_vals mem =
    let va_src_flag =
      IList.exists (function | Src (Variable, _, _) -> true | _ -> false) arg_typs
    in
    match arg_exps, arg_typs with
    | [], _ | _ , [] -> mem
    | _, (Dst (Variable, _) :: []) ->
        assert (va_src_flag || IList.length src_vals > 0);
        IList.fold_left (process_dst loc src_vals) mem arg_exps
    | _, (Dst (Variable, _) :: _) ->
        failwith "API encoding error (Varg not at the last position)"
    | (arg_e :: arg_exps_left), (Dst (Fixed, _) :: arg_typs_left) ->
        assert (va_src_flag || IList.length src_vals > 0);
        let mem = process_dst loc src_vals mem arg_e in
        process_args pname allocinfo loc node arg_exps_left arg_typs_left src_vals mem
    | _, (Buf (Variable, _) :: []) ->
        IList.fold_left (process_buf loc) mem arg_exps
    | _, (Buf (Variable, _) :: _) ->
        failwith "itvSetm.ml : API encoding error (Varg not at the last position)"
    | (arg_e :: arg_exps_left), (Buf (Fixed, _) :: arg_typs_left) ->
        let mem = process_buf loc mem arg_e in
        process_args pname allocinfo loc node arg_exps_left arg_typs_left src_vals mem
    | (arg_e :: arg_exps_left), (StructPtr :: arg_typs_left) ->
        (* position node pname inst_num loc (mem, global) ptr_e *)
        let mem = process_struct_ptr node pname allocinfo loc mem arg_e in
        process_args pname allocinfo loc node arg_exps_left arg_typs_left src_vals mem
    | (_ :: arg_exps_left), (Src _ :: arg_typs_left)
    | (_ :: arg_exps_left), (Size :: arg_typs_left)
    | (_ :: arg_exps_left), (Skip :: arg_typs_left) ->
        process_args pname allocinfo loc node arg_exps_left arg_typs_left src_vals mem

  let gen_block pname (inst_num, dim) node init_v mem =
    let allocsite = Sem.get_allocsite pname node inst_num dim in
    let offset = Itv.of_int 0 in
    let sz = Itv.top in
    let st = Itv.of_int 1 in
    let pow_loc = PowLoc.singleton (Loc.Allocsite allocsite) in
    let array = ArrayBlk.make allocsite offset sz st in
    let block_v = Dom.Val.make OvfSet.bot TaintSet.bot pow_loc array in
    (Dom.Mem.update_mem pow_loc init_v mem, block_v)

  let produce_ret pname allocinfo loc node ret_typ va_src_flag
      src_vals dst_vals buf_vals size_vals mem =
    match ret_typ with
    | Const v -> (mem, v)
    | TaintInput -> (* User input value (top itv & taintness) *)
        (mem, Dom.Val.of_taint_with_loc loc)
    | SrcArg -> (* Src argument returned *)
        assert (IList.length src_vals = 1);
        (mem, IList.hd src_vals)
    | SizeArg -> (* Integer between 0 ~ Size argument returned *)
        assert (IList.length size_vals = 1);
        (mem, IList.hd size_vals)
    | TopWithSrcTaint -> (* Top itv & taintness of Src argument returned *)
        assert (va_src_flag || IList.length src_vals > 0);
        let src_v = IList.fold_left Dom.Val.join Dom.Val.bot src_vals in
        let src_taint = Dom.Val.get_taint src_v in
        (mem, Dom.Val.of_taint src_taint)
    | DstArg -> (* Dst argument returned *)
        assert (IList.length dst_vals = 1);
        (mem, IList.hd dst_vals)
    | BufArg -> (* Buf argument returned *)
        assert (IList.length buf_vals = 1);
        (mem, IList.hd buf_vals)
    | AllocConst v -> (* New block, filled with given abstract val. *)
        gen_block pname allocinfo node v mem
    | AllocDst -> (* New block, filled with Src argument *)
        assert (va_src_flag || IList.length src_vals > 0);
        let src_v = IList.fold_left Dom.Val.join Dom.Val.bot src_vals in
        gen_block pname allocinfo node src_v mem
    | AllocBuf -> (* New block, filled with user input *)
        gen_block pname allocinfo node
          (Dom.Val.of_taint_with_loc loc) mem
    | AllocStruct -> (* Newly allocated struct *)
        let (inst_num, dim) = allocinfo in
        let allocsite = Sem.get_allocsite pname node inst_num dim in
        let ext_v = Dom.Val.extern_value allocsite loc in
        gen_block pname allocinfo node ext_v mem

  let handle_api pname allocinfo loc node (ret, exps) mem api_type =
    let arg_typs = api_type.arg_typs in
    let ret_typ = api_type.ret_typ in
    let src_vals = collect_src_vals exps arg_typs loc mem in
    let dst_vals = collect_dst_vals exps arg_typs loc mem in
    let buf_vals = collect_buf_vals exps arg_typs loc mem in
    let size_vals = collect_size_vals exps arg_typs loc mem in
    let mem =
      process_args pname allocinfo loc node exps arg_typs src_vals mem
    in
    match ret with
    | Some (id, _) ->
        let va_src_flag =
          IList.exists (function | Src (Variable, _, _) -> true | _ -> false) arg_typs
        in
        let (mem, ret_v) =
          produce_ret pname allocinfo loc node ret_typ
            va_src_flag src_vals dst_vals buf_vals size_vals mem in

        Dom.Mem.add_stack (Loc.of_var (Var.of_id id)) ret_v mem
    | None -> mem

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
    | fname when ApiMap.mem fname api_map ->
        let api_type = ApiMap.find fname api_map in
        (*  pname inst_num position loc node (ret, exps) (mem, global) mode api_type *)
        handle_api pname (0, 0) loc node (ret, fst (IList.split params)) mem api_type
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

  let rec declare_symbolic_array
      pname tenv node loc typ ~inst_num ~sym_num ~dim mem threshold =
    if threshold = 0 then (mem, sym_num) else
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
          declare_symbolic_array
            pname tenv node field typ ~inst_num ~sym_num ~dim:(dim+1) mem (threshold-1)
      | _ -> (mem, sym_num)
    in
    let offset = Itv.make_sym pname sym_num in
    let sym_num = sym_num + 2 in (* TODO *)
    let size = Itv.make_sym pname sym_num in
    let sym_num = sym_num + 2 in (* TODO *)
    let arr =
      Sem.eval_array_alloc pname node typ offset size inst_num dim
    in
    let mem = Dom.Mem.add_heap loc arr mem in
    let (mem, sym_num) =
      match typ with
      | Typ.Tstruct typename ->
          (match Tenv.lookup tenv typename with
           | Some str ->
               IList.fold_left decl_fld (mem, sym_num) str.StructTyp.fields
           | _ -> (mem, sym_num))
      | Typ.Tint _ ->
          let (elem_val, sym_num) = Dom.Val.make_sym pname sym_num in
          let arr_loc = arr |> Dom.Val.get_array_blk |> ArrayBlk.get_pow_loc in
          let mem = Dom.Mem.strong_update_heap arr_loc elem_val mem in
          (mem, sym_num)
      | Typ.Tptr (typ, _) ->
          let v = Dom.Mem.find_heap loc mem in
          let loc =
            let locs = Dom.Val.get_all_locs v in
            assert(PowLoc.cardinal locs = 1);
            PowLoc.choose locs
          in
          declare_symbolic_array
            pname tenv node loc typ ~inst_num ~sym_num ~dim:(dim+1) mem (threshold-1)
      | _ -> (mem, sym_num)
    in
    (mem, sym_num)


  let declare_symbolic_parameter pdesc tenv node inst_num mem threshold =
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
              ~inst_num ~sym_num ~dim:1 mem threshold
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
        let ovf_subst_map =
          Sem.get_ovf_subst tenv pdesc params caller_m callee_entry_m loc
        in
        let taint_subst_map =
          Sem.get_taint_subst tenv pdesc params caller_m callee_entry_m loc
        in
        let ret_loc = Loc.of_pvar (Pvar.get_ret_pvar callee_pname) in
        let ret_val = Dom.Mem.find_heap ret_loc callee_exit_m in
        Dom.Val.subst ret_val ovf_subst_map taint_subst_map
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

  let rec update_all_ret_val ret_val visited_locs src_mem tgt_mem =
    let pow_loc = PowLoc.diff (Dom.Val.get_all_locs ret_val) visited_locs in
    let visited_locs = PowLoc.union pow_loc visited_locs in
    if PowLoc.cardinal pow_loc = 0 then tgt_mem else
      let new_val = Dom.Mem.find_heap_set pow_loc src_mem in
      let tgt_mem = Dom.Mem.update_mem pow_loc new_val tgt_mem in
      update_all_ret_val new_val visited_locs src_mem tgt_mem


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
             let src_m = Dom.Summary.get_output summary in
             let mem' = Dom.Mem.add_stack (Loc.of_var (Var.of_id id)) ret_val mem in
             update_all_ret_val ret_val PowLoc.empty src_m mem'
         | _ -> mem)
    | None -> handle_unknown_call pname ret callee_pname params node mem loc

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
          call_sem pdata node loc callee_pname params ret mem
      | Declare_locals (locals, _) ->
          (* array allocation in stack e.g., int arr[10] *)
          let (mem, inst_num) =
            IList.fold_left try_decl_arr (mem, 1) locals
          in
          declare_symbolic_parameter pdesc tenv node inst_num mem 3
      (* TODO IF main argc, argv strong update look formals *)
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
  module Semantics = IntOvfSemantics.Make (CFG)
  module Sem = Semantics
  module TransferFunctions = TransferFunctions (CFG)

  type extras = Procname.t -> Procdesc.t option

  let instantiate_cond
  = fun tenv caller_pname callee_pdesc params caller_mem summary loc ->
    let callee_entry_mem = Dom.Summary.get_input summary in
    let callee_cond = Dom.Summary.get_cond_set summary in
    match callee_pdesc with
    | Some pdesc ->
      let taint_subst : TaintSet.astate TaintSet.SubstMap.t =
        Sem.get_taint_subst tenv pdesc params caller_mem callee_entry_mem loc
      in
      let ovf_subst =
        Sem.get_ovf_subst tenv pdesc params caller_mem callee_entry_mem loc
      in
      let pname = Procdesc.get_proc_name pdesc in
      Dom.ConditionSet.subst 
        callee_cond ovf_subst taint_subst caller_pname pname loc
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
    |> SinkMap.add "malloc" 0
    |> SinkMap.add "__new_array" 0
    |> SinkMap.add "realloc" 0 
    |> SinkMap.add "calloc" 1 

  let add_cond_n n pname loc params mem cond_set =
    match IList.nth params n with
    | (e, _) ->
        let p = Sem.eval e mem loc in
        let v = Dom.Mem.find_heap_set (Dom.Val.get_all_locs p) mem in
        let o = Dom.Val.get_ovf v in
        (if Config.ropas_debug >= 2 then
           (F.fprintf F.err_formatter "@[<v 2>Add condition :@,";
            F.fprintf F.err_formatter "Pname: %s@," (Procname.to_string pname);
            F.fprintf F.err_formatter "Sink: %a@," OvfSet.pp o;
            F.fprintf F.err_formatter "@]@."));
        Dom.ConditionSet.add_int_ovf_safety pname loc o cond_set
    | exception _ -> assert false

  let add_conds caller callee loc params mem cond_set =
    match SinkMap.find (Procname.to_string callee) sink_funcs with
    | n -> add_cond_n n caller loc params mem cond_set
    | exception Not_found -> cond_set

  let collect_instr
    : extras ProcData.t -> CFG.node -> Dom.ConditionSet.t * Dom.Mem.t
      -> Sil.instr -> Dom.ConditionSet.t * Dom.Mem.t
  = fun ({ pdesc; tenv; extras } as pdata) node (cond_set, mem) instr ->
    let pname = Procdesc.get_proc_name pdesc in
    let cond_set =
      match instr with
      | Sil.Call (_, Const (Cfun callee_pname), params, loc, _) ->
          let cond_set = add_conds pname callee_pname loc params mem cond_set in
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

  let report_error tenv pdesc conds =
    let pname = Procdesc.get_proc_name pdesc in
    let report1 cond acc =
      let safe = Dom.Condition.check cond in
      let (caller_pname, loc) =
        match Dom.Condition.get_trace cond with
        | Dom.Condition.Inter (caller_pname, _, loc) -> (caller_pname, loc)
        | Dom.Condition.Intra pname -> (pname, Dom.Condition.get_location cond)
      in
      (* report symbol-related alarms only in debug mode *)
      if not safe && Procname.equal pname caller_pname then
        (F.fprintf F.err_formatter "report error!";
        let fs_kind = "FORMAT-STRING CHECKER" in
        let cond_str = Dom.Condition.to_string cond in
        Checkers.ST.report_error tenv pname pdesc fs_kind loc cond_str;
        Dom.ConditionSet.remove cond acc)
      else acc

    in
    Dom.ConditionSet.fold report1 conds conds

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
    let cond_set =
      if not Config.ropas_report then Report.report_error tenv pdesc cond_set
      else cond_set
    in
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
