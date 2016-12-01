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

module Summary = Summary.Make (struct
    type summary = BufferOverrunDomain.astate

    let update_payload astate payload = 
      { payload with Specs.interval = Some astate }

    let read_from_payload payload =
      payload.Specs.interval
  end)

module SubstMap = Map.Make(struct type t = Itv.Bound.t let compare = Itv.Bound.compare end)
module EntryMap = Map.Make(struct type t = Procname.t let compare = Pervasives.compare end)

module TransferFunctions (CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = BufferOverrunDomain
  type extras = Procname.t -> Procdesc.t option
  let entry_map = ref EntryMap.empty 

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

  let conditions = ref Domain.ConditionSet.initial

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
        let size = eval size mem (CFG.loc node) |> Domain.Val.get_itv in
        Domain.Mem.add_stack (Loc.of_id id) (eval_array_alloc pdesc node typ Itv.zero size 0 1) mem
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
    let arr = eval_array_alloc pdesc node typ Itv.zero size inst_num dimension in
    let mem = if dimension = 1 then Domain.Mem.add_stack loc arr mem else Domain.Mem.add_heap loc arr mem 
    in
    let loc = Loc.of_allocsite (get_allocsite pdesc node inst_num dimension) in
    match typ with 
      Typ.Tarray (typ, Some len) -> 
        declare_array pdesc node loc typ len inst_num (dimension + 1) mem
    | _ -> mem

  let declare_symbolic_array pdesc tenv node loc typ inst_num dimension mem =
    let (offset, size) = (Itv.get_new_sym (), Itv.get_new_sym ()) in
    let mem = Domain.Mem.add_heap loc (eval_array_alloc pdesc node typ offset size inst_num dimension) mem in
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
                  Domain.Mem.add_heap field (eval_array_alloc pdesc node typ offset size inst_num dimension) mem
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
    : Exp.t -> Domain.TempAlias.astate -> Domain.Mem.astate -> Domain.Mem.astate
  = fun e ta mem ->
    match e with
    | Exp.Var x ->
        (match Domain.TempAlias.find x ta with
         | Some x' ->
             let lv = Loc.of_pvar x' in
             let v = Domain.Mem.find_heap lv mem in
             let v' = Domain.Val.prune v Domain.Val.zero in
             update_mem (PowLoc.singleton lv) v' mem
         | None -> mem)
    | Exp.UnOp (Unop.LNot, Exp.Var x, _) ->
        (match Domain.TempAlias.find x ta with
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
    : Exp.t -> Domain.TempAlias.astate -> Location.t -> Domain.Mem.astate
      -> Domain.Mem.astate
  = fun e ta loc mem ->
    match e with
    | Exp.BinOp (Binop.Lt as comp, Exp.Var x, e')
    | Exp.BinOp (Binop.Gt as comp, Exp.Var x, e')
    | Exp.BinOp (Binop.Le as comp, Exp.Var x, e')
    | Exp.BinOp (Binop.Ge as comp, Exp.Var x, e') ->
        (match Domain.TempAlias.find x ta with
         | Some x' ->
             let lv = Loc.of_pvar x' in
             let v = Domain.Mem.find_heap lv mem in
             let v' = Domain.Val.prune_comp comp v (eval e' mem loc) in
             update_mem (PowLoc.singleton lv) v' mem
         | None -> mem)
    | Exp.BinOp (Binop.Eq, Exp.Var x, e') ->
        (match Domain.TempAlias.find x ta with
         | Some x' ->
             let lv = Loc.of_pvar x' in
             let v = Domain.Mem.find_heap lv mem in
             let v' = Domain.Val.prune_eq v (eval e' mem loc) in
             update_mem (PowLoc.singleton lv) v' mem
         | None -> mem)
    | Exp.BinOp (Binop.Ne, Exp.Var x, e') ->
        (match Domain.TempAlias.find x ta with
         | Some x' ->
             let lv = Loc.of_pvar x' in
             let v = Domain.Mem.find_heap lv mem in
             let v' = Domain.Val.prune_ne v (eval e' mem loc) in
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
    : Exp.t -> Domain.TempAlias.astate -> Location.t -> Domain.Mem.astate
      -> Domain.Mem.astate
  = fun e ta loc mem ->
    match e with
    | Exp.BinOp (Binop.Lt as c, e', Exp.Var x)
    | Exp.BinOp (Binop.Gt as c, e', Exp.Var x)
    | Exp.BinOp (Binop.Le as c, e', Exp.Var x)
    | Exp.BinOp (Binop.Ge as c, e', Exp.Var x)
    | Exp.BinOp (Binop.Eq as c, e', Exp.Var x)
    | Exp.BinOp (Binop.Ne as c, e', Exp.Var x) ->
        prune_binop_left (Exp.BinOp (comp_rev c, Exp.Var x, e')) ta loc mem
    | _ -> mem

  let rec prune
    : Exp.t -> Domain.TempAlias.astate -> Location.t -> Domain.Mem.astate
      -> Domain.Mem.astate
  = fun e ta loc mem ->
    let mem =
      mem
      |> prune_unop e ta
      |> prune_binop_left e ta loc
      |> prune_binop_right e ta loc
    in
    match e with
    | Exp.BinOp (Binop.Ne, e, Exp.Const (Const.Cint i)) when IntLit.iszero i ->
        prune e ta loc mem
    | Exp.BinOp (Binop.Eq, e, Exp.Const (Const.Cint i)) when IntLit.iszero i ->
        prune (Exp.UnOp (Unop.LNot, e, None)) ta loc mem
    | Exp.UnOp (Unop.Neg, Exp.Var x, _) -> prune (Exp.Var x) ta loc mem
    | Exp.BinOp (Binop.LAnd, e1, e2) ->
        mem |> prune e1 ta loc |> prune e2 ta loc
    | Exp.UnOp (Unop.LNot, Exp.BinOp (Binop.LOr, e1, e2), t) ->
        mem
        |> prune (Exp.UnOp (Unop.LNot, e1, t)) ta loc
        |> prune (Exp.UnOp (Unop.LNot, e2, t)) ta loc
    | Exp.UnOp (Unop.LNot, Exp.BinOp (Binop.Lt as c, e1, e2), _)
    | Exp.UnOp (Unop.LNot, Exp.BinOp (Binop.Gt as c, e1, e2), _)
    | Exp.UnOp (Unop.LNot, Exp.BinOp (Binop.Le as c, e1, e2), _)
    | Exp.UnOp (Unop.LNot, Exp.BinOp (Binop.Ge as c, e1, e2), _)
    | Exp.UnOp (Unop.LNot, Exp.BinOp (Binop.Eq as c, e1, e2), _)
    | Exp.UnOp (Unop.LNot, Exp.BinOp (Binop.Ne as c, e1, e2), _) ->
        prune (Exp.BinOp (comp_not c, e1, e2)) ta loc mem
    | _ -> mem

  let get_formals : Procdesc.t -> (Pvar.t * Typ.t) list
  = fun pdesc ->
    let proc_name = Procdesc.get_proc_name pdesc in
    Procdesc.get_formals pdesc |> IList.map (fun (name, typ) -> (Pvar.mk name proc_name, typ))

  let init_conditions astate = conditions := Domain.get_conds astate
  let get_conditions () = !conditions

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

   
  let instantiate tenv callee_pdesc callee_pname params caller_mem callee_mem callee_conds loc =
    try 
    (* TODO: remove fold_left2 exception catch by addressing variable arguments *)
    let callee_entry_mem = EntryMap.find callee_pname !entry_map in
    match callee_pdesc with 
      Some pdesc ->
        let pairs = 
          IList.fold_left2 (fun l (formal, typ) (actual,_) ->
              let formal = Domain.Mem.find_heap (Loc.of_pvar formal) callee_entry_mem in
              let actual = eval actual caller_mem loc in
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
        let (new_mem, new_cond) = 
          (Domain.Mem.add_heap ret_loc new_ret_val callee_mem, Domain.ConditionSet.subst callee_conds subst_map)
        in
        (if Config.debug_mode then 
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
        end);
        (new_mem, new_cond)
    | _ -> (callee_mem, callee_conds)
  with _ -> (callee_mem, callee_conds)

  let add_condition : Procdesc.t -> CFG.node -> Exp.t -> Location.t -> Domain.Mem.astate -> unit
  = fun pdesc node exp loc mem ->
    let array_access = 
      match exp with 
      | Exp.Var _ -> 
        Some (eval exp mem loc |> Domain.Val.get_array_blk, 
              Itv.zero)
      | Exp.Lindex (e1, e2)
      | Exp.BinOp (Binop.PlusA, e1, e2) 
      | Exp.BinOp (Binop.MinusA, e1, e2) -> 
          Some (eval e1 mem loc |> Domain.Val.get_array_blk, 
           eval e2 mem loc |> Domain.Val.get_itv)
      | _ -> None
    in
    match array_access with
      Some (arr, idx) -> 
        let site = get_allocsite pdesc node 0 0 in
        let size = ArrayBlk.sizeof arr in
        let offset = ArrayBlk.offsetof arr in
        let idx = Itv.plus offset idx in
        if size <> Itv.bot && idx <> Itv.bot then 
          (if Config.debug_mode then
             (F.fprintf F.err_formatter "@[<v 2>Add condition :@,";
              F.fprintf F.err_formatter "array: %a@," ArrayBlk.pp arr;
              F.fprintf F.err_formatter "  idx: %a@," Itv.pp idx;
              F.fprintf F.err_formatter "@]@.");
           conditions := Domain.ConditionSet.add_bo_safety
               pdesc site ~size ~idx loc !conditions)
    | None -> ()

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
   
  let exec_instr ((mem, conds, ta) as astate) { ProcData.pdesc; tenv; extras }
      node (instr : Sil.instr) =
    init_conditions astate;
    let output_astate =
      match instr with
      | Load (id, exp, _, loc) ->
          add_condition pdesc node exp loc mem;
          let locs = eval exp mem loc |> Domain.Val.get_all_locs in
          let v = Domain.Mem.find_heap_set locs mem in
          (Domain.Mem.add_stack (Loc.of_var (Var.of_id id)) v mem,
           get_conditions (),
           Domain.TempAlias.load id exp ta)
      | Store (exp1, _, exp2, loc) ->
          add_condition pdesc node exp1 loc mem;
(*          add_condition pdesc node exp2 loc mem;*)
          let locs = eval exp1 mem loc |> Domain.Val.get_all_locs in
          (update_mem locs (eval exp2 mem loc) mem,
           get_conditions (),
           Domain.TempAlias.store exp1 exp2 ta)
      | Prune (exp, loc, _, _) ->
          (prune exp ta loc mem, get_conditions (), ta)
      | Call (ret, Const (Cfun callee_pname), params, loc, _) ->
          let callee = extras callee_pname in
          let old_conds = get_conditions () in
          begin
            match Summary.read_summary tenv pdesc callee_pname with
            | Some (callee_mem, callee_cond, _) -> 
              let (new_mem, new_conds) = instantiate tenv callee callee_pname params mem callee_mem callee_cond loc in
              let new_mem = 
                match ret with Some (id,_) -> 
                  Domain.Mem.add_stack (Loc.of_var (Var.of_id id))
                   (Domain.Mem.find_heap (Loc.of_pvar (Pvar.get_ret_pvar callee_pname)) new_mem) mem
                | _ -> mem
              in
              (new_mem, Domain.ConditionSet.join old_conds new_conds, ta)
            | None -> (handle_unknown_call pdesc ret callee_pname params node mem, old_conds, ta)
          end
      | Call (_, _, _, _, _) -> astate
      | Declare_locals (locals, _) ->
          (* static array allocation *)
          let mem = IList.fold_left (fun (mem, c) (pvar, typ) ->
              match typ with
                Typ.Tarray (typ, Some len) ->
                  (declare_array pdesc node (Loc.of_var (Var.of_pvar pvar)) typ len c 1 mem, c+1)
              | _ -> (mem, c)) (mem, 1) locals
                    |> fst
          in
          (* formal parameters *)
          IList.fold_left (fun (mem, c) (pvar, typ) ->
              match typ with
                Typ.Tint _ -> (Domain.Mem.add_heap (Loc.of_pvar pvar) (Domain.Val.get_new_sym ()) mem, c+1)
              | Typ.Tptr (typ, _) ->
                  (declare_symbolic_array pdesc tenv node (Loc.of_pvar pvar) typ c 1 mem, c+1)
              | _ -> (mem, c) (* TODO *)) (mem, 0) (get_formals pdesc)
          |> (fun (mem, _) -> 
                let proc_name = Procdesc.get_proc_name pdesc in
                entry_map := EntryMap.add proc_name mem !entry_map;
                (mem, conds, ta))
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

module Interprocedural = Analyzer.Interprocedural (Summary)
module Domain = BufferOverrunDomain

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
  

let checker ({ Callbacks.get_proc_desc; Callbacks.tenv; proc_desc } as callback) =
  let post = Interprocedural.checker callback get_proc_desc in
  match post with 
  | Some post ->
      let proc_name = Procdesc.get_proc_name proc_desc in
      F.fprintf F.err_formatter "@.@[<v 2>Summary of %a :@,@," Procname.pp proc_name;
      Domain.pp_summary F.err_formatter post;
      F.fprintf F.err_formatter "@]@.";
      if Procname.to_string proc_name = "main" then
(*        report_error tenv proc_desc (Domain.get_conds post |> Domain.ConditionSet.merge)*)
        my_report_error tenv proc_desc (Domain.get_conds post |> Domain.ConditionSet.merge)        
  | _ -> ()
