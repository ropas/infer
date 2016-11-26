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

module SubstMap = Map.Make(struct type t = Itv.Bound.t let compare = Pervasives.compare end)

module TransferFunctions (CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = BufferOverrunDomain
  type extras = Procname.t -> Procdesc.t option

  exception Not_implemented 

  let eval_const : Const.t -> Domain.Val.astate = function 
    | Const.Cint intlit -> 
        Domain.Val.of_int (IntLit.to_int intlit)
    | _ -> Domain.Val.of_int (-999) (* TODO *)

  let sizeof : Typ.t -> int
  = fun t ->
    (* TODO *)
    4
  let conditions = ref Domain.ConditionSet.initial

  let rec eval : Exp.t -> Domain.Mem.astate -> Location.t -> Domain.Val.astate
  = fun exp mem loc ->
    match exp with
    (* Pure variable: it is not an lvalue *)
    | Exp.Var id -> Domain.Mem.find (Var.of_id id |> Loc.of_var) mem
    (* The address of a program variable *)
    | Exp.Lvar pvar -> pvar |> Var.of_pvar |> Loc.of_var |> PowLoc.singleton |> Domain.Val.of_pow_loc
    | Exp.UnOp (uop, e, _) -> eval_unop uop e mem loc
    | Exp.BinOp (bop, e1, e2) -> eval_binop bop e1 e2 mem loc
    | Exp.Const c -> eval_const c
    (* Type cast *)
(*    | Cast Typ.t t *)
    (* A field offset, the type is the surrounding struct type *)
(*    | Lfield t Ident.fieldname Typ.t *)
    | Exp.Lindex (e1, e2) -> 
        let arr = eval e1 mem loc |> Domain.Val.get_pow_loc |> flip Domain.Mem.find_set mem in
        let idx = eval e2 mem loc in
        add_condition arr idx loc;
        arr
        |> Domain.Val.get_array_blk 
        |> ArrayBlk.pow_loc_of_array
        |> Domain.Val.of_pow_loc
    | Exp.Sizeof (typ, _, _) -> Domain.Val.of_int (sizeof typ)
(*    | Exp.Exn _ -> 
    | Exp.Closure _ -> *)
    | _ -> raise Not_implemented
  and add_condition : Domain.Val.t -> Domain.Val.t -> Location.t -> unit
  = fun arr idx loc ->
    let size = arr |> Domain.Val.get_array_blk |> ArrayBlk.sizeof in
    let idx = idx |> Domain.Val.get_itv in
    conditions := Domain.ConditionSet.add_bo_safety ~size ~idx loc !conditions

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
    | Binop.PlusA -> Domain.Val.plus v1 v2
    | Binop.PlusPI -> raise Not_implemented
    | Binop.MinusA -> Domain.Val.minus v1 v2
    | Binop.MinusPI -> raise Not_implemented
    | Binop.MinusPP -> raise Not_implemented
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
    : Procdesc.t -> CFG.node -> Typ.t -> Exp.t -> int -> int
      -> Domain.Mem.astate -> Domain.Val.astate
  = fun pdesc node typ size inst_num dimension mem ->
    let allocsite = get_allocsite pdesc node inst_num dimension in
    let offset = Itv.of_int 0 in
    let size = eval size mem (CFG.loc node) |> Domain.Val.get_itv in
    let stride = Itv.of_int 4 in (* TODO *)
    let nullpos = Itv.of_int 0 in (* TODO *)
    ArrayBlk.make allocsite offset size stride nullpos
    |> Domain.Val.of_array_blk

  let handle_unknown_call ret callee_pname params node astate = 
    match Procname.get_method callee_pname with
      "malloc" -> prerr_endline "print malloc"; astate
    | _ ->
      (match ret with 
         Some (id, _) -> 
          prerr_endline "handle";
          let ret_loc = Loc.of_var (Var.of_pvar (Pvar.get_ret_pvar callee_pname)) in
          (Domain.Mem.add ret_loc Domain.Val.top_itv (Domain.get_mem astate),
           Domain.get_conds astate,
           Domain.get_temp_alias astate)
       | None -> astate)

  let rec declare_array pdesc node loc typ inst_num dimension mem = 
    match typ with 
      Typ.Tarray (typ, Some len) -> 
(*      prerr_endline "Tarray";
        IntLit.pp F.err_formatter len;
          Loc.pp  F.err_formatter loc;
          Typ.pp_full pe_text F.err_formatter typ;
*)
        let size = Exp.Const (Const.Cint len) in
        let mem = Domain.Mem.add loc (eval_array_alloc pdesc node typ size inst_num dimension mem) mem in
        let loc = Loc.of_allocsite (get_allocsite pdesc node inst_num dimension) in
        declare_array pdesc node loc typ inst_num (dimension + 1) mem
    | _ -> mem

  let can_strong_update ploc =
    if PowLoc.cardinal ploc = 1 then 
      let lv = PowLoc.choose ploc in
      Loc.is_var lv
    else false

  let update_mem : PowLoc.t -> Domain.Val.t -> Domain.Mem.astate -> Domain.Mem.astate
  = fun ploc v s ->
    if can_strong_update ploc then Domain.Mem.strong_update ploc v s
    else Domain.Mem.weak_update ploc v s

  let prune_unop
    : Exp.t -> Domain.TempAlias.astate -> Domain.Mem.astate -> Domain.Mem.astate
  = fun e ta mem ->
    match e with
    | Exp.Var x ->
        (match Domain.TempAlias.find x ta with
         | Some x' ->
             let lv = PowLoc.of_pvar x' in
             let v = Domain.Mem.find_set lv mem in
             let v' = Domain.Val.prune v Domain.Val.zero in
             update_mem lv v' mem
         | None -> mem)
    | Exp.UnOp (Unop.LNot, Exp.Var x, _) ->
        (match Domain.TempAlias.find x ta with
         | Some x' ->
             let lv = PowLoc.of_pvar x' in
             let v = Domain.Mem.find_set lv mem in
             let v' = (Domain.Val.get_itv Domain.Val.zero,
                       Domain.Val.get_pow_loc v,
                       Domain.Val.get_array_blk v) in
             update_mem lv v' mem
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
             let lv = PowLoc.of_pvar x' in
             let v = Domain.Mem.find_set lv mem in
             let v' = Domain.Val.prune_comp comp v (eval e' mem loc) in
             update_mem lv v' mem
         | None -> mem)
    | Exp.BinOp (Binop.Eq, Exp.Var x, e') ->
        (match Domain.TempAlias.find x ta with
         | Some x' ->
             let lv = PowLoc.of_pvar x' in
             let v = Domain.Mem.find_set lv mem in
             let v' = Domain.Val.prune_eq v (eval e' mem loc) in
             update_mem lv v' mem
         | None -> mem)
    | Exp.BinOp (Binop.Ne, Exp.Var x, e') ->
        (match Domain.TempAlias.find x ta with
         | Some x' ->
             let lv = PowLoc.of_pvar x' in
             let v = Domain.Mem.find_set lv mem in
             let v' = Domain.Val.prune_ne v (eval e' mem loc) in
             update_mem lv v' mem
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
(*
  let report_error : Tenv.t -> Procdesc.t -> Domain.Conds.t -> Itv.Bound.t SubstMap.t -> Domain.Conds.t
  = fun tenv proc_desc callee_conds subst_map -> 
    let sym_map = SubstMap.fold (fun formal actual map ->
        match formal with 
          Itv.Bound.V (0, se1) when Itv.SymExp.cardinal se1 = 1 -> 
            let (symbol, coeff) = Itv.SymExp.choose se1 in
            if coeff = 1 then
              Itv.SubstMap.add symbol actual map
            else (* impossible *) map
        | _ -> (* impossible *) map) subst_map Itv.SubstMap.empty
    in
    let new_conds = Domain.Conds.fold (fun cond conds -> 
        Domain.Conds.add (Domain.Conds.subst cond sym_map) conds) callee_conds Domain.Conds.initial
    in
    Domain.Conds.pp F.err_formatter new_conds;
    F.fprintf F.err_formatter "@.@.";
  (*    let new_conds = Domain.Conds.fold (fun cond conds ->
        let checked = Domain.Conds.check cond in
        if checked <> Itv.one then
          let _ = Checkers.ST.report_error tenv
            (Procdesc.get_proc_name proc_desc)
            proc_desc
            "BUFFER-OVERRUN CHECKER"
            (Domain.Conds.get_location cond)
            (Domain.Conds.string_of_cond cond)
          in
          conds
        else Domain.Conds.add cond conds) new_conds Domain.Conds.initial in*)
    new_conds
*)
  let check_bo tenv callee_pdesc params caller_mem callee_mem callee_conds loc =
    match callee_pdesc with 
      Some pdesc ->
        let formals =
          get_formals pdesc
          |> IList.map
            (fun (p, _) -> Domain.Mem.find (Loc.of_pvar p) callee_mem)
        in
        let actuals = IList.map (fun (p, _) -> eval p caller_mem loc) params in
        let pairs = IList.fold_left2 (fun l formal actual ->
              let formal_itv = Domain.Val.get_itv formal in
              let actual_itv = Domain.Val.get_itv actual in
             (Itv.lb formal_itv, Itv.lb actual_itv) 
             :: (Itv.ub formal_itv, Itv.ub actual_itv) :: l) [] formals actuals
        in
        let subst_map : Itv.Bound.t Itv.SubstMap.t = 
            IList.fold_left (fun map (formal, actual) ->
              match formal with 
                Itv.Bound.V (0, se1) when Itv.SymExp.cardinal se1 = 1 -> 
                  let (symbol, coeff) = Itv.SymExp.choose se1 in
                  if coeff = 1 then
                    Itv.SubstMap.add symbol actual map
                  else (* impossible *) map
              | _ -> (* impossible *) map) Itv.SubstMap.empty pairs
        in
        Domain.ConditionSet.subst callee_conds subst_map
    | _ -> callee_conds
    
  let exec_instr ((mem, conds, ta) as astate) { ProcData.pdesc; tenv; extras }
      node (instr : Sil.instr) =
    Domain.pp F.err_formatter astate;
    F.fprintf F.err_formatter "@.@.";
    Sil.pp_instr Utils.pe_text F.err_formatter instr;
    F.fprintf F.err_formatter "@.";

    init_conditions astate;
    match instr with
    | Load (id, exp, _, loc) ->
        let locs = eval exp mem loc |> Domain.Val.get_pow_loc in
        let v = Domain.Mem.find_set locs mem in
        (Domain.Mem.add (Loc.of_var (Var.of_id id)) v mem,
         get_conditions (),
         Domain.TempAlias.load id exp ta)
    | Store (exp1, _, exp2, loc) ->
        let locs = eval exp1 mem loc |> Domain.Val.get_pow_loc in
        (update_mem locs (eval exp2 mem loc) mem,
         get_conditions (),
         Domain.TempAlias.store exp1 exp2 ta)
    | Prune (exp, loc, _, _) ->
        (prune exp ta loc mem, get_conditions (), ta)
    | Call ((Some (id, _) as ret), Const (Cfun callee_pname), params, loc, _) ->
        let callee = extras callee_pname in
        let call_site = CallSite.make callee_pname loc in
        let old_conds = get_conditions () in
        let (callee_mem, callee_cond, _) =
          match Summary.read_summary tenv pdesc callee_pname with
          | Some astate -> astate
          | None -> handle_unknown_call ret callee_pname params node astate
        in
        let new_conds = check_bo tenv callee params mem callee_mem callee_cond loc in
        (Domain.Mem.add (Loc.of_var (Var.of_id id))
           (Domain.Mem.find (Loc.of_var (Var.of_pvar (Pvar.get_ret_pvar callee_pname))) callee_mem) mem, 
         Domain.ConditionSet.join old_conds new_conds,
         ta)
    | Call (_, _, params, loc, _) -> astate
    | Declare_locals (locals, _) -> 
        let mem = IList.fold_left (fun (mem, c) (pvar, typ) ->
            match typ with 
              Typ.Tarray (_, _) ->
                (declare_array pdesc node (Loc.of_var (Var.of_pvar pvar)) typ c 1 mem, c+1)
            | _ -> (mem, c)) (mem, 1) locals 
          |> fst
        in
        IList.fold_left (fun (mem, c) (pvar, typ) ->
            match typ with
              Typ.Tint _ -> (Domain.Mem.add (Loc.of_pvar pvar) (Domain.Val.get_new_sym ()) mem, c+1)
            | _ -> (mem, c) (* TODO *)) (mem, 0) (get_formals pdesc)
        |> (fun (mem, _) -> (mem, conds, ta))
    | Remove_temps _ | Abstract _ | Nullify _ -> astate
end

module Analyzer =
  AbstractInterpreter.Make
    (ProcCfg.Normal)
    (Scheduler.ReversePostorder)
    (TransferFunctions)

module Interprocedural = Analyzer.Interprocedural (Summary)
module Domain = BufferOverrunDomain

let report_error : Tenv.t -> Procdesc.t -> Domain.ConditionSet.t -> Itv.Bound.t SubstMap.t -> unit 
  = fun tenv proc_desc callee_conds subst_map -> 
    Domain.ConditionSet.pp F.err_formatter callee_conds;
    Domain.ConditionSet.iter (fun cond ->
        let safe = Domain.Condition.check cond in
        if not safe then
          Checkers.ST.report_error tenv
            (Procdesc.get_proc_name proc_desc)
            proc_desc
            "BUFFER-OVERRUN CHECKER"
            (Domain.Condition.get_location cond)
            (Domain.Condition.to_string cond)
        else ()) callee_conds


let checker ({ Callbacks.get_proc_desc; Callbacks.tenv; proc_desc } as callback) =

  let post = Interprocedural.checker callback get_proc_desc in
  match post with 
    Some post ->
      F.fprintf F.err_formatter "Final @.@.";
      Domain.pp F.err_formatter post;
      F.fprintf F.err_formatter "@.@.";
      report_error tenv proc_desc (Domain.get_conds post) SubstMap.empty
  | _ -> ()
