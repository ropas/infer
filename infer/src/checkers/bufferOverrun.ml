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


module TransferFunctions (CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = BufferOverrunDomain
  type extras = Procname.t -> Procdesc.t option

  exception Not_implemented 

  let eval_const : Const.t -> Domain.Val.astate = function 
    | Const.Cint intlit -> 
        Domain.Val.of_int (IntLit.to_int intlit)
    | _ -> Domain.Val.of_int (-999)

  let sizeof : Typ.t -> int
  = fun t ->
    (* TODO *)
    4
  let conditions = ref Domain.Conds.initial

  let rec eval : Exp.t -> Domain.Mem.astate -> Domain.Val.astate
  = fun exp mem ->
    match exp with
    (* Pure variable: it is not an lvalue *)
    | Exp.Var _
    (* The address of a program variable *)
    | Exp.Lvar _ -> Domain.Mem.find_set (eval_lv exp mem) mem
    | Exp.UnOp (uop, e, _) -> eval_unop uop e mem
    | Exp.BinOp (bop, e1, e2) -> eval_binop bop e1 e2 mem
    | Exp.Const c -> eval_const c
    (* Type cast *)
(*    | Cast Typ.t t *)
    (* A field offset, the type is the surrounding struct type *)
(*    | Lfield t Ident.fieldname Typ.t *)
    | Exp.Lindex (e1, e2) -> 
        add_condition e1 e2 mem;
        let locs = Domain.Mem.find_set (eval_lv e1 mem) mem
          |> Domain.Val.get_array_blk 
          |> ArrayBlk.pow_loc_of_array
        in
        Domain.Mem.find_set locs mem
    | Exp.Sizeof (typ, _, _) -> Domain.Val.of_int (sizeof typ)
(*    | Exp.Exn _ -> 
    | Exp.Closure _ -> *)
    | _ -> raise Not_implemented
  and eval_lv : Exp.t -> Domain.Mem.astate -> PowLoc.t
  = fun e mem ->
    match e with 
    | Exp.Var id -> Var.of_id id |> Loc.of_var |> PowLoc.singleton
    | Exp.Lvar pvar -> Var.of_pvar pvar |> Loc.of_var |> PowLoc.singleton
    | Exp.Lindex (e1, e2) -> 
        add_condition e1 e2 mem;
        eval e1 mem |> Domain.Val.get_array_blk |> ArrayBlk.pow_loc_of_array
    | _ -> raise Not_implemented

  and add_condition : Exp.t -> Exp.t -> Domain.Mem.astate -> unit
  = fun arr idx astate ->
    let size = eval arr astate |> Domain.Val.get_array_blk |> ArrayBlk.sizeof in
    let idx = eval idx astate |> Domain.Val.get_itv in
    conditions := Domain.Conds.add_bo_safety ~size ~idx !conditions

  and eval_unop : Unop.t -> Exp.t -> Domain.Mem.astate -> Domain.Val.astate 
  = fun unop e mem -> 
    let v = eval e mem in
    match unop with
    | Unop.Neg -> Domain.Val.neg v
    | Unop.BNot -> Domain.Val.unknown_bit v
    | Unop.LNot -> Domain.Val.lnot v

  and eval_binop
    : Binop.t -> Exp.t -> Exp.t -> Domain.Mem.astate -> Domain.Val.astate 
  = fun binop e1 e2 mem -> 
    let v1 = eval e1 mem in
    let v2 = eval e2 mem in
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

  let eval_array_alloc : Procdesc.t -> CFG.node -> Typ.t -> Exp.t -> int -> int -> Domain.Mem.astate -> Domain.Val.astate
  = fun pdesc node typ size inst_num dimension mem ->
    let allocsite = get_allocsite pdesc node inst_num dimension in
    let offset = Itv.of_int 0 in
    let size = eval size mem |> Domain.Val.get_itv in
    let stride = Itv.of_int 4 in (* TODO *)
    let nullpos = Itv.of_int 0 in (* TODO *)
    ArrayBlk.make allocsite offset size stride nullpos
    |> Domain.Val.of_array_blk

  let handle_unknown_call callee_pname params node astate = 
    match Procname.get_method callee_pname with
      "malloc" -> prerr_endline "print malloc"; astate
    | _ -> astate

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

  let get_formals : Procdesc.t -> (Pvar.t * Typ.t) list
  = fun pdesc ->
    let proc_name = Procdesc.get_proc_name pdesc in
    Procdesc.get_formals pdesc |> IList.map (fun (name, typ) -> (Pvar.mk name proc_name, typ))

  let init_conditions astate = conditions := Domain.get_conds astate
  let get_conditions () = !conditions

  module SubstMap = Map.Make(struct type t = Itv.Bound.t let compare = Pervasives.compare end)
  let report_error : Tenv.t -> Procdesc.t -> Domain.Conds.t -> Itv.Bound.t SubstMap.t -> unit 
  = fun tenv proc_desc callee_conds subst_map -> 
    let sym_map = SubstMap.fold (fun formal actual map ->
        match formal, actual with 
          Itv.Bound.V (0, se1), Itv.Bound.V (c, se2) when Itv.SymExp.cardinal se1 = 1 && Itv.SymExp.cardinal se2 = 0 -> 
            let (symbol, coeff) = Itv.SymExp.choose se1 in
            if coeff = 1 then
              Itv.SubstMap.add symbol c map
            else map
        | _ -> map) subst_map Itv.SubstMap.empty
    in
    let new_conds = Domain.Conds.fold (fun cond conds -> 
        Domain.Conds.add (Domain.Conds.subst cond sym_map) conds) callee_conds Domain.Conds.initial
    in
    Domain.Conds.pp F.err_formatter new_conds;
    Domain.Conds.iter (fun cond ->
        let checked = Domain.Conds.check cond in
        if checked <> Itv.one then
          Checkers.ST.report_error tenv
            (Procdesc.get_proc_name proc_desc)
            proc_desc
            "CHECKERS_MY_SIMPLE_CHECKER"
            Location.dummy
            "A description of my simple checker"
        else ()) new_conds;
    ()

  let check_bo tenv callee_pdesc params caller_mem callee_mem callee_cond = 
    match callee_pdesc with 
      Some pdesc ->
        let formals = get_formals pdesc |> IList.map (fun (p, _) -> let loc = Loc.of_pvar p in Domain.Mem.find loc callee_mem) in
        let actuals = IList.map (fun (p, _) -> eval p caller_mem) params in
        let subst_map = IList.fold_left2 (fun map formal actual ->
              let formal_itv = Domain.Val.get_itv formal in
              let actual_itv = Domain.Val.get_itv actual in
              if formal_itv <> Itv.bot && actual_itv <> Itv.bot then
                map 
                |> SubstMap.add (Itv.lb formal_itv) (Itv.lb actual_itv)
                |> SubstMap.add (Itv.ub formal_itv) (Itv.ub actual_itv)
              else map) SubstMap.empty formals actuals
        in
        report_error tenv pdesc callee_cond subst_map
    | _ -> ()
    
  let exec_instr ((mem, conds) as astate) { ProcData.pdesc; tenv; extras } node (instr : Sil.instr) = 
    Sil.pp_instr Utils.pe_text F.err_formatter instr;
    prerr_newline ();
    Domain.pp F.err_formatter astate;
    prerr_newline ();

    init_conditions astate;
    match instr with
    | Load (id, exp, _, loc) ->
        (Domain.Mem.add (Loc.of_var (Var.of_id id)) (eval exp mem) mem, get_conditions ())
    | Store (exp1, _, exp2, loc) ->
        (update_mem (eval_lv exp1 mem) (eval exp2 mem) mem, get_conditions ())
    | Prune (exp, loc, _, _) -> astate
    | Call (ret, Const (Cfun callee_pname), params, loc, _) when extras callee_pname = None -> (* unknown function *)
        prerr_endline "UNKNOWN FUNCTION";
        astate
    | Call (Some (id, _), Const (Cfun callee_pname), params, loc, _) ->
        let callee = extras callee_pname in
(*        (match callee with 
          Some pdesc -> 
            let formals = get_formals pdesc in
            IList.iter (fun (f,typ) -> Pvar.pp pe_text F.err_formatter f) formals
         | _ -> ());*)
        let call_site = CallSite.make callee_pname loc in
        let (callee_mem, callee_cond) = 
          match Summary.read_summary tenv pdesc callee_pname with
          | Some astate -> astate
          | None -> handle_unknown_call callee_pname params node Domain.initial
        in
        check_bo tenv callee params mem callee_mem callee_cond;
        (Domain.Mem.add (Loc.of_var (Var.of_id id)) (Domain.Mem.find (Loc.of_var (Var.of_pvar (Pvar.get_ret_pvar callee_pname))) callee_mem) mem, get_conditions ())
    | Call (_, _, params, loc, _) -> astate
    | Declare_locals (locals, _) -> 
        let mem = IList.fold_left (fun (mem,c) (pvar, typ) ->
            match typ with 
              Typ.Tarray (_, _) ->
                (declare_array pdesc node (Loc.of_var (Var.of_pvar pvar)) typ c 1 mem, c+1)
            | _ -> (mem, c)) (mem, 1) locals 
          |> fst
        in
        IList.fold_left (fun (mem,c) (pvar, typ) -> 
            match typ with
              Typ.Tint _ -> (Domain.Mem.add (Loc.of_pvar pvar) (Domain.Val.get_new_sym ()) mem, c+1)
            | _ -> (mem, c) (* TODO *)) (mem, 0) (get_formals pdesc)
        |> (fun (mem, _) -> (mem, conds))
    | Remove_temps _ | Abstract _ | Nullify _ -> astate
end

module Analyzer =
  AbstractInterpreter.Make
    (ProcCfg.Normal)
    (Scheduler.ReversePostorder)
    (TransferFunctions)

module Interprocedural = Analyzer.Interprocedural (Summary)

let checker ({ Callbacks.get_proc_desc; Callbacks.tenv; proc_desc } as callback) =
  let post = Interprocedural.checker callback get_proc_desc in
  ()
