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

  let rec eval : Exp.t -> Domain.astate -> Domain.Val.astate
  = fun exp astate ->
    match exp with
      (* Pure variable: it is not an lvalue *)
    | Exp.Var _
    (* The address of a program variable *)
    | Exp.Lvar _ -> 
        Domain.find_mem_set (eval_lv exp astate) astate
    | Exp.UnOp (uop, e, _) -> eval_unop uop e astate
    | Exp.BinOp (bop, e1, e2) -> eval_binop bop e1 e2 astate
    | Exp.Const c -> eval_const c 
    (* Type cast *)
(*    | Cast Typ.t t *)
    (* A field offset, the type is the surrounding struct type *)
(*    | Lfield t Ident.fieldname Typ.t *)
    | Exp.Lindex (e1, e2) -> 
        let locs = Domain.find_mem_set (eval_lv e1 astate) astate 
          |> Domain.Val.get_array_blk 
          |> ArrayBlk.pow_loc_of_array
        in
        Domain.find_mem_set locs astate
    | Exp.Sizeof (typ, _, _) -> Domain.Val.of_int (sizeof typ) 
(*    | Exp.Exn _ -> 
    | Exp.Closure _ -> *)
    | _ -> raise Not_implemented

  and eval_lv : Exp.t -> Domain.astate -> PowLoc.t
  = fun e astate ->
    match e with 
    | Exp.Var id -> Var.of_id id |> Loc.of_var |> PowLoc.singleton
    | Exp.Lvar pvar -> Var.of_pvar pvar |> Loc.of_var |> PowLoc.singleton
    | Exp.Lindex (e1, e2) -> 
        eval e1 astate |> Domain.Val.get_array_blk |> ArrayBlk.pow_loc_of_array
    | _ -> raise Not_implemented

  and eval_unop : Unop.t -> Exp.t -> Domain.astate -> Domain.Val.astate 
  = fun unop e astate -> 
    let v = eval e astate in
    match unop with
    | Unop.Neg -> Domain.Val.neg v
    | Unop.BNot -> Domain.Val.unknown_bit v
    | Unop.LNot -> Domain.Val.lnot v

  and eval_binop : Binop.t -> Exp.t -> Exp.t -> Domain.astate -> Domain.Val.astate 
  = fun binop e1 e2 astate -> 
    let v1 = eval e1 astate in
    let v2 = eval e2 astate in
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

  let eval_array_alloc : Procdesc.t -> CFG.node -> Typ.t -> Exp.t -> int -> int -> Domain.astate -> Domain.Val.astate
  = fun pdesc node typ size inst_num dimension astate ->
    let allocsite = get_allocsite pdesc node inst_num dimension in
    let offset = Itv.of_int 0 in
    let size = eval size astate |> Domain.Val.get_itv in
    let stride = Itv.of_int 4 in (* TODO *)
    let nullpos = Itv.of_int 0 in (* TODO *)
    ArrayBlk.make allocsite offset size stride nullpos
    |> Domain.Val.of_array_blk

  let handle_unknown_call callee_pname params node astate = 
    match Procname.get_method callee_pname with
      "malloc" -> prerr_endline "print malloc"; astate
    | _ -> astate

  let rec declare_array pdesc node loc typ inst_num dimension astate = 
    match typ with 
      Typ.Tarray (typ, Some len) -> 
(*      prerr_endline "Tarray";
        IntLit.pp F.err_formatter len;
          Loc.pp  F.err_formatter loc;
          Typ.pp_full pe_text F.err_formatter typ;
*)
        let size = Exp.Const (Const.Cint len) in
        let astate = Domain.add_mem loc (eval_array_alloc pdesc node typ size inst_num dimension astate) astate in
        let loc = Loc.of_allocsite (get_allocsite pdesc node inst_num dimension) in
        declare_array pdesc node loc typ inst_num (dimension + 1) astate
    | _ -> astate

  let can_strong_update ploc =
    if PowLoc.cardinal ploc = 1 then 
      let lv = PowLoc.choose ploc in
      Loc.is_var lv
    else false

  let update_mem : PowLoc.t -> Domain.Val.t -> Domain.astate -> Domain.astate 
  = fun ploc v s ->
    if can_strong_update ploc then Domain.strong_update_mem ploc v s
    else Domain.weak_update_mem ploc v s

  let get_formals : Procdesc.t -> (Pvar.t * Typ.t) list
  = fun pdesc ->
    let proc_name = Procdesc.get_proc_name pdesc in
    Procdesc.get_formals pdesc |> IList.map (fun (name, typ) -> (Pvar.mk name proc_name, typ))

  let exec_instr astate { ProcData.pdesc; tenv; extras } node (instr : Sil.instr) = 
    Sil.pp_instr Utils.pe_text F.err_formatter instr;
    prerr_newline ();
    Domain.pp F.err_formatter astate;
    prerr_newline ();
    match instr with
    | Load (id, exp, _, loc) ->
        Domain.add_mem (Loc.of_var (Var.of_id id)) (eval exp astate) astate
    | Store (exp1, _, exp2, loc) ->
        update_mem (eval_lv exp1 astate) (eval exp2 astate) astate
    | Prune (exp, loc, _, _) ->
(*    | Call (_, Const (Cfun callee_pname), params, loc, _) ->
        let callsite = CallSite.make callee_pname loc in
        let callee_globals =
          match Summary.read_summary tenv pdesc callee_pname with
          | Some (Domain.NonBottom trace) ->
              Domain.NonBottom (SiofTrace.with_callsite trace callsite)
          | _ ->
              Domain.Bottom in
        add_params_globals astate loc params
        |> Domain.join callee_globals
        |>
        (* make sure it's not Bottom: we made a function call so this needs initialization *)
        at_least_bottom*)
        astate
    | Call (ret, Const (Cfun callee_pname), params, loc, _) when extras callee_pname = None -> (* unknown function *)
        prerr_endline "UNKNOWN FUNCTION";
        astate
    | Call (Some (id, _), Const (Cfun callee_pname), params, loc, _) ->
        let callee = extras callee_pname in
        (match callee with 
          Some pdesc -> 
            let formals = get_formals pdesc in
            IList.iter (fun (f,typ) -> Pvar.pp pe_text F.err_formatter f) formals
         | _ -> ());
        let call_site = CallSite.make callee_pname loc in
        let callee_state = 
          match Summary.read_summary tenv pdesc callee_pname with
          | Some astate -> astate
          | None -> handle_unknown_call callee_pname params node Domain.initial
        in
        Domain.add_mem (Loc.of_var (Var.of_id id)) (Domain.find_mem (Loc.of_var (Var.of_pvar (Pvar.get_ret_pvar callee_pname))) callee_state) astate
    | Call (_, _, params, loc, _) -> astate
    | Declare_locals (locals, _) -> 
        let astate = IList.fold_left (fun (astate,c) (pvar, typ) ->
            match typ with 
              Typ.Tarray (_, _) ->
                (declare_array pdesc node (Loc.of_var (Var.of_pvar pvar)) typ c 1 astate, c+1)
            | _ -> (astate, c)) (astate, 1) locals 
          |> fst
        in
        IList.fold_left (fun (astate,c) (pvar, typ) -> 
            match typ with
              Typ.Tint _ -> (Domain.add_mem (Loc.of_pvar pvar) (Domain.Val.get_new_sym ()) astate, c+1)
            | _ -> (astate, c) (* TODO *)) (astate, 0) (get_formals pdesc)
        |> fst
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
