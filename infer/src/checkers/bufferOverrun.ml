open! Utils

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
  type extras = ProcData.no_extras

  exception Not_implemented 

  let eval_const : Const.t -> Domain.Val.astate = function 
    | Const.Cint intlit -> 
        Domain.Val.of_int (IntLit.to_int intlit)
    | _ -> Domain.Val.of_int (-999)

 let rec eval : Exp.t -> Domain.astate -> Domain.Val.astate
  = fun exp astate ->
    match exp with
      (* Pure variable: it is not an lvalue *)
    | Exp.Var id -> Domain.find_mem (Var.of_id id) astate
    | Exp.UnOp (uop, e, _) -> eval_unop uop e astate
    | Exp.BinOp (bop, e1, e2) -> eval_binop bop e1 e2 astate
    | Exp.Const c -> eval_const c 
    (* Type cast *)
(*    | Cast Typ.t t *)
    (* The address of a program variable *)
    | Exp.Lvar pvar -> Domain.find_mem (Var.of_pvar pvar) astate
    (* A field offset, the type is the surrounding struct type *)
(*    | Lfield t Ident.fieldname Typ.t *)
(*    | Lindex (e1, e2) -> 
        Domain.find_mem (*)
    (* A sizeof expression. [Sizeof (Tarray elt (Some static_length)) (Some dynamic_length)]
        represents the size of an array value consisting of [dynamic_length] elements of type [elt].
        The [dynamic_length], tracked by symbolic execution, may differ from the [static_length]
        obtained from the type definition, e.g. when an array is over-allocated.  For struct types,
        the [dynamic_length] is that of the final extensible array, if any. *)
(*    | Sizeof Typ.t dynamic_length Subtype.t;*)
(*    | Exp.Exn _ -> 
    | Exp.Closure _ -> *)
    | _ -> raise Not_implemented

  and eval_lv : Exp.t -> Domain.astate -> Var.t
  = fun e astate ->
    match e with 
    | Exp.Var id -> Var.of_id id
    | Exp.Lvar pvar -> Var.of_pvar pvar
    | _ -> raise Not_implemented
  and eval_unop : Unop.t -> Exp.t -> Domain.astate -> Domain.Val.astate 
  = fun unop e astate -> 
    raise Not_implemented
  and eval_binop : Binop.t -> Exp.t -> Exp.t -> Domain.astate -> Domain.Val.astate 
  = fun binop e1 e2 astate -> 
    raise Not_implemented

   
  let handle_unknown_call callee_pname params node astate = 
    match Procname.get_method callee_pname with
      "malloc" -> prerr_endline "print malloc"; astate
    | _ -> astate

  let exec_instr astate { ProcData.pdesc; tenv } node (instr : Sil.instr) = 
    Sil.pp_instr Utils.pe_text F.err_formatter instr;
    prerr_newline ();
    Domain.pp F.err_formatter astate;
    prerr_newline ();
    match instr with
    | Load (id, exp, _, loc) ->
        Domain.add_mem (Var.of_id id) (eval exp astate) astate
    | Store (exp1, _, exp2, loc) ->
        Domain.add_mem (eval_lv exp1 astate) (eval exp2 astate) astate
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
    | Call (Some (id, _), Const (Cfun callee_pname), params, loc, _) ->
        let call_site = CallSite.make callee_pname loc in
        let callee_state = 
          match Summary.read_summary tenv pdesc callee_pname with
          | Some astate -> astate
          | None -> handle_unknown_call callee_pname params node Domain.initial
        in
        Domain.add_mem (Var.of_id id) (Domain.find_mem (Var.of_pvar (Pvar.get_ret_pvar callee_pname)) callee_state) astate
    | Call (_, _, params, loc, _) -> astate
    | Declare_locals _ | Remove_temps _ | Abstract _ | Nullify _ ->
        astate
end

module Analyzer =
  AbstractInterpreter.Make
    (ProcCfg.Normal)
    (Scheduler.ReversePostorder)
    (TransferFunctions)

module Interprocedural = Analyzer.Interprocedural (Summary)

let checker ({ Callbacks.tenv; proc_desc } as callback) =
  let post = Interprocedural.checker callback ProcData.empty_extras in
  ()
