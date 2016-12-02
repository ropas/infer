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
end 
