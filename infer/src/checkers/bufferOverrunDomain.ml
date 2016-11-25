open BasicDom

module F = Format
module L = Logging

(* Set of safety conditions

   It collects all the B.O. safety conditions in the function, in
   terms of symbol. *)
module Conds =
struct
  type rel_t =
    | Le of Itv.astate * Itv.astate
    | Lt of Itv.astate * Itv.astate
    | Eq of Itv.astate * Itv.astate

  type cond = {rel: rel_t; loc: Location.t}

  (* TODO: Check the condition list is short.  If it is not, we may
     have to use set instead of list. *)
  type astate = cond list

  type t = astate

  let initial : astate = []

  let get_location : cond -> Location.t
  = fun c -> c.loc 

  (* TODO: Duplication checks may be required. *)
  let add x conds = x :: conds

  let add_bo_safety ~idx ~size conds loc =
    {rel = Le (Itv.zero, idx); loc}
    :: {rel = Lt (idx, size); loc}
    :: conds

  (* TODO: As of now, we do not use logical implications among
     conditions for order. *)
  let (<=) : lhs:astate -> rhs:astate -> bool
  = fun ~lhs ~rhs ->
    List.for_all (fun c -> List.mem c rhs) lhs

  let subst : cond -> Itv.Bound.t Itv.SubstMap.t -> cond 
  = fun cond map ->
    let r =
      match cond.rel with
      | Le (l,r) -> Le (Itv.subst l map, Itv.subst r map)
      | Lt (l,r) -> Lt (Itv.subst l map, Itv.subst r map)
      | Eq (l,r) -> Eq (Itv.subst l map, Itv.subst r map)
    in
    {cond with rel = r}

  (* TODO: generalize *)
  let string_of_cond cond =
    match cond.rel with
    | Le (_, r) -> "Offset : " ^ Itv.to_string r
    | Lt (l, r) -> "Offset : " ^ Itv.to_string l ^ " Size : " ^ Itv.to_string r
    | _ -> ""

  let check : cond -> Itv.astate
  = fun cond ->
    match cond.rel with
    | Le (l,r) -> Itv.le_sem l r
    | Lt (l,r) -> Itv.lt_sem l r
    | Eq (l,r) -> Itv.eq_sem l r

  let fold : (cond -> 'a -> 'a) -> astate -> 'a -> 'a
  = fun f l init ->
    List.fold_left (fun acc e -> f e acc) init l

  let iter : (cond -> unit) -> astate -> unit
  = fun f l ->
    List.iter f l

  let join : astate -> astate -> astate
  = fun x y ->
    fold (fun c acc -> if List.mem c acc then acc else c :: acc) y x

  (* TODO: We expect that the growing of conditions is finite by the
     widening of Itv. *)
  let widen : prev:astate -> next:astate -> num_iters:int -> astate
  = fun ~prev ~next ~num_iters:_ ->
    join next prev

  let pp1 : F.formatter -> cond -> unit
  = fun fmt cond ->
    (match cond.rel with
     | Le (x, y) -> F.fprintf fmt "%a <= %a" Itv.pp x Itv.pp y
     | Lt (x, y) -> F.fprintf fmt "%a < %a" Itv.pp x Itv.pp y
     | Eq (x, y) -> F.fprintf fmt "%a = %a" Itv.pp x Itv.pp y);
    F.fprintf fmt " at %a" Location.pp cond.loc

  let pp : F.formatter -> astate -> unit
  = fun fmt x ->
    F.fprintf fmt "@[";
    (match x with
     | [] -> F.fprintf fmt "true"
     | c :: tl ->
         pp1 fmt c;
         List.iter (fun c -> F.fprintf fmt " @,/\\ %a" pp1 c) tl);
    F.fprintf fmt "@]"
end

module Val =
struct
  include AbstractDomain.Pair3(Itv)(PowLoc)(ArrayBlk)

  type t = astate

  let bot = initial

  let get_itv (x,_,_) = x
  let get_pow_loc (_,x,_) = x
  let get_array_blk (_,_,x) = x

  let top_itv = (Itv.top, PowLoc.bot, ArrayBlk.bot)

  let of_int : int -> astate
  = fun n ->
    (Itv.of_int n, PowLoc.bot, ArrayBlk.bot)

  let of_pow_loc : PowLoc.t -> astate
  = fun x ->
    (Itv.bot, x, ArrayBlk.bot)

  let of_array_blk : ArrayBlk.astate -> astate
  = fun a ->
    (Itv.bot, PowLoc.bot, a)

  let get_new_sym : unit -> t 
  = fun () -> (Itv.get_new_sym (), PowLoc.bot, ArrayBlk.bot)

  let unknown_bit : astate -> astate
  = fun (_, x, a) ->
    (Itv.top, x, a)

  let neg : astate -> astate
  = fun (n, x, a) ->
    (Itv.neg n, x, a)

  let lnot : astate -> astate
  = fun (n, x, a) ->
    (Itv.lnot n, x, a)

  let plus : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.plus n1 n2, x1, a1)

  let minus : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.minus n1 n2, x1, a1)

  let mult : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.mult n1 n2, x1, a1)

  let div : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.div n1 n2, x1, a1)

  let mod_sem : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.mod_sem n1 n2, x1, a1)

  let shiftlt : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.shiftlt n1 n2, x1, a1)

  let shiftrt : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.shiftrt n1 n2, x1, a1)

  let lt_sem : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.lt_sem n1 n2, x1, a1)

  let gt_sem : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.gt_sem n1 n2, x1, a1)

  let le_sem : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.le_sem n1 n2, x1, a1)

  let ge_sem : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.ge_sem n1 n2, x1, a1)

  let eq_sem : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.eq_sem n1 n2, x1, a1)

  let ne_sem : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.ne_sem n1 n2, x1, a1)

  let land_sem : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.land_sem n1 n2, x1, a1)

  let lor_sem : astate -> astate -> astate
  = fun (n1, x1, a1) (n2, _, _) ->
    (Itv.lor_sem n1 n2, x1, a1)
end

module PPMap = 
struct 
  module Ord = struct include Loc let compare = compare let pp_key = pp end

  include PrettyPrintable.MakePPMap(Ord)

  (* TODO: Revise format not to use "\n". *)
  let pp ~pp_value fmt m =
    let pp_item fmt (k, v) = F.fprintf fmt "%a -> %a\n" Ord.pp_key k pp_value v in
    PrettyPrintable.pp_collection ~pp_item fmt (bindings m)
end

module Mem = 
struct
  include AbstractDomain.Map(PPMap)(Val)
  let find l m = try find l m with Not_found -> Val.bot

  let find_set : PowLoc.t -> astate -> Val.astate
  = fun locs mem -> 
    let find_join loc acc = Val.join acc (find loc mem) in
    PowLoc.fold find_join locs Val.bot

  let strong_update : PowLoc.t -> Val.astate -> astate -> astate
  = fun locs v mem ->
    PowLoc.fold (fun x -> add x v) locs mem

  let weak_update : PowLoc.t -> Val.astate -> astate -> astate
  = fun locs v mem ->
    PowLoc.fold (fun x -> add x (Val.join v (find x mem))) locs mem
end

include AbstractDomain.Pair(Mem)(Conds)

let get_mem : astate -> Mem.astate
= fun s ->
  fst s

let get_conds : astate -> Conds.astate
= fun s ->
  snd s
