open BasicDom

module F = Format
module L = Logging

(* Set of safety conditions

   It collects all the B.O. safety conditions in the function, in
   terms of symbol. *)
module Conds =
struct
  type cond =
    | Le of Itv.astate * Itv.astate
    | Lt of Itv.astate * Itv.astate
    | Eq of Itv.astate * Itv.astate

  (* TODO: Check the condition list is short.  If it is not, we may
     have to use set instead of list. *)
  type astate = cond list

  let initial : astate = []

  (* TODO: As of now, we do not use logical implications among
     conditions for order. *)
  let (<=) : lhs:astate -> rhs:astate -> bool
  = fun ~lhs ~rhs ->
    List.for_all (fun c -> List.mem c rhs) lhs

  let fold : (cond -> 'a -> 'a) -> astate -> 'a -> 'a
  = fun f l init ->
    List.fold_left (fun acc e -> f e acc) init l

  let join : astate -> astate -> astate
  = fun x y ->
    fold (fun c acc -> if List.mem c acc then acc else c :: acc) y x

  (* TODO: We expect that the growing of conditions is finite by the
     widening of Itv. *)
  let widen : prev:astate -> next:astate -> num_iters:int -> astate
  = fun ~prev ~next ~num_iters:_ ->
    join next prev

  let pp1 : F.formatter -> cond -> unit
  = fun fmt -> function
    | Le (x, y) -> F.fprintf fmt "%a <= %a" Itv.pp x Itv.pp y
    | Lt (x, y) -> F.fprintf fmt "%a < %a" Itv.pp x Itv.pp y
    | Eq (x, y) -> F.fprintf fmt "%a = %a" Itv.pp x Itv.pp y

  let pp : F.formatter -> astate -> unit
  = fun fmt x ->
    F.fprintf fmt "@[";
    (match x with
     | [] -> F.fprintf fmt "true"
     | c :: tl ->
         pp1 fmt c;
         List.iter (fun c -> F.fprintf fmt "@, /\\ %a" pp1 c) tl);
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

  let of_int : int -> astate
  = fun n ->
    (Itv.of_int n, PowLoc.bot, ArrayBlk.bot)
  let of_pow_loc x = (Itv.bot, x, ArrayBlk.bot)
  let of_array_blk : ArrayBlk.astate -> astate
  = fun a -> (Itv.bot, PowLoc.bot, a)
  let get_new_sym : unit -> t 
  = fun () -> (Itv.get_new_sym (), PowLoc.bot, ArrayBlk.bot)
end

module PPMap = 
struct 
  module Ord = struct include Loc let compare = compare let pp_key = pp end
  include PrettyPrintable.MakePPMap(Ord)
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

let get_cond : astate -> Conds.astate
= fun s ->
  snd s

let add_mem : Loc.t -> Val.astate -> astate -> astate
= fun x y s ->
  (get_mem s |> Mem.add x y, get_cond s)

let strong_update_mem : PowLoc.t -> Val.astate -> astate -> astate
= fun ploc v s ->
  (get_mem s |> Mem.strong_update ploc v, get_cond s)

let weak_update_mem : PowLoc.t -> Val.astate -> astate -> astate
= fun ploc v s ->
  (get_mem s |> Mem.weak_update ploc v, get_cond s)

let find_mem : Loc.t -> astate -> Val.astate
= fun x s ->
  Mem.find x (get_mem s)

let find_mem_set : PowLoc.t -> astate -> Val.astate
= fun x s ->
  Mem.find_set x (get_mem s)
