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

(* Abstract Array Block *)

open BasicDom

module ArrInfo = 
struct
  type t = {
    offset    : Itv.t;
    size      : Itv.t;
    stride    : Itv.t;
  }
  type astate = t

  let bot = { offset = Itv.bot; size = Itv.bot; stride = Itv.bot; }
  let initial = bot
  let top = { offset = Itv.top; size = Itv.top; stride = Itv.top; }
  let input = { offset = Itv.zero; size = Itv.pos; stride = Itv.one; }
  
  let make (o,s,stride) = 
    { offset = o; size = s; stride = stride; }
  
  let compare a1 a2 =
    let i = Itv.compare a1.offset a2.offset in
    if i <> 0 then i else
      let i = Itv.compare a1.size a2.size in
      if i <> 0 then i else
        Itv.compare a1.stride a2.stride

  let join a1 a2 = 
    if a1 == a2 then a2 else
    { offset    = Itv.join a1.offset a2.offset;
      size      = Itv.join a1.size a2.size;
      stride    = Itv.join a1.stride a2.stride; }
  let widen ~prev ~next ~num_iters = 
    if prev == next then next else
    { offset    = Itv.widen ~prev:prev.offset ~next:next.offset ~num_iters;
      size      = Itv.widen ~prev:prev.size ~next:next.size ~num_iters;
      stride    = Itv.widen ~prev:prev.stride ~next:next.stride ~num_iters; }

  let eq a1 a2 = 
    if a1 == a2 then true
    else 
      Itv.eq a1.offset a2.offset
      && Itv.eq a1.size a2.size
      && Itv.eq a1.stride a2.stride

  let (<=) ~lhs ~rhs = 
    if lhs == rhs then true
    else 
      Itv.le ~lhs:lhs.offset ~rhs:rhs.offset
      && Itv.le ~lhs:lhs.size ~rhs:rhs.size
      && Itv.le ~lhs:lhs.stride ~rhs:rhs.stride

  let weak_plus_size arr i = { arr with size = Itv.join arr.size (Itv.plus i arr.size) }
  let plus_offset arr i = { arr with offset = Itv.plus arr.offset i }
  let minus_offset arr i = { arr with offset = Itv.minus arr.offset i }

  let diff arr1 arr2 =
    let i1 = Itv.mult arr1.offset arr1.stride in
    let i2 = Itv.mult arr2.offset arr2.stride in
    Itv.minus i1 i2

  let subst arr subst_map = { arr with offset = Itv.subst arr.offset subst_map; size = Itv.subst arr.size subst_map; }
  let pp fmt arr = 
    if Config.debug_mode then 
      Format.fprintf fmt "offset : %a, size : %a, stride : %a" Itv.pp arr.offset Itv.pp arr.size Itv.pp arr.stride
    else 
      Format.fprintf fmt "offset : %a, size : %a" Itv.pp arr.offset Itv.pp arr.size

  let get_symbols arr =
    let s1 = Itv.get_symbols arr.offset in
    let s2 = Itv.get_symbols arr.size in
    let s3 = Itv.get_symbols arr.stride in
    IList.flatten [s1; s2; s3]
end

module PPMap = PrettyPrintable.MakePPMap 
  (struct
     include Allocsite
     let pp_key f k = pp f k
   end)
include AbstractDomain.Map(PPMap)(ArrInfo)

let bot = initial
let make : Allocsite.t -> Itv.t -> Itv.t -> Itv.t -> astate
= fun a o sz st ->
  add a (ArrInfo.make (o, sz, st)) bot

let offsetof : astate -> Itv.t
= fun a ->
  fold (fun _ arr -> Itv.join arr.ArrInfo.offset) a Itv.bot

let sizeof : astate -> Itv.t
= fun a ->
  fold (fun _ arr -> Itv.join arr.ArrInfo.size) a Itv.bot

let extern allocsite = 
  add allocsite ArrInfo.top empty 

let input allocsite = 
  add allocsite ArrInfo.input empty 

let weak_plus_size : astate -> Itv.t -> astate
= fun arr i -> 
  map (fun a -> ArrInfo.weak_plus_size a i) arr

let plus_offset : astate -> Itv.t -> astate
= fun arr i ->
  map (fun a -> ArrInfo.plus_offset a i) arr

let minus_offset : astate -> Itv.t -> astate
= fun arr i ->
  map (fun a -> ArrInfo.minus_offset a i) arr

let diff : astate -> astate -> Itv.t
= fun arr1 arr2 ->
  let diff_join k a2 acc =
    match find k arr1 with
    | a1 -> Itv.join acc (ArrInfo.diff a1 a2)
    | exception Not_found -> acc
  in
  fold diff_join arr2 Itv.bot

let get_pow_loc : astate -> PowLoc.t = fun array ->
  let pow_loc_of_allocsite k _ acc = PowLoc.add (Loc.of_allocsite k) acc in
  fold pow_loc_of_allocsite array PowLoc.bot

let subst a subst_map = map (fun info -> ArrInfo.subst info subst_map) a

let get_symbols a =
  IList.flatten (IList.map (fun (_, ai) -> ArrInfo.get_symbols ai) (bindings a))
