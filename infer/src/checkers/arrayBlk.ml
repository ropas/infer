(* Abstract Array Block *)
open BasicDom

module ArrInfo = 
struct
  type t = {
    offset    : Itv.t;
    size      : Itv.t;
    stride    : Itv.t;
    null_pos  : Itv.t;
(*    structure : PowStruct.t;*)
  }
  type astate = t

  let bot = { offset = Itv.bot; size = Itv.bot; stride = Itv.bot; null_pos = Itv.bot; (* structure = PowStruct.bot *)}
  let initial = bot
  let top = { offset = Itv.top; size = Itv.top; stride = Itv.top; null_pos = Itv.top; (* structure = PowStruct.bot *)}
  let input = { offset = Itv.zero; size = Itv.pos; stride = Itv.one; null_pos = Itv.nat; (* structure = PowStruct.bot *)}
  
  let make (o,s,stride,null(*,structure*)) = 
    { offset = o; size = s; stride = stride; null_pos = null; (* structure = structure *)}
  
  let compare = Pervasives.compare 

  let join a1 a2 = 
    if a1 == a2 then a2 else
    { offset    = Itv.join a1.offset a2.offset;
      size      = Itv.join a1.size a2.size;
      stride    = Itv.join a1.stride a2.stride;
      null_pos  = Itv.join a1.null_pos a2.null_pos;
(*      structure = PowStruct.join a1.structure a2.structure; *)}
  let widen ~prev ~next ~num_iters = 
    if prev == next then next else
    { offset    = Itv.widen ~prev:prev.offset ~next:next.offset ~num_iters;
      size      = Itv.widen ~prev:prev.size ~next:next.size ~num_iters;
      stride    = Itv.widen ~prev:prev.stride ~next:next.stride ~num_iters;
      null_pos  = Itv.widen ~prev:prev.null_pos ~next:next.null_pos ~num_iters;
(*      structure = PowStruct.widen a1.structure a2.structure; *)}

  let eq a1 a2 = 
    if a1 == a2 then true
    else 
      Itv.eq a1.offset a2.offset
      && Itv.eq a1.size a2.size
      && Itv.eq a1.stride a2.stride
      && Itv.eq a1.null_pos a2.null_pos
(*      && PowStruct.eq a1.structure a2.structure*)

  let (<=) ~lhs ~rhs = 
    if lhs == rhs then true
    else 
      Itv.le ~lhs:lhs.offset ~rhs:rhs.offset
      && Itv.le ~lhs:lhs.size ~rhs:rhs.size
      && Itv.le ~lhs:lhs.stride ~rhs:rhs.stride
      && Itv.le ~lhs:lhs.null_pos ~rhs:rhs.null_pos
(*      && PowStruct.le a1.structure a2.structure*)

  let weak_plus_size arr i = { arr with size = Itv.join arr.size (Itv.plus i arr.size) }
  let plus_offset arr i = { arr with offset = Itv.plus arr.offset i }
  let minus_offset arr i = { arr with offset = Itv.minus arr.offset i }
  let set_null_pos arr i = { arr with null_pos = i }
  let plus_null_pos arr i = { arr with null_pos = Itv.plus arr.null_pos i }

  let diff arr1 arr2 =
    let i1 = Itv.mult arr1.offset arr1.stride in
    let i2 = Itv.mult arr2.offset arr2.stride in
    Itv.minus i1 i2

  let subst arr subst_map = { arr with offset = Itv.subst arr.offset subst_map; size = Itv.subst arr.size subst_map; }
  let pp fmt arr = 
    Format.fprintf fmt "offset : %a, size : %a, stride : %a" Itv.pp arr.offset Itv.pp arr.size Itv.pp arr.stride
end

module PPMap = PrettyPrintable.MakePPMap 
  (struct
     include Allocsite
     let pp_key f k = pp f k
   end)
include AbstractDomain.Map(PPMap)(ArrInfo)

let bot = initial
let make : Allocsite.t -> Itv.t -> Itv.t -> Itv.t -> Itv.t -> astate
= fun a o sz st np ->
  add a (ArrInfo.make (o, sz, st, np(*, PowStruct.bot*))) bot

let offsetof : astate -> Itv.t
= fun a ->
  fold (fun _ arr -> Itv.join arr.ArrInfo.offset) a Itv.bot

let sizeof : astate -> Itv.t
= fun a ->
  fold (fun _ arr -> Itv.join arr.ArrInfo.size) a Itv.bot

let nullof : astate -> Itv.t
= fun a ->
  fold (fun _ arr -> Itv.join arr.ArrInfo.null_pos) a Itv.bot

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

let set_null_pos : astate -> Itv.t -> astate
= fun arr i ->
  map (fun a -> ArrInfo.set_null_pos a i) arr

let plus_null_pos : astate -> Itv.t -> astate
= fun arr i ->
  map (fun a -> ArrInfo.plus_null_pos a i) arr

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
