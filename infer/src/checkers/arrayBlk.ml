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
(*
  let meet a1 a2 = 
    if a1 == a2 then a2 else
    { offset    = Itv.meet a1.offset a2.offset;
      size      = Itv.meet a1.size a2.size;
      stride    = Itv.meet a1.stride a2.stride;
      null_pos  = Itv.meet a1.null_pos a2.null_pos;
(*      structure = PowStruct.meet a1.structure a2.structure; *)}
*)
  let widen ~prev ~next ~num_iters = 
    if prev == next then next else
    { offset    = Itv.widen ~prev:prev.offset ~next:next.offset ~num_iters;
      size      = Itv.widen ~prev:prev.size ~next:next.size ~num_iters;
      stride    = Itv.widen ~prev:prev.stride ~next:next.stride ~num_iters;
      null_pos  = Itv.widen ~prev:prev.null_pos ~next:next.null_pos ~num_iters;
(*      structure = PowStruct.widen a1.structure a2.structure; *)}
(*
  let narrow a1 a2 = 
    if a1 == a2 then a2 else
    { offset    = Itv.narrow a1.offset a2.offset;
      size      = Itv.narrow a1.size a2.size;
      stride    = Itv.narrow a1.stride a2.stride;
      null_pos  = Itv.narrow a1.null_pos a2.null_pos;
      structure = PowStruct.narrow a1.structure a2.structure; }
*)  
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
(*
  let resize orig_st new_st x = Itv.divide (Itv.times x orig_st) new_st
  let cast typ arr =
    match typ with
      Cil.TPtr ((Cil.TComp (comp, _) as t'), _) -> 
        let new_stride = try CilHelper.byteSizeOf t' |> Itv.of_int with _ -> Itv.top in
        { offset = resize arr.stride new_stride arr.offset;
          size = resize arr.stride new_stride arr.size;
          null_pos = resize arr.stride new_stride arr.null_pos;
          stride = new_stride;
          structure = PowStruct.add comp.Cil.cname arr.structure }
    | Cil.TPtr (t', _) | Cil.TArray (t', _, _) ->
        let new_stride = try CilHelper.byteSizeOf t' |> Itv.of_int with _ -> Itv.top in
        { arr with 
            offset = resize arr.stride new_stride arr.offset;
            size = resize arr.stride new_stride arr.size;
            null_pos = resize arr.stride new_stride arr.null_pos;
            stride = new_stride; }
    | _ -> arr
*)
  let weak_plus_size arr i = { arr with size = Itv.join arr.size (Itv.plus i arr.size) }
  let plus_offset arr i = { arr with offset = Itv.plus arr.offset i }
  let minus_offset arr i = { arr with offset = Itv.minus arr.offset i }
  let set_null_pos arr i = { arr with null_pos = i }
  let plus_null_pos arr i = { arr with null_pos = Itv.plus arr.null_pos i }

  let diff arr1 arr2 =
    let i1 = Itv.mult arr1.offset arr1.stride in
    let i2 = Itv.mult arr2.offset arr2.stride in
    Itv.minus i1 i2

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

(*
let cast_array : Cil.typ -> t -> t 
= fun typ a ->
  mapi (fun allocsite -> if Allocsite.is_cmd_arg allocsite then id else ArrInfo.cast typ) a

let allocsites_of_array a =
  foldi (fun k _ -> BatSet.add k) a BatSet.empty 

let struct_of_array a = 
  foldi (fun k v -> 
      if PowStruct.bot <> v.ArrInfo.structure then PowLoc.add (Loc.of_allocsite k) 
      else id) a PowLoc.bot

let append_field : t -> Cil.fieldinfo -> PowLoc.t 
= fun s f ->
  foldi (fun a info ->
      if PowStruct.mem f.Cil.fcomp.Cil.cname info.ArrInfo.structure then
        let loc = Loc.of_allocsite a in
        PowLoc.add (Loc.append_field loc f.Cil.fname)
      else id) s PowLoc.bot
*)
(*
let to_string : t -> string = fun x ->
  if is_empty x then "bot" else
  foldi (fun a b s ->
      let str = A.to_string a ^ " -> " ^ B.to_string b in
      link_by_sep "\n\t" str s) x ""
*)
