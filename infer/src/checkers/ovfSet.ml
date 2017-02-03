module F = Format

module Ovf =
struct
  type t =
    | IfTainted of TaintSet.Taint.t
    | OvfSymb of Symbol.t 

  let compare x y =
    (* IfTainted < OvfSymb *)
    match x, y with
    | IfTainted t1, IfTainted t2 -> TaintSet.Taint.compare t1 t2
    | OvfSymb s1, OvfSymb s2 -> Symbol.compare s1 s2
    | IfTainted _, OvfSymb _ -> -1
    | OvfSymb _, IfTainted _ -> 1

  let pp_element fmt x =
    match x with
    | IfTainted t -> TaintSet.Taint.pp_element fmt t
    | OvfSymb x' -> Symbol.pp fmt x'

  let is_overflowed = function
    | IfTainted t -> TaintSet.Taint.is_pgm_point t
    | OvfSymb _ -> false

  let is_symbol = function
    | IfTainted t -> TaintSet.Taint.is_symbol t
    | OvfSymb _ -> true

  let make_sym pname i = (OvfSymb (Symbol.make pname i), i + 1)

  let get_symbols = function
    | IfTainted t -> TaintSet.Taint.get_symbols t
    | OvfSymb s -> Some s
end

module OvfPPSet = PrettyPrintable.MakePPSet (Ovf)

module SubstMap =
struct
  include Map.Make (Symbol)

  let of_pairs pairs =
    let add acc (k, v) =
      match k with
      | Ovf.OvfSymb s -> add s v acc
      | _ -> assert false
    in
    IList.fold_left add empty pairs
end

include AbstractDomain.FiniteSet (OvfPPSet)

let bot = empty

let is_unsafe x = exists Ovf.is_overflowed x

let has_symbol x = exists Ovf.is_symbol x

let subst x ovf_subst taint_subst =
  let union_substed elem acc =
    match elem with
    | Ovf.OvfSymb s ->
      (try 
        let ovf_set = SubstMap.find s ovf_subst in
        union acc ovf_set with
      | Not_found -> add elem acc)
    | Ovf.IfTainted (TaintSet.Taint.TntSymb s) -> 
      (try 
        let taint_set = TaintSet.SubstMap.find s taint_subst in
        TaintSet.fold (fun t acc ->
          add (Ovf.IfTainted t) acc
        ) taint_set acc 
      with Not_found -> add elem acc)
    | Ovf.IfTainted (TaintSet.Taint.PgmPoint _) -> add elem acc
  in
  fold union_substed x initial

let make_sym pname i =
  let (ovf, i) = Ovf.make_sym pname i in
  (singleton ovf, i)

let get_symbols x =
  let add_symbols elem acc =
    match Ovf.get_symbols elem with
    | Some s -> s :: acc
    | None -> acc
  in
  fold add_symbols x []
