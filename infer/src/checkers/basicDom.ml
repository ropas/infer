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

module F = Format

module Allocsite = 
struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let make x = x
end

module Loc = 
struct
  type t = Var of Var.t | Allocsite of Allocsite.t | Field of t * Ident.fieldname

  let rec pp fmt = function 
    | Var v -> 
        Var.pp F.str_formatter v;
        let s = F.flush_str_formatter () in
        if s.[0] = '&' then
          F.fprintf fmt "%s" (String.sub s 1 (String.length s - 1))
        else F.fprintf fmt "%s" s
    | Allocsite a -> Allocsite.pp fmt a
    | Field (l, f) -> F.fprintf fmt "%a.%a" pp l Ident.pp_fieldname f
  let is_var = function Var _ -> true | _ -> false
  let of_var v = Var v
  let of_allocsite a = Allocsite a
  let of_pvar pvar = Var (Var.of_pvar pvar)
  let of_id id = Var (Var.of_id id)
  let append_field l f = Field (l, f)
end

module PowLoc = 
struct 
  include AbstractDomain.FiniteSet
    (struct 
      include Set.Make (struct type t = Loc.t let compare = compare end)
      let pp_element fmt e = Loc.pp fmt e
      let pp fmt s =
        Format.fprintf fmt "{";
        iter (fun e -> Format.fprintf fmt "%a," pp_element e) s;
        Format.fprintf fmt "}"
     end)

  let bot = initial

  let of_pvar pvar = singleton (Loc.of_pvar pvar)
  let of_id id = singleton (Loc.of_id id)
  let append_field ploc fn = fold (fun l -> add (Loc.append_field l fn)) ploc empty
end
