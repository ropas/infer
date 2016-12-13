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
module L = Logging

type t = Procname.t * int

let compare : t -> t -> int
= fun x y -> 
  let c = Procname.compare (fst x) (fst y) in
  if c <> 0 then c else snd x - snd y

let eq : t -> t -> bool
= fun x y -> compare x y = 0

let make : Procname.t -> int -> t 
= fun pname i -> (pname, i)

let pp : F.formatter -> t -> unit
= fun fmt x -> 
  if Config.ropas_debug = 0 then
    F.fprintf fmt "s$%d" (snd x)
  else
    F.fprintf fmt "%s-s$%d" (fst x |> Procname.to_string) (snd x)
