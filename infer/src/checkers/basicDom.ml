module Allocsite = 
struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let make x = x
end

module Loc = 
struct
  type t = Var of Var.t | Allocsite of Allocsite.t
  let pp fmt = function 
    | Var v -> Var.pp fmt v
    | Allocsite a -> Allocsite.pp fmt a
  let of_var v = Var v
  let of_allocsite a = Allocsite a
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
end
