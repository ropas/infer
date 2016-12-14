module F = Format

module FSTaint =
struct
  type t =
    | PgmPoint of Location.t
    | TntSymb of Symbol.t

  let compare x y =
    match x, y with
    | PgmPoint x', PgmPoint y' -> Location.compare x' y'
    | PgmPoint _, _ -> -1
    | _, PgmPoint _ -> 1
    | TntSymb x', TntSymb y' -> Symbol.compare x' y'

  let pp_element fmt x =
    match x with
    | PgmPoint x' ->
        F.fprintf fmt "File: %a, line: %d, col: %d"
          DB.source_file_pp x'.file x'.line x'.col;
    | TntSymb x' -> Symbol.pp fmt x'

  let is_pgm_point = function
    | PgmPoint _ -> true
    | _ -> false

  let is_symbol = function
    | TntSymb _ -> true
    | _ -> false

  let make_sym pname i = (TntSymb (Symbol.make pname i), i + 1)

  let get_symbols = function
    | TntSymb s -> Some s
    | _ -> None
end

module FSTaintPPSet = PrettyPrintable.MakePPSet (FSTaint)

module SubstMap =
struct
  include Map.Make (Symbol)

  let of_pairs pairs =
    let add acc (k, v) =
      match k with
      | FSTaint.TntSymb s -> add s v acc
      | _ -> assert false
    in
    IList.fold_left add empty pairs
end

include AbstractDomain.FiniteSet (FSTaintPPSet)

let is_unsafe cs = exists FSTaint.is_pgm_point cs

let has_symbol cs = exists FSTaint.is_symbol cs

let subst cs subst_map =
  let union_substed c acc =
    match c with
    | FSTaint.TntSymb s ->
        (try union acc (SubstMap.find s subst_map) with
         | Not_found -> acc)
    | _ -> add c acc
  in
  fold union_substed cs initial

let bot = empty

let make_sym pname i =
  let (v, i) = FSTaint.make_sym pname i in
  (singleton v, i)

let get_symbols cs =
  let add_symbols c acc =
    match FSTaint.get_symbols c with
    | Some s -> s :: acc
    | None -> acc
  in
  fold add_symbols cs []

let add_taint loc cs = add (FSTaint.PgmPoint loc) cs
