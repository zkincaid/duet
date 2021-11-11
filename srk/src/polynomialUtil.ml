open Polynomial

module PolyVectorContext = struct

  exception Not_in_context

  module MonomialMap = BatMap.Make(Monomial)

  type t =
    {
      index_to_monomial: Monomial.t SrkUtil.Int.Map.t
    ; monomial_to_index : int MonomialMap.t
    ; ordering : Monomial.t -> Monomial.t -> [`Eq | `Lt | `Gt ]
    ; size : int
    }

  (*
  let monomials_ordered_by
      ?increasing:(increasing = true)
      (ord: Monomial.t -> Monomial.t -> [`Eq | `Lt | `Gt ])
      (polys : M.t list) =
    let monos_in p = BatEnum.fold (fun l (_scalar, mono) -> mono :: l) [] (M.enum p) in
    let monos = List.fold_left
        (fun l p -> List.append (monos_in p) l) [] polys in
    let sorted = List.sort_uniq (fun m1 m2 ->
        match ord m1 m2 with
        | `Eq -> 0
        | `Lt -> -1
        | `Gt -> 1)
        monos in
    if increasing then sorted else List.rev sorted
  *)

  let context ?increasing:(increasing=true)
      (ord: Monomial.t -> Monomial.t -> [`Eq | `Lt | `Gt ])
      monos =
    (* let l = monomials_ordered_by ~increasing:increasing ord polys in *)
    let l = List.sort_uniq (fun m1 m2 ->
        match ord m1 m2 with
        | `Eq -> 0
        | `Lt -> -1
        | `Gt -> 1)
        monos in
    let l = if increasing then l else List.rev l in
    let emp = { index_to_monomial = SrkUtil.Int.Map.empty
              ; monomial_to_index = MonomialMap.empty
              ; ordering = ord
              ; size = 0
              } in
    BatList.fold_lefti
      (fun ctxt idx mono ->
         let i2m_map = SrkUtil.Int.Map.add idx mono ctxt.index_to_monomial in
         let m2i_map = MonomialMap.add mono idx ctxt.monomial_to_index in
         { index_to_monomial = i2m_map
         ; monomial_to_index = m2i_map
         ; ordering = ord
         ; size = ctxt.size + 1
         })
      emp l

  let monomial_of idx ctxt =
    try
      SrkUtil.Int.Map.find idx ctxt.index_to_monomial
    with Not_found -> raise Not_in_context

  let dim_of mono ctxt =
    try
      MonomialMap.find mono ctxt.monomial_to_index
    with Not_found -> raise Not_in_context

  let num_dimensions ctxt = ctxt.size

  let max_dimension ctxt = ctxt.size

  let fold_over_dimensions f ctxt base =
    SrkUtil.Int.Map.fold f ctxt.index_to_monomial base

  let string_of_idx_mono dim_pp idx mono =
    let () = Format.fprintf Format.str_formatter
        "(%a, %a)"
        Format.pp_print_int idx
        (Monomial.pp dim_pp) mono in
    Format.flush_str_formatter ()

  let string_of_mono_idx dim_pp mono idx =
    let () = Format.fprintf Format.str_formatter
        "(%a, %a)"
        (Monomial.pp dim_pp) mono
        Format.pp_print_int idx in
    Format.flush_str_formatter ()

  let pp_i2m_map dim_pp fmt (map : Monomial.t SrkUtil.Int.Map.t) =
    let l = SrkUtil.Int.Map.fold (fun idx mono l -> (idx, mono) :: l) map [] in
    let l = List.sort (fun (idx1, _mono1) (idx2, _mono2) -> idx1 - idx2) l in
    let s = String.concat ", " (List.map (fun (idx, mono) -> string_of_idx_mono dim_pp idx mono) l) in
    Format.pp_print_string fmt s

  let pp_m2i_map dim_pp fmt (map : int MonomialMap.t) =
    let l = MonomialMap.fold (fun mono idx l -> (mono, idx) :: l) map [] in
    let l = List.sort (fun (_mono1, idx1) (_mono2, idx2) -> idx1 - idx2) l in
    let s = String.concat ", " (List.map (fun (mono, idx) -> string_of_mono_idx dim_pp mono idx) l) in
    Format.pp_print_string fmt s

  let pp dim_pp fmt conv_ctxt =
    let () = Format.fprintf Format.str_formatter
        "[%a | %a]"
        (pp_i2m_map dim_pp) conv_ctxt.index_to_monomial
        (pp_m2i_map dim_pp) conv_ctxt.monomial_to_index in
    let s = Format.flush_str_formatter () in
    Format.pp_print_string fmt s

end

module PolyVectorConversion = struct

  open PolyVectorContext
  open Linear

  let rational_poly_to_vector ctxt p =
    fold_over_dimensions
      (fun dim mono v ->
         QQVector.add_term (QQXs.coeff mono p) dim v)
      ctxt
      QQVector.zero

  let rational_poly_to_scalars ctxt p =
    let l = fold_over_dimensions
        (fun _dim mono l ->
           (QQXs.coeff mono p) :: l)
        ctxt
        []
    in
    List.rev l

  let scalars_to_rational_poly ctxt l =
    BatList.fold_lefti
      (fun p dim scalar ->
         QQXs.add_term scalar (monomial_of dim ctxt) p)
      QQXs.zero
      l

end
