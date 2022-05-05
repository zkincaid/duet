open Polynomial
open BatPervasives

module V = Linear.QQVector

module PrettyPrint = struct

  let pp_ascii_dim formatter i =
    if i <> Linear.const_dim then
      Format.pp_print_string formatter (Char.escaped (Char.chr i))
    else
      Format.pp_print_string formatter "1"

  let pp_numeric_dim base formatter i =
    Format.fprintf formatter "%s_{%d}" base i

  let pp_list pp_elt fmt =
    Format.fprintf fmt
      (* "@[<v 0>%a@]" *)
      "%a"
      (Format.pp_print_list
         ~pp_sep:(fun fmt _unit -> Format.fprintf fmt "@;")
         pp_elt)

  let pp_qq_matrix = pp_list (SrkUtil.pp_print_list QQ.pp)

  let pp_zz_matrix = pp_list (SrkUtil.pp_print_list ZZ.pp)

  let pp_poly_list pp_dim = pp_list (QQXs.pp pp_dim)

end

module PolyVectorContext = struct

  exception Not_in_context

  module MonomialMap = BatMap.Make(Monomial)

  type t =
    {
      dim_to_mono: Monomial.t SrkUtil.Int.Map.t
    ; mono_to_dim : int MonomialMap.t
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

  let get_mono_map ctx = ctx.mono_to_dim

  let context ?increasing:(increasing=true)
      ?fix_const_dim:(fix_const_dim=true)
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
    let emp = { dim_to_mono = SrkUtil.Int.Map.empty
              ; mono_to_dim = MonomialMap.empty
              ; ordering = ord
              ; size = 0
              } in
    BatList.fold_lefti
      (fun ctxt idx mono ->
        let idx =
          if fix_const_dim && Monomial.equal mono Monomial.one then
            Linear.const_dim
          else idx
        in
         let i2m_map = SrkUtil.Int.Map.add idx mono ctxt.dim_to_mono in
         let m2i_map = MonomialMap.add mono idx ctxt.mono_to_dim in
         { dim_to_mono = i2m_map
         ; mono_to_dim = m2i_map
         ; ordering = ord
         ; size = ctxt.size + 1
         })
      emp l

  let mk_context ?increasing:(increasing=true)
      ?fix_const_dim:(fix_const_dim=true)
      (ord: Monomial.t -> Monomial.t -> [`Eq | `Lt | `Gt ])
      polys =
    let monos = BatList.concat_map (fun poly ->
        (BatList.of_enum (QQXs.enum poly) |>
        BatList.map (fun (_, mono) -> mono)))
       polys in
    context ~increasing ~fix_const_dim ord monos


  let monomial_of dim ctxt =
    try
      SrkUtil.Int.Map.find dim ctxt.dim_to_mono
    with Not_found -> raise Not_in_context

  let dim_of mono ctxt =
    try
      MonomialMap.find mono ctxt.mono_to_dim
    with Not_found -> raise Not_in_context

  let num_dimensions ctxt = ctxt.size

  let max_variable ctxt =
    SrkUtil.Int.Map.fold
      (fun _dim mono max_dim_opt ->
         BatEnum.fold
           (fun curr_dim_opt (dim, _pow) ->
              match curr_dim_opt with
              | Some curr_dim ->
                if curr_dim >= dim then Some curr_dim else Some dim
              | None -> Some dim)
           max_dim_opt (Monomial.enum mono))
      ctxt.dim_to_mono
      None

  let enum_by_dimension ctxt =
    SrkUtil.Int.Map.enum ctxt.dim_to_mono

  let enum_by_monomial ctxt =
    MonomialMap.enum ctxt.mono_to_dim

  let context_expand ctx ?increasing:(increasing=true) poly =
    let monos_list = BatList.of_enum (enum_by_dimension ctx) |> BatList.map (fun (_, m) -> m) in
    let new_monos = BatList.of_enum (QQXs.enum poly) |>
        BatList.map (fun (_, mono) -> mono) in
    context ~increasing ctx.ordering (monos_list @ new_monos)


  let string_of_dim_mono dim_pp dim mono =
    let () = Format.fprintf Format.str_formatter
        "(%a, %a)"
        dim_pp dim
        (Monomial.pp dim_pp) mono in
    Format.flush_str_formatter ()

  let string_of_mono_dim dim_pp mono dim =
    let () = Format.fprintf Format.str_formatter
        "(%a, %a)"
        (Monomial.pp dim_pp) mono
        dim_pp dim in
    Format.flush_str_formatter ()

  let pp_d2m_map dim_pp fmt (map : Monomial.t SrkUtil.Int.Map.t) =
    let l = SrkUtil.Int.Map.fold (fun dim mono l -> (dim, mono) :: l) map [] in
    let l = List.sort (fun (dim1, _mono1) (dim2, _mono2) -> dim1 - dim2) l in
    let s = String.concat ", "
              (List.map (fun (dim, mono) -> string_of_dim_mono dim_pp dim mono) l) in
    Format.pp_print_string fmt s

  let pp_m2d_map dim_pp fmt (map : int MonomialMap.t) =
    let l = MonomialMap.fold (fun mono dim l -> (mono, dim) :: l) map [] in
    let l = List.sort (fun (_mono1, dim1) (_mono2, dim2) -> dim1 - dim2) l in
    let s = String.concat ", "
              (List.map (fun (mono, idx) -> string_of_mono_dim dim_pp mono idx) l) in
    Format.pp_print_string fmt s

  let pp dim_pp fmt conv_ctxt =
    let () = Format.fprintf Format.str_formatter
        "@[dim-mono | mono-dim] = [%a | %a]@]"
        (pp_d2m_map dim_pp) conv_ctxt.dim_to_mono
        (pp_m2d_map dim_pp) conv_ctxt.mono_to_dim in
    let s = Format.flush_str_formatter () in
    Format.pp_print_string fmt s

end

module PolyVectorConversion = struct

  open PolyVectorContext

  let poly_to_vector ctxt p =
    BatEnum.fold
      (fun v (coeff, mono) ->
        Linear.QQVector.add_term coeff (dim_of mono ctxt) v)
      Linear.QQVector.zero
      (QQXs.enum p)

  let vector_to_poly ctxt v =
    BatEnum.fold (fun poly (scalar, dim) ->
        QQXs.add_term scalar (monomial_of dim ctxt) poly)
      QQXs.zero
      (Linear.QQVector.enum v)

end
