open BatPervasives
open Polynomial

module PV = Polynomial.LinearQQXs

module L = Log.Make(struct let name = "srk.polynomialConeCpClosure" end)

let integer_hull_method = ref (`GomoryChvatal : [`GomoryChvatal | `Normaliz])

let set_cutting_plane_method how = integer_hull_method := how

let pp_dim = Polynomial.pp_numeric_dim "x"

let pp_poly_list pp_dim =
  Format.pp_print_list ~pp_sep:(fun fmt _ -> Format.pp_print_text fmt ", ")
    (QQXs.pp pp_dim)

type affine_basis =
  { basis : QQXs.t list }

module MonomialSet =
  BatSet.Make(struct type t = Monomial.t
                     let compare x y = match Monomial.degrevlex x y with
                       | `Lt -> -1
                       | `Eq -> 0
                       | `Gt -> 1
              end)

let _highest_dim_in_mono mono =
  BatEnum.fold
    (fun curr (dim, _power) ->
      Int.max dim curr)
    (Linear.const_dim) (Monomial.enum mono)

let fresh_dim polys =
  let fresh =
    List.fold_left
      (fun curr_fresh poly ->
        QQXs.dimensions poly
        |> SrkUtil.Int.Set.max_elt_opt
        |> (fun d ->
         match d with
         | Some d ->
            Int.max curr_fresh (d + 1)
         | None -> curr_fresh))
      Linear.const_dim
      polys in
  if fresh < 0 then 0 else fresh

(** TODO: Check if we need degrevlex order when densifying into vectors for
    integer hull. *)
let make_context polys =
  let monos =
    polys
    |> List.fold_left
         (fun monos poly ->
           QQXs.enum poly
           |> BatEnum.fold (fun s (_coeff, mono) -> MonomialSet.add mono s) monos)
         MonomialSet.empty
  in
  PV.make_context (MonomialSet.elements monos)

let make_affine_basis ideal affine_polys : affine_basis =
  let affine_polys = BatList.filter_map
                       (fun p -> let p' = Rewrite.reduce ideal p in
                                 if QQXs.equal p' QQXs.zero then None
                                 else Some p')
                       affine_polys in
  let ctx = make_context affine_polys in
  let vectors = List.map (PV.densify_affine ctx) affine_polys in
  let lattice = IntLattice.hermitize vectors in
  L.logf ~level:`trace "make_affine_basis: of polynomials: @[%a@]@."
    (pp_poly_list pp_dim) affine_polys;
  let basis = IntLattice.basis lattice
              |> List.map (fun v -> PV.sparsify_affine ctx v)
  in
  { basis }

type transformation =
  { linear_map : (Monomial.dim * QQXs.t) list
  (** \y_dim. y_dim -> b *)
  ; substitutions: (Monomial.dim -> QQXs.t)
  }

let pp_transformation pp_dim fmt transformation =
  Format.fprintf fmt "%a"
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
       (fun fmt (a, b) ->
         Format.fprintf fmt "%d |-> %a" a (QQXs.pp pp_dim) b))
    transformation.linear_map

let make_transformation image fresh : transformation * int =
  let adjoin substitution dim basis_poly =
    (fun i -> if i = dim then basis_poly else substitution i) in
  let identity_subst = fun i -> QQXs.of_dim i in
  let (new_fresh, linear_map, substitutions) =
    List.fold_left
      (fun (curr_fresh, map, subst) poly ->
        (curr_fresh + 1
        , (curr_fresh, poly) :: map
        , adjoin subst curr_fresh poly))
      (fresh, [], identity_subst)
      image in
  let transformation = { linear_map ; substitutions } in
  L.logf ~level:`trace
    "make_transformation: @[%a@], new fresh = %d@;"
    (pp_transformation pp_dim) transformation
    new_fresh;
  ( transformation, new_fresh )

let polyhedron_of ctx zeroes positives =
  L.logf ~level:`trace
    "polyhedron_of: conversion context for polyhedron is: @[%a@]@;"
    (PV.pp (Monomial.pp pp_dim))
    ctx;
  let to_vector = PV.densify_affine ctx in
  let (linear_constraints, conic_constraints) =
    ( List.map (fun poly -> (`Zero, to_vector poly)) zeroes
    , List.map (fun poly -> (`Nonneg, to_vector poly)) positives ) in
  let p = Polyhedron.of_constraints
            (BatList.enum (List.append linear_constraints conic_constraints)) in
  L.logf ~level:`trace
    "@[polyhedron_of: @[<v 0>zeroes: @[<v 0>%a@]@; positives: @[%a@]@]@. is: %a@]@;"
    (pp_poly_list pp_dim) zeroes
    (pp_poly_list pp_dim) positives
    (Polyhedron.pp pp_dim) p;
  p

let compute_cut cone affine_basis =
  if (not (PolynomialCone.is_proper cone)) || affine_basis.basis = [] then
    ([], [])
  else
    (* 1. Compute inverse linear map of cone under affine basis linear map *)
    let (zeroes, positives) =
      ( Rewrite.generators (PolynomialCone.get_ideal cone)
      , PolynomialCone.get_cone_generators cone) in
    let fresh = fresh_dim (List.concat [zeroes ; positives ; affine_basis.basis]) in
    let (transform, _new_fresh) = make_transformation affine_basis.basis fresh in
    let (linear_zeroes, linear_positives) =
      PolynomialCone.inverse_linear_map cone transform.linear_map
    in
    L.logf ~level:`trace
      "compute_cut:
       @[zeroes: @[%a@]@]@;
       @[positives: @[%a@]@]@;"
      (pp_poly_list pp_dim) linear_zeroes
      (pp_poly_list pp_dim) linear_positives;

    (* 2. Integer hull *)
    let ctx = make_context (List.concat [linear_zeroes; linear_positives]) in
    let polyhedron_to_hull = polyhedron_of ctx linear_zeroes linear_positives
    in

    L.logf ~level:`trace
      "compute_cut: polyhedron to hull: @[%a@]@;computing integer hull using %s...@;"
      (Polyhedron.pp pp_dim) polyhedron_to_hull
      (match !integer_hull_method with
       | `GomoryChvatal -> "Gomory-Chvatal"
       | `Normaliz -> "Normaliz"
      );

    let hull = Polyhedron.integer_hull ~decompose:true
                 !integer_hull_method polyhedron_to_hull
    in
    L.logf ~level:`trace
      "compute_cut: computed integer hull: @[%a@]@;"
      (Polyhedron.pp pp_dim) hull;

    (* 3. Substitute back to compute the forward image *)
    let (new_zeroes, new_positives) =
      BatEnum.fold (fun (zeroes, positives) (kind, v) ->
          let sub = transform.substitutions in
          let poly = QQXs.substitute sub (PV.sparsify_affine ctx v)
          in
          match kind with
          | `Zero -> (poly :: zeroes, positives)
          | `Nonneg -> (zeroes, poly :: positives)
          | `Pos -> failwith "compute_cut: Image of polynomial cone should not contain open faces"
        )
        ([], []) (Polyhedron.enum_constraints hull)
    in

    L.logf ~level:`trace
      "compute_cut: result is:
       @[zeroes: @[%a@]@]@;
       @[positives: @[%a@]@]@;"
      (pp_poly_list pp_dim) new_zeroes
      (pp_poly_list pp_dim) new_positives;

    (new_zeroes, new_positives)

(**
   [regular_cutting_plane_closure C L] computes the smallest regular
   polynomial cone that contains C and is closed with respect to the polynomial
   lattice spanned by L (and the polynomial 1).

   Termination is guaranteed by the Hilbert Basis theorem.
 *)
let regular_cutting_plane_closure polynomial_cone lattice_polys =
  let lattice_polys = QQXs.one :: lattice_polys in

  L.logf "regular_cutting_plane_closure:@.
          CP closure of: @[<hov>%a@]@;
          with respect to @[%a@]@;"
    (PolynomialCone.pp pp_dim) polynomial_cone
    (pp_poly_list pp_dim) lattice_polys;

  let num_rounds = ref 0 in
  let rec closure cone affine_basis =

    let (new_zeroes, new_positives) = compute_cut cone affine_basis in
    let new_cone = PolynomialCone.add_generators
                     ~zeros:new_zeroes
                     ~nonnegatives:new_positives cone in
    if PolynomialCone.leq new_cone cone then
      (* A better way is to augment [add_generators] to tell us if the cone
         has truly expanded. *)
      begin
        L.logf "regular_cutting_plane_closure: closure took %d rounds@;" !num_rounds;
        (new_cone, affine_basis)
      end
    else
      begin
        L.logf "regular_cutting_plane_closure: closure round %d@;" !num_rounds;
        num_rounds := !num_rounds + 1;
        let new_affine_basis =
          make_affine_basis (PolynomialCone.get_ideal new_cone) affine_basis.basis in
        closure new_cone new_affine_basis
      end
  in
  let affine_basis = make_affine_basis (PolynomialCone.get_ideal polynomial_cone)
                       lattice_polys in
  let (final_cone, final_lattice) =
    closure polynomial_cone affine_basis
  in
  L.logf "regular_cutting_plane_closure: concluded, closure is:@;  @[%a@]@;"
    (PolynomialCone.pp pp_dim)
    final_cone;
  let ideal = Rewrite.generators (PolynomialCone.get_ideal final_cone)
              |> Ideal.make in
  (final_cone, PolynomialLattice.make ideal final_lattice.basis)
