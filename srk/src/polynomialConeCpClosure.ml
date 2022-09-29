open BatPervasives
open Polynomial
open PolynomialUtil

module L = Log.Make(struct let name = "srk.polynomialConeCpClosure" end)

let integer_hull_method = ref `GomoryChvatal

module MonomialSet = BatSet.Make(Monomial)

let set_cutting_plane_method how = integer_hull_method := how

let pp_dim = PrettyPrint.pp_numeric_dim "x"

let pp_poly_list pp_dim =
  Format.pp_print_list ~pp_sep:(fun fmt _ -> Format.pp_print_text fmt ", ")
    (QQXs.pp pp_dim)

let pp_vectors pp_elem = SrkUtil.pp_print_list pp_elem

let context_of ?ordering:(ordering=Monomial.degrevlex) polys =
  PolyVectorContext.mk_context ordering polys

type affine_basis =
  { basis : QQXs.t list }

let make_affine_basis ideal affine_polys : affine_basis =
  let affine_polys = BatList.filter_map
                       (fun p -> let p' = Rewrite.reduce ideal p in
                                 if QQXs.equal p' QQXs.zero then None
                                 else Some p')
                       affine_polys in
  let ctxt = context_of affine_polys in
  let open PolynomialUtil in
  let vectors =
    List.map (PolyVectorConversion.poly_to_vector ctxt) affine_polys in
  let lattice = IntLattice.hermitize vectors in
  L.logf ~level:`trace "polylattice_spanned_by:
                        @[input affine polynomials: @[%a@] @]@;
                        @[transformed vectors: @[%a@] @]@;
                        @[lattice: @[%a@] @]@;
                        "
    (pp_poly_list pp_dim) affine_polys
    (pp_vectors Linear.QQVector.pp) vectors
    IntLattice.pp lattice;

  let basis = IntLattice.basis lattice
              |> List.map (fun v -> PolyVectorConversion.vector_to_poly ctxt v)
  in
  { basis }

type transformation_data =
  (** Pairs are s.t. the first component is for the polynomial 1, and the second
      component is for the rest.
   *)
  (** The fresh dimensions/variables introduced *)
  { codomain_dims: Monomial.dim * Monomial.dim list
  (** \y_dim. y_dim -> b *)
  ; substitutions: (Monomial.dim -> QQXs.t) * (Monomial.dim -> QQXs.t)
  (** { y_i - b_i }, where each b_i is in the lattice and y_i is fresh *)
  ; rewrite_polys: QQXs.t * QQXs.t list
  }

let pp_transformation_data pp_dim fmt transformation_data =
  Format.fprintf fmt
    "@[<v 0>{ codomain_dims: @[%a@]@;  rewrites: @[<v 0>%a@] }@]"
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") pp_dim)
    (fst transformation_data.codomain_dims :: snd transformation_data.codomain_dims)
    (pp_poly_list pp_dim)
    (fst transformation_data.rewrite_polys :: snd transformation_data.rewrite_polys)

(** [compute_transformation_data affine_basis ctxt]
    computes fresh dimensions Y = y_0, ..., y_n, with y_0 corresponding to 1,
    the substitution y_i |-> b_i for 0 <= i <= n,
    and the rewrite polynomials { f_i = y_i - b_i : 0 <= i <= n }.

    The dimensions Y are fresh with respect to [ctxt], which should include all
    monomials of all generators in the polynomial cone and [affine_basis],
    so that the dimensions are indeed fresh.
*)
let compute_transformation affine_basis ctxt : transformation_data =
  let fresh_start = Option.value ~default:0 (PolyVectorContext.max_variable ctxt) + 1 in

  L.logf ~level:`trace
    "compute_transformation:
     @[transformation context: @[%a@]@]@;
     @[fresh variables range from %d to %d@]@;
     "
    (PolyVectorContext.pp pp_dim) ctxt
    fresh_start (fresh_start + List.length affine_basis);

  let transformation_poly dim basis_poly =
    QQXs.sub (QQXs.of_dim dim) basis_poly in

  let adjoin substitution dim basis_poly =
    (fun i -> if i = dim then basis_poly else substitution i) in

  let codomain_one = fresh_start in
  let rewrite_one = transformation_poly codomain_one (QQXs.one) in
  let identity_subst = fun i -> QQXs.of_dim i in
  let substitute_one = adjoin identity_subst codomain_one QQXs.one in

  let (codomain_rest, substitution_rest, rewrite_rest) =
    (* { y_i - b_i } *)
    BatList.fold_lefti (fun (codims, substitution, rewrites) dim poly ->
        let new_dim = dim + (codomain_one + 1) in
        ( new_dim :: codims
        , adjoin substitution new_dim poly
        , transformation_poly new_dim poly :: rewrites))
      ([], identity_subst, []) affine_basis in

  let data =
    { codomain_dims = (codomain_one, codomain_rest)
    ; substitutions = (substitute_one, substitution_rest)
    ; rewrite_polys = (rewrite_one, rewrite_rest)
    }
  in
  L.logf ~level:`trace "compute_transformation: @[%a@]@;"
    (pp_transformation_data pp_dim) data;
  data

let polyhedron_of ctxt zeroes positives =
  L.logf ~level:`trace
    "polyhedron_of: conversion context for polyhedron is: @[%a@]@;"
    (PolyVectorContext.pp pp_dim)
    ctxt;
  let to_vector = PolyVectorConversion.poly_to_vector ctxt in
  let (linear_constraints, conic_constraints) =
    ( List.map (fun poly -> (`Zero, to_vector poly)) zeroes
    , List.map (fun poly -> (`Nonneg, to_vector poly)) positives ) in
  let p = Polyhedron.of_constraints
            (BatList.enum (List.append linear_constraints conic_constraints)) in
  L.logf ~level:`trace
    "@[polyhedron_of: @[<v 0>zeroes: @[<v 0>%a@]@; positives: @[%a@]@]@; is: %a@]@;"
    (pp_poly_list pp_dim) zeroes
    (pp_poly_list pp_dim) positives
    (Polyhedron.pp pp_dim) p;
  p

(**
   [compute_cut T C] computes [cl_{ZZ B}(C \cap QQ B)], where
   B = T.substitutions(T.codomain_dims) = { b_0 = 1, b_1, ..., b_n } is the
   basis for the lattice.

   1. Expand the cone C to contain the rewrite polynomials
      { y_i - b_i : 1 <= i <= n } of T in its ideal, and have its Groebner
      basis be with respect to an elimination order X > Y.
      (We can ignore 1.)

   2. Intersect with QQ[Y]^1, the affine space with dimensions Y.
      These two steps implement the inverse of the linear map sending the
      fresh Y's to QQ[X].

   3. Convert these generators to vectors and consider them as
      constraints defining a polyhedron. Take the integer hull.

   4. Convert back to polynomials and do the substitution y_i |-> b_i.
 *)
let compute_cut transform cone =

  (* 1. Expand the polynomial cone and project it onto QQ{1, y_1, ..., y_m}. *)
  let transform_polys = snd transform.rewrite_polys in
  let expanded = PolynomialCone.add_polys_to_cone cone transform_polys [] in
  let codims = Linear.const_dim :: snd transform.codomain_dims in
  let projected = PolynomialCone.project expanded (fun x -> List.mem x codims) in
  L.logf ~level:`trace "compute_cut: projected cone: @[%a@]@;"
    (PolynomialCone.pp pp_dim) projected;
  let (linear_zeroes, linear_positives) =
    (* Projection uses a graded elimination order keeping Y *)
    let p = PolynomialCone.restrict
              (fun m -> QQXs.degree (QQXs.add_term QQ.one m QQXs.zero) <= 1) projected in
    ( Rewrite.generators (PolynomialCone.get_ideal p)
    , PolynomialCone.get_cone_generators p)
  in
  L.logf ~level:`trace
    "compute_cut:
     @[zeroes: @[%a@]@]@;
     @[positives: @[%a@]@]@;"
    (pp_poly_list pp_dim) linear_zeroes
    (pp_poly_list pp_dim) linear_positives;

  (* 2. Integer hull *)
  let open PolynomialUtil in
  (* Conversion context to polyhedron.
     [linear_zeroes] and [linear_positives] are those of the expanded cone corresponding to
     [transform], so the fresh y_i's are already among them.
   *)
  let ctxt = context_of
               (List.concat [[QQXs.one] ; linear_zeroes; linear_positives]) in
  let polyhedron_to_hull = polyhedron_of ctxt linear_zeroes linear_positives in

  L.logf ~level:`trace "compute_cut: polyhedron to hull: @[%a@]@;computing integer hull...@;"
    (Polyhedron.pp pp_dim) polyhedron_to_hull;

  let hull = Polyhedron.integer_hull !integer_hull_method polyhedron_to_hull in
  L.logf ~level:`trace
    "compute_cut: computed integer hull: @[%a@]@;"
    (Polyhedron.pp pp_dim) hull;

  (* 3. Substitute back *)
  let (new_zeroes, new_positives) =
    BatEnum.fold (fun (zeroes, positives) (kind, v) ->
        let sub = snd transform.substitutions in
        let poly = PolyVectorConversion.vector_to_poly ctxt v
                   |> QQXs.substitute sub in
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
   [cutting_plane_operator C L], where (C, L) is a coherent cone-lattice pair,
   computes one round of (cutting plane closure + regular closure),
   and returns the new coherent (C', L').
 *)
let cutting_plane_operator polynomial_cone affine_basis =
  if (not (PolynomialCone.is_proper polynomial_cone)) || affine_basis.basis = []
  then
    (polynomial_cone, affine_basis)
  else
    let (zeroes, positives) =
      ( Rewrite.generators (PolynomialCone.get_ideal polynomial_cone)
      , PolynomialCone.get_cone_generators polynomial_cone) in
    let ctxt_x = context_of (List.concat [zeroes ; positives ; affine_basis.basis]) in
    let tdata =
      (* Introduce fresh dimensions/variables and associated data *)
      compute_transformation affine_basis.basis ctxt_x in
    let (linear, conic) = compute_cut tdata polynomial_cone in
    L.logf ~level:`trace "cutting_plane_operator: Cut computed@;";
    let cut_polycone = PolynomialCone.add_polys_to_cone polynomial_cone linear conic in
    L.logf ~level:`trace "cutting_plane_operator: result: @[%a@]@;"
      (PolynomialCone.pp pp_dim) cut_polycone;
    let new_basis =
      make_affine_basis (PolynomialCone.get_ideal cut_polycone) affine_basis.basis
    in
    (cut_polycone, new_basis)

(**
   [regular_cutting_plane_closure C L] computes the smallest regular
   polynomial cone that contains C and is closed with respect to the polynomial
   lattice spanned by L (and the polynomial 1).

   Termination is guaranteed by the Hilbert Basis theorem.
 *)
let regular_cutting_plane_closure polynomial_cone lattice_polys =
  let lattice_polys = QQXs.one :: lattice_polys in

  L.logf "regular_cutting_plane_closure:
          @[CP closure of: @[<v 0>%a@] @]@;
          @[with respect to @[%a@] @]@;"
    (PolynomialCone.pp pp_dim) polynomial_cone
    (pp_poly_list pp_dim) lattice_polys;

  (* The transformation is fixed for all iterations, because the lattice is fixed
       and the cutting plane closure does not introduce new monomials.
   *)
  let num_rounds = ref 0 in
  let rec closure cone affine_basis =
    let (cone', affine_basis') = cutting_plane_operator cone affine_basis in
    if PolynomialCone.leq cone' cone then
      begin
        L.logf "regular_cutting_plane_closure: closure took %d rounds@;" !num_rounds;
        (cone', affine_basis')
      end
    else
      begin
        L.logf "regular_cutting_plane_closure: closure round %d@;" !num_rounds;
        num_rounds := !num_rounds + 1;
        closure cone' affine_basis'
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
