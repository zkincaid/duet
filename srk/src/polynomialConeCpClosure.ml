open Polynomial
open PolynomialUtil

module L = Log.Make(struct let name = "srk.polynomialConeCpClosure" end)

module MonomialSet = BatSet.Make(Monomial)

let monomials_in polys =
  let monomials_in p =
    BatEnum.fold (fun s (_scalar, monomial) -> MonomialSet.add monomial s)
      MonomialSet.empty (QQXs.enum p)
  in
  List.fold_left (fun s p -> MonomialSet.union s (monomials_in p))
    MonomialSet.empty polys

(**
   [context_of monomials] computes conversion context consisting of a
   bijection between the set of monomials and a set X of dimensions.
 *)
let context_of monomials =
  (* TODO: Verify that reverse lexicographic + increasing means that the
     fresh monomials y0, y1, ... introduced in the construction of the linear
     map for cut are given indices in the same order in the context.
     y0 should be the fresh monomial corresponding to 1.
     Specifically: y0 < y1 < y2 < ... in terms of monomial dimension,
     and we also want y0 < y1 < y2 < ... in terms of dimension in the
     polynomial-vector context.
     For lex, lower dimension wins, so in revlex, higher dimension wins,
     so increasing means lower dimension to higher.

     We don't strictly need this yet, but it will be useful if we want to
     implement the substitution y0 |-> 1 without doing polynomial-vector
     conversions.
   *)
  PolyVectorContext.context Monomial.degrevlex monomials

let zzvector_to_qqvector vec =
  BatEnum.fold (fun v (scalar, dim) -> Linear.QQVector.add_term (QQ.of_zz scalar) dim v)
    Linear.QQVector.zero
    (Linear.ZZVector.enum vec)

(** Denominator, the constant polynomial, and the other basis polynomials. 

    TODO: The constant polynomial should always be 1, for otherwise the cutting 
    plane axiom can lead to inconsistency, e.g. if 1/3 is in the lattice, 
    3(1/3) + (-1/2) >= 0 =>  1/3 - 1 >= 0.
    We should thus be able to return only the denominator and the other basis
    polynomials after testing is done.
*)
type polylattice = ZZ.t * QQXs.t * QQXs.t list

exception Invalid_lattice

(** [lattice_spanned_by polys] computes Hermite Normal Form basis
    { (1/d) b_0 = (1/d) 1, (1/d) b_1, ..., (1/d) b_n } for the lattice spanned
    by [polys] AND the polynomial 1, and returns (d, (b_1, ..., b_n)).
    Note that b_0 = 1 is omitted; it is implicit.
*)
let lattice_spanned_by polys : polylattice =
  let polys = QQXs.one :: polys in
  (* TODO: Verify that ctxt has the monomial 1 in position 0. *)
  let ctxt = monomials_in polys |> MonomialSet.to_list |> context_of in
  let open PolynomialUtil in
  let vectors =
    List.map (PolyVectorConversion.poly_to_vector ctxt) polys in
  let (denom, basis) = IntLattice.basis (IntLattice.lattice_of vectors) in
  let (one, others) =
    List.partition
      (fun v ->
        Linear.QQVector.equal (zzvector_to_qqvector v)
          (Linear.const_linterm (QQ.of_zz denom)))
      basis
  in
  if (List.length one <> 1)
  then
  (* Lattice must contain 1. Since we add 1 above, this happens if there is 
     a non-integral rational in the lattice, which may lead to 
     inconsistency, e.g., if 1/2 is in the lattice, 2 (1/2) + (-1) >= 0
     implies 1/2 + floor(-1/2) >= 0, which implies -1/2 >= 0.
   *)
    let pp_vectors =
      Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", @;")
        Linear.ZZVector.pp in
    L.logf
        "@[<v 0>lattice_spanned_by: 1 not in basis:@;denominator = %a;@;vectors are: @[%a@]@]"
        ZZ.pp denom pp_vectors (List.append one others);
    raise Invalid_lattice
  else
    ();
  
  let constant_poly = zzvector_to_qqvector (List.hd one)
                      |> PolyVectorConversion.vector_to_poly ctxt
  in  
  let basis_polys =
    List.map (fun v -> zzvector_to_qqvector v
                       |> PolyVectorConversion.vector_to_poly ctxt)
      others in
  (denom, constant_poly, basis_polys)

type transformation_data =
  (* Pairs are s.t. the first component is for the polynomial 1, and the second
     component is for the rest.
   *)
  { codomain_dims: Monomial.dim * Monomial.dim list
    (* dimension for polynomial 1 is the smallest fresh variable/dimension
       introduced
     *)
  ; substitutions: (Monomial.dim -> QQXs.t) * (Monomial.dim -> QQXs.t)
  (* \y_dim. y_dim -> b *)
  ; rewrite_polys: QQXs.t * QQXs.t list
  (* { y_i - b_i }, where each b_i is in the lattice and y_i is fresh *)
  }

let pp_transformation_data pp_dim fmt transformation_data =
  Format.fprintf fmt
    "@[Transformation data:@;@[Rewrites: %a@]@;@[codomain_dims: %a@]@]@;"
    (PrettyPrintPoly.pp_poly_list (PrettyPrintDim.pp_numeric "x"))
    (fst transformation_data.rewrite_polys :: snd transformation_data.rewrite_polys)
    (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_dim)
    (fst transformation_data.codomain_dims :: snd transformation_data.codomain_dims)

(** [compute_transformation_data lattice ctxt], where 
    [lattice] = (d, b_1, ..., b_n) is s.t. 1/d { b_0 = 1, b_1, ..., b_n } is a
    basis for a lattice, and 
    [ctxt] is the conversion context betweeen polynomials in the lattice 
    (and polynomial cone) and a set of dimensions X,
    computes fresh dimensions Y = y_0, ..., y_n, with y_0 corresponding to 1,
    the substitution y_i |-> b_i for 0 <= i <= n,
    and the rewrite polynomials { f_i = y_i - b_i : 0 <= i <= n }.
*)
let compute_transformation lattice ctxt : transformation_data =
  let (denom, one, lattice) = lattice in
  let rescale poly = QQXs.scalar_mul (QQ.inverse (QQ.of_zz denom)) poly in
  let fresh_start = Option.value ~default:0 (PolyVectorContext.max_dimension ctxt) + 1 in

  L.logf ~level:`trace "compute_transformation: transformation context: %a\n"
    (PolyVectorContext.pp (PrettyPrintDim.pp_numeric "x"))
      ctxt;
  L.logf ~level:`trace "compute_transformation: fresh variables range from %d to %d\n"
    fresh_start (fresh_start + List.length lattice);

  let transformation_poly dim basis_poly =
    QQXs.sub (QQXs.of_dim dim) (rescale basis_poly) in

  let adjoin substitution dim basis_poly =
    (fun i -> if i = dim then rescale basis_poly else substitution i) in

  let codomain_one = fresh_start in
  let rewrite_one = transformation_poly codomain_one one in
  let identity_subst = fun i -> QQXs.of_dim i in
  let substitute_one = adjoin identity_subst codomain_one QQXs.one in

  let (codomain_rest, substitution_rest, rewrite_rest) =
    (* { y_i - b_i } *)
    BatList.fold_lefti (fun (codims, substitution, rewrites) dim poly ->
        let new_dim = dim + (codomain_one + 1) in
        ( new_dim :: codims
        , adjoin substitution new_dim poly
        , transformation_poly new_dim poly :: rewrites))
      ([], identity_subst, []) lattice in

  let data =
    { codomain_dims = (codomain_one, codomain_rest)
    ; substitutions = (substitute_one, substitution_rest)
    ; rewrite_polys = (rewrite_one, rewrite_rest)
    }
  in
  L.logf ~level:`trace "@[compute_transformation: %a@]"
    (pp_transformation_data (PrettyPrintDim.pp_numeric "x")) data;
  data

(**
   [expand_cone polynomial_cone transform] adjoins the rewrite polynomials 
   {y_i - b_i : 0 <= i <= n} from [transform] to the zeros of
   [polynomial_cone], computes a Groebner basis for the new ideal,
   and reduces the positives with respect to the basis.
 *)
let expand_cone polynomial_cone transform =
  let elim_order =
    (* order must have original x > fresh y's and be graded on y's. *)
    Monomial.block [fun dim -> dim < fst transform.codomain_dims]
      Monomial.degrevlex (* Reverse lexicographic within each block *)
  in
  let generators = PolynomialCone.get_ideal polynomial_cone |> Rewrite.generators in
  let positives = PolynomialCone.get_cone_generators polynomial_cone in
  let expanded_ideal =
    let transform_polys = fst transform.rewrite_polys :: snd transform.rewrite_polys in
    List.append generators transform_polys
    |> Rewrite.mk_rewrite elim_order
  in
  (* Use PolynomialCone to reduce the positives *)
  PolynomialCone.make_enclosing_cone expanded_ideal positives

(**
   [compute_cut ctxt transform zeroes positives]:
   - Sends [zeroes] and [positives] to QQ {y_0, y_1, ..., y_n} 
     ([transform.codomain_dims]) by converting the polynomials to polyhedra 
     using [ctxt], and projecting the polyhedron onto Y to get the intersection 
     (which is the image of the linear map).
     (TODO: Use [PolynomialCone.project] directly.)
   - Substitute y_0 |-> 1 throughout.
   - Compute integral hull.
   - Convert back to polynomials and do the substitution y_i |-> b_i.
 *)
let compute_cut ctxt transform zeroes positives =
  let open PolynomialUtil in
  let linear_constraints =
    List.map (fun poly ->
        PolyVectorConversion.poly_to_vector ctxt poly
        |> fun v -> (`Zero, v) ) zeroes in
  let conic_constraints =
    List.map (fun poly ->
        PolyVectorConversion.poly_to_vector ctxt poly
        |> fun v -> (`Nonneg, v) ) positives in
  let expanded_polyhedron =
    Polyhedron.of_constraints
      (BatList.enum (List.append linear_constraints conic_constraints)) in
  (* 1. Project out the original dimensions and substitute y0 |-> 1 *)
  let dimension_for_one = fst transform.codomain_dims in
  let original_dimensions =
    BatEnum.fold (fun l (dim, _mono) -> if dim < dimension_for_one then dim :: l else l)
      []
      (PolyVectorContext.enum_by_dimension ctxt) in
  (* TODO: Is the projection of constraints the same as projection of generators? *)
  let projected = Polyhedron.project original_dimensions expanded_polyhedron in
  let substitute_one v =
    let entry = Linear.QQVector.coeff dimension_for_one v in
    Linear.QQVector.of_term entry dimension_for_one
    |> Linear.QQVector.sub v
    |> Linear.QQVector.add (Linear.QQVector.of_term entry Linear.const_dim)
  in
  let substituted_constraints =
    BatEnum.fold (fun constraints (kind, v) ->
        let u = substitute_one v in
        match kind with
        | `Zero -> (`Zero, u) :: constraints
        | `Nonneg -> (`Nonneg, u) :: constraints
        | `Pos -> failwith "compute_cut: Image of polynomial cone should not contain open faces"
      )
      [] (Polyhedron.enum_constraints projected)
  in
  (* 2. Integer hull *)
  let hull = Polyhedron.of_constraints (BatList.enum substituted_constraints)
             |> Polyhedron.integer_hull in
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
  (new_zeroes, new_positives)

(**
   [cutting_plane_closure L C]:
   - Check if the ideal is the whole ring.
   - Compute basis B = { b_0 = 1, b_1, ..., b_n} for lattice L.
   - Compute context for L and C assigning monomials to set X of dimensions.
   - Compute transformation data containing fresh variables Y disjoint from X.
   - Expand cone.
   - Compute context for L, C, Y to embed polynomial cone into QQ Y.
   - Compute cut.
   - Take the union with the original cone.
 *)
let cutting_plane_closure lattice polynomial_cone =
  let ideal = PolynomialCone.get_ideal polynomial_cone in
  let is_full_ring =
    Rewrite.reduce ideal QQXs.one
    |> (fun p -> QQXs.equal p (QQXs.zero))
  in
  if is_full_ring then
    polynomial_cone (* cutting plane closure is itself *)
  else
    let polylattice = lattice_spanned_by lattice in
    let (zeroes, positives) =
      ( Rewrite.generators ideal
      , PolynomialCone.get_cone_generators polynomial_cone) in
    let ctxt_x = monomials_in (List.append zeroes positives)
                 |> MonomialSet.to_list
                 |> context_of in
    let transform = compute_transformation polylattice ctxt_x in
    let expanded_cone = expand_cone polynomial_cone transform in
    let (expanded_zeroes, expanded_positives) =
      ( Rewrite.generators (PolynomialCone.get_ideal expanded_cone)
      , PolynomialCone.get_cone_generators expanded_cone)
    in
    let ctxt_xy = monomials_in (List.append expanded_zeroes expanded_positives)
                  |> MonomialSet.to_list
                  |> context_of in
    let (linear, conic) =
      compute_cut ctxt_xy transform expanded_zeroes expanded_positives in
    PolynomialCone.add_polys_to_cone PolynomialCone.empty
      zeroes (* preserve original zeroes *)
      (List.concat [ linear ; List.map QQXs.negate linear ; conic ])
