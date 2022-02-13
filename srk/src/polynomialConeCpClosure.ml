open Polynomial
open PolynomialUtil

module L = Log.Make(struct let name = "srk.polynomialConeCpClosure" end)

(* let _ = Log.set_verbosity_level "srk.polynomialConeCpClosure" `trace *)

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
let context_of ?ordering:(ordering=Monomial.degrevlex) monomials =
  PolyVectorContext.context ordering monomials

let zzvector_to_qqvector vec =
  BatEnum.fold (fun v (scalar, dim) -> Linear.QQVector.add_term (QQ.of_zz scalar) dim v)
    Linear.QQVector.zero
    (Linear.ZZVector.enum vec)

(** Denominator, the constant polynomial, and the other basis polynomials.

    TODO: Check that the constant polynomial is always 1, for otherwise the cutting
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
let polylattice_spanned_by polys : polylattice =
  let polys = QQXs.one :: polys in
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
    L.logf ~level:`trace
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
  (** Pairs are s.t. the first component is for the polynomial 1, and the second
      component is for the rest. *)
  (** The fresh dimensions/variables introduced *)
  { codomain_dims: Monomial.dim * Monomial.dim list
  (** \y_dim. y_dim -> b *)
  ; substitutions: (Monomial.dim -> QQXs.t) * (Monomial.dim -> QQXs.t)
  (** { y_i - b_i }, where each b_i is in the lattice and y_i is fresh *)
  ; rewrite_polys: QQXs.t * QQXs.t list
  }

let pp_transformation_data pp_dim fmt transformation_data =
  Format.fprintf fmt
    "@[<v 0>{ @[codomain_dims: %a@] @;@[rewrites: @[<v 0>%a@]@] }@]"
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") pp_dim)
    (fst transformation_data.codomain_dims :: snd transformation_data.codomain_dims)
    (PrettyPrintPoly.pp_poly_list (PrettyPrintDim.pp_numeric "x"))
    (fst transformation_data.rewrite_polys :: snd transformation_data.rewrite_polys)

(** [compute_transformation_data polylattice ctxt], where

    [polylattice] = (d, b_1, ..., b_n) is s.t. 1/d { b_0 = 1, b_1, ..., b_n } is a
    basis for a polynomial lattice, and
    [ctxt] is the conversion context betweeen the set of polynomials in the
    polylattice (and polynomial cone), and a set of dimensions X,

    computes fresh dimensions Y = y_0, ..., y_n, with y_0 corresponding to 1,
    the substitution y_i |-> b_i for 0 <= i <= n,
    and the rewrite polynomials { f_i = y_i - b_i : 0 <= i <= n }.

    Need to ensure that [ctxt] contains all monomials in the lattice.
*)
let compute_transformation lattice ctxt : transformation_data =
  let (denom, one, lattice) = lattice in
  let rescale poly = QQXs.scalar_mul (QQ.inverse (QQ.of_zz denom)) poly in
  let fresh_start = Option.value ~default:0 (PolyVectorContext.max_variable ctxt) + 1 in

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
   [polynomial_cone], computes a Groebner basis with X > Y
   (Y the codomain variables, X the original variables) for the new ideal,
   and reduces the positives with respect to this basis.
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
   [compute_cut C T] computes [cl_{ZZ B}(C \cap QQ B)], where
   B = T.substitutions(T.codomain_dims) = { b_0 = 1, b_1, ..., b_n } is the
   basis for the lattice.

   - Expand the cone C to contain the rewrite polynomials
     { y_i - b_i : 0 <= i <= n } of T in its ideal, and have its Groebner
     basis be with respect to an elimination order X > Y.

   - Convert this cone to a polyhedron and project it onto the dimensions
     Y = y0, ..., y_n, the [codomain_dims] in T (i.e., the fresh variables).
     This implements intersection with QQ Y, which gives the image of the cone
     under the linear map defined by [transform].

     (TODO: Compare with using [PolynomialCone.project] directly, namely:
     compute the intersection of the polynomial cone with QQ[Y] (not QQ Y),
     and extract only the linear (affine) polynomials. Are these the same?)

   - Substitute y_0 |-> 1 throughout.

   - Compute the integral hull.

   - Convert back to polynomials and do the substitution y_i |-> b_i.
 *)
let compute_cut cone transform =
  (* 1. Expand the cone *)
  let expanded = expand_cone cone transform in
  let (zeroes, positives) =
    ( PolynomialCone.get_ideal expanded |> Rewrite.generators
    , PolynomialCone.get_cone_generators expanded)
  in
  let open PolynomialUtil in
  (* Conversion context to polyhedron.
     [zeroes] and [positives] are those of the expanded cone corresponding to
     [transform], so the fresh y_i's are already among them.
   *)
  let ctxt = monomials_in (List.concat [zeroes; positives])
             |> MonomialSet.to_list
             |> context_of in
  L.logf ~level:`trace
    "@[compute_cut: zeroes: @[%a@]@; positives: @[%a@]@]@;"
    (PolynomialUtil.PrettyPrintPoly.pp_poly_list (PrettyPrintDim.pp_numeric "x"))
    zeroes
    (PolynomialUtil.PrettyPrintPoly.pp_poly_list (PrettyPrintDim.pp_numeric "x"))
    positives;

  L.logf ~level:`trace
    "@[compute_cut: context is: @[%a@]@]@;"
    (PolyVectorContext.pp (PrettyPrintDim.pp_numeric "x"))
    ctxt;

  (* 2. Convert to polyhedron *)
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

  (* 3. Project out the original dimensions *)
  let (y0, ys) =
    let dim_of mono = PolyVectorContext.dim_of (Monomial.singleton mono 1) ctxt in
    (dim_of (fst transform.codomain_dims), List.map dim_of (snd transform.codomain_dims))
  in
  let ys_set = List.fold_left (fun s y -> SrkUtil.Int.Set.add y s)
                 SrkUtil.Int.Set.empty (y0 :: ys)
  in
  let original_dimensions =
    BatEnum.fold (fun l (dim, _mono) ->
        if SrkUtil.Int.Set.mem dim ys_set then l else (dim :: l))
      []
      (PolyVectorContext.enum_by_dimension ctxt) in
  let projected = Polyhedron.project original_dimensions expanded_polyhedron in

  (* 4. Substitute y_0 |-> one *)
  let substitute_one v =
    let entry = Linear.QQVector.coeff y0 v in
    Linear.QQVector.of_term entry y0
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
  let polyhedron_to_hull = Polyhedron.of_constraints (BatList.enum substituted_constraints) in

  (* 5. Integer hull *)
  let hull = Polyhedron.integer_hull polyhedron_to_hull in

  (* 6. Substitute back *)
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
    "compute_cut: original dimensions to project out: @[%a@]@;"
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
       (PrettyPrintDim.pp_numeric "x"))
    original_dimensions;

  L.logf ~level:`trace
    "compute_cut: @[polyhedron before projection: %a@];"
    (Polyhedron.pp (PrettyPrintDim.pp_numeric "x")) expanded_polyhedron;

  L.logf ~level:`trace
    "compute_cut: @[polyhedron after projection: %a@];"
    (Polyhedron.pp (PrettyPrintDim.pp_numeric "x")) projected;

  L.logf ~level:`trace
    "compute_cut: @[polyhedron after y0 |-> 1: %a@];"
    (Polyhedron.pp (PrettyPrintDim.pp_numeric "x")) polyhedron_to_hull;

  L.logf ~level:`trace
    "compute_cut: @[integer hull: %a@];"
    (Polyhedron.pp (PrettyPrintDim.pp_numeric "x")) hull;

  L.logf ~level:`trace
    "compute_cut: @[zeroes: @[%a@]@;positives: @[%a@]@];"
    (PrettyPrintPoly.pp_poly_list (PrettyPrintDim.pp_numeric "x")) new_zeroes
    (PrettyPrintPoly.pp_poly_list (PrettyPrintDim.pp_numeric "x")) new_positives;

  (new_zeroes, new_positives)

(**
   [cutting_plane_closure L C]:
   - Check if the ideal is the whole ring or if L = [] (1 is implicit);
     if so, C is already closed under CP-INEQ.
   - Compute basis B = { b_0 = 1, b_1, ..., b_n } for polynomial lattice L.
   - Compute context for L and C assigning monomials to set X of dimensions.
   - Compute transformation data containing fresh variables Y disjoint from X.
   - Expand cone.
   - Compute context for L, C, Y to embed polynomial cone C into QQ Y.
   - Compute cut.
   - Take the union with the original cone.
 *)
let cutting_plane_closure lattice polynomial_cone =
  L.logf ~level:`trace "CP closure of: @[%a@]@;with respect to @[%a@]"
    (PolynomialCone.pp (PrettyPrintDim.pp_numeric "x"))
    polynomial_cone
    (PrettyPrintPoly.pp_poly_list (PrettyPrintDim.pp_numeric "x"))
    lattice;

  let ideal = PolynomialCone.get_ideal polynomial_cone in
  let is_full_ring =
    Rewrite.reduce ideal QQXs.one
    |> (fun p -> QQXs.equal p (QQXs.zero))
  in
  if is_full_ring || lattice = [] then
    (* cutting plane closure is itself; note that the else branch requires the
       ideal to be proper, so this is not just an optimization!
     *)
    polynomial_cone
  else
    let polylattice = polylattice_spanned_by lattice in
    let (_denom, one, basis) = polylattice in
    let (zeroes, positives) =
      ( Rewrite.generators ideal
      , PolynomialCone.get_cone_generators polynomial_cone) in
    let ctxt_x = monomials_in (List.concat [zeroes ; positives ; [one]; basis])
                 |> MonomialSet.to_list
                 |> context_of in
    compute_transformation polylattice ctxt_x
    |> (fun tdata -> L.logf ~level:`trace "Transformation data computed@;"; tdata)
    |> compute_cut polynomial_cone
    |> (fun (linear, conic) -> L.logf ~level:`trace "Cut computed@;"; (linear, conic))
    |> (fun (linear, conic) ->
      PolynomialCone.add_polys_to_cone PolynomialCone.trivial
        (List.concat [ zeroes ; linear ])
        (List.concat [ positives ; conic ]))
