open Polynomial
open PolynomialUtil

module L = Log.Make(struct let name = "srk.polynomialConeCpClosure" end)

(* let _ = Log.set_verbosity_level "srk.polynomialConeCpClosure" `trace *)

module MonomialSet = BatSet.Make(Monomial)

let pp_dim = PrettyPrint.pp_numeric_dim "x"

let pp_poly_list = PolynomialUtil.PrettyPrint.pp_poly_list
let pp_vectors pp_elem = SrkUtil.pp_print_list pp_elem

(*
let monomials_in polys =
  let monomials_in p =
    BatEnum.fold (fun s (_scalar, monomial) -> MonomialSet.add monomial s)
      MonomialSet.empty (QQXs.enum p)
  in
  List.fold_left (fun s p -> MonomialSet.union s (monomials_in p))
    MonomialSet.empty polys
 *)

let context_of ?ordering:(ordering=Monomial.degrevlex) polys =
  PolyVectorContext.mk_context ordering polys

let zzvector_to_qqvector vec =
  BatEnum.fold (fun v (scalar, dim) -> Linear.QQVector.add_term (QQ.of_zz scalar) dim v)
    Linear.QQVector.zero
    (Linear.ZZVector.enum vec)

(** TODO: Check that the constant polynomial is always 1, for otherwise the cutting
    plane axiom can lead to inconsistency, e.g. if 1/3 is in the lattice,
    3(1/3) + (-1/2) >= 0 =>  1/3 - 1 >= 0.
    We should thus be able to return only the denominator and the other basis
    polynomials after testing is done.
*)
type polylattice =
  { denominator : ZZ.t
  ; constant_poly : QQXs.t
  ; basis_polys : QQXs.t list
  ; lattice_context : PolyVectorContext.t
  ; int_lattice : IntLattice.t
  }

let pp_polylattice pp_dim fmt polylattice =
  Format.fprintf fmt
    "@[<v 0>{ denominator: @[%a@]@;; constant_poly: @[%a@]@;; basis_polys: @[<v 0>%a@] }@]"
    ZZ.pp polylattice.denominator
    (QQXs.pp pp_dim) polylattice.constant_poly
    (pp_poly_list pp_dim) polylattice.basis_polys

exception Invalid_lattice

(** [lattice_spanned_by polys] computes Hermite Normal Form basis
    { (1/d) b_0 = (1/d) 1, (1/d) b_1, ..., (1/d) b_n } for the lattice spanned
    by [polys] AND the polynomial 1, and returns (d, (b_1, ..., b_n)).
    Note that b_0 = 1 is omitted; it is implicit.
*)
let polylattice_spanned_by polys : polylattice =
  let polys = QQXs.one :: polys in
  let ctxt = context_of polys in
  let open PolynomialUtil in
  let vectors =
    List.map (PolyVectorConversion.poly_to_vector ctxt) polys in
  let lattice = IntLattice.lattice_of vectors in
  let (denominator, basis) = IntLattice.basis lattice in
  let (one, others) =
    List.partition
      (fun v ->
        Linear.QQVector.equal (zzvector_to_qqvector v)
          (Linear.const_linterm (QQ.of_zz denominator)))
      basis
  in
  L.logf "polylattice_spanned_by: input polynomials: @[%a@]@;"
    (PolynomialUtil.PrettyPrint.pp_poly_list pp_dim) polys;
  L.logf "polylattice_spanned_by: transformed vectors: @[%a@]@;"
    (pp_vectors Linear.QQVector.pp)
    vectors;
  L.logf "polylattice_spanned_by: lattice: @[%a@]@;"
    IntLattice.pp lattice;
  if (List.length one <> 1)
  then
  (* Lattice must contain 1. Since we add 1 above, this happens if there is
     a non-integral rational in the lattice, which may lead to
     inconsistency, e.g., if 1/2 is in the lattice, 2 (1/2) + (-1) >= 0
     implies 1/2 + floor(-1/2) >= 0, which implies -1/2 >= 0.
   *)
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
  { denominator
  ; constant_poly
  ; basis_polys
  ; int_lattice = lattice
  ; lattice_context = ctxt
  }

let in_polylattice poly polylattice =
  let open PolynomialUtil in
  try
    let v = PolyVectorConversion.poly_to_vector polylattice.lattice_context poly in
    IntLattice.member v polylattice.int_lattice
  with PolyVectorContext.Not_in_context ->
    false

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
    "@[<v 0>{ codomain_dims: @[%a@]@;  rewrites: @[<v 0>%a@] }@]"
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") pp_dim)
    (fst transformation_data.codomain_dims :: snd transformation_data.codomain_dims)
    (pp_poly_list pp_dim)
    (fst transformation_data.rewrite_polys :: snd transformation_data.rewrite_polys)

(** [compute_transformation_data polylattice ctxt], where

    [polylattice] = (d, b_1, ..., b_n) is s.t. 1/d { b_0 = 1, b_1, ..., b_n } is a
    basis for a polynomial lattice, and
    [ctxt] is the conversion context betweeen the set of polynomials in the
    polylattice and polynomial cone, and a set of dimensions X;

    computes fresh dimensions Y = y_0, ..., y_n, with y_0 corresponding to 1,
    the substitution y_i |-> b_i for 0 <= i <= n,
    and the rewrite polynomials { f_i = y_i - b_i : 0 <= i <= n }.

    Need to ensure that [ctxt] contains all monomials in the lattice.
*)
let compute_transformation lattice ctxt : transformation_data =
  (* Polynomial generators of the lattice have to be converted to vectors
     using the combined context, not the one used in the formation of the
     lattice.
   *)
  let { denominator = denom ; constant_poly = one ; basis_polys = lattice ; _ }
    = lattice in
  let rescale poly = QQXs.scalar_mul (QQ.inverse (QQ.of_zz denom)) poly in
  let fresh_start = Option.value ~default:0 (PolyVectorContext.max_variable ctxt) + 1 in

  L.logf ~level:`trace "compute_transformation: transformation context: @[%a@]@;"
    (PolyVectorContext.pp pp_dim)
      ctxt;
  L.logf ~level:`trace "compute_transformation: fresh variables range from %d to %d@;"
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
  L.logf ~level:`trace "compute_transformation: @[%a@]@;"
    (pp_transformation_data pp_dim) data;
  data

(**
   [compute_cut T C] computes [cl_{ZZ B}(C \cap QQ B)], where
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
let compute_cut transform cone =
  (* 1. Expand the polynomial cone and project it onto QQ Y. *)
  let transform_polys = fst transform.rewrite_polys :: snd transform.rewrite_polys in
  let expanded = PolynomialCone.add_polys_to_cone cone transform_polys [] in
  let codim_one = fst transform.codomain_dims in
  let projected = PolynomialCone.project expanded (fun x ->
                      let codims = codim_one :: snd transform.codomain_dims in
                      List.mem x codims) in

  (* 2. Substitute y0 |-> 1 *)
  let (zeroes, positives) =
    ( Rewrite.generators (PolynomialCone.get_ideal projected)
    , PolynomialCone.get_cone_generators projected) in

  let substitute_one i =
    if i = codim_one then QQXs.one else QQXs.of_dim i
  in
  let (substituted_zeroes, substituted_positives) =
    let sub = QQXs.substitute substitute_one in
    (List.map sub zeroes, List.map sub positives) in

  (* 3. Convert to polyhedron *)
  let open PolynomialUtil in
  (* Conversion context to polyhedron.
     [zeroes] and [positives] are those of the expanded cone corresponding to
     [transform], so the fresh y_i's are already among them.
   *)
  let ctxt = context_of (List.concat [substituted_zeroes; substituted_positives])
  in

  L.logf ~level:`trace
    "compute_cut: @[zeroes: @[%a@]@;positives: @[%a@]@]@;"
    (pp_poly_list pp_dim) substituted_zeroes
    (pp_poly_list pp_dim) substituted_positives;

  L.logf ~level:`trace
    "compute_cut: context is: @[%a@]@;"
    (PolyVectorContext.pp pp_dim)
    ctxt;

  let to_vector = PolyVectorConversion.poly_to_vector ctxt in
  let (linear_constraints, conic_constraints) =
    ( List.map (fun poly -> (`Zero, to_vector poly)) substituted_zeroes
    , List.map (fun poly -> (`Nonneg, to_vector poly)) substituted_positives ) in
  let polyhedron_to_hull =
    Polyhedron.of_constraints
      (BatList.enum (List.append linear_constraints conic_constraints)) in
  L.logf ~level:`trace "compute_cut: polyhedron to hull: @[%a@]"
    (Polyhedron.pp pp_dim) polyhedron_to_hull;

  (* 4. Integer hull *)
  L.logf ~level:`trace
    "compute_cut: computing integer hull...@;";

  let hull = Polyhedron.integer_hull polyhedron_to_hull in
  L.logf ~level:`trace
    "compute_cut: computed integer hull@;";

  (* 5. Substitute back *)
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
    "compute_cut: polynomial cone after projection: @[%a@]@;"
    (PolynomialCone.pp pp_dim) projected;

  L.logf ~level:`trace
    "compute_cut: polyhedron to hull: @[%a@]@;"
    (Polyhedron.pp pp_dim) polyhedron_to_hull;

  L.logf ~level:`trace
    "compute_cut: integer hull: @[%a@]@;"
    (Polyhedron.pp pp_dim) hull;

  L.logf ~level:`trace
    "compute_cut: @[zeroes: @[%a@]@;positives: @[%a@]@];"
    (pp_poly_list pp_dim) new_zeroes
    (pp_poly_list pp_dim) new_positives;

  (new_zeroes, new_positives)


(**
   [cutting_plane_operator T C]: performs one round of the cutting plane
   operation, which when iterated until fixed point is the regular cutting
   plane closure of C with respect to the lattice defined by T
   (i.e., the one spanned by [T.substitutions(T.codomain_dims)]).

   - Check if the ideal is the whole ring;
     if so, C is already closed under CP-INEQ.
   - Otherwise, adjoin the linear and conic generators of [compute_cut T C]
     to C.
 *)
let cutting_plane_operator transformation_data polynomial_cone =
  let ideal = PolynomialCone.get_ideal polynomial_cone in
  let is_full_ring =
    Rewrite.reduce ideal QQXs.one
    |> (fun p -> QQXs.equal p (QQXs.zero))
  in
  if is_full_ring then
    (* cutting plane closure is itself; note that the else branch requires the
       ideal to be proper, so this is not just an optimization!
     *)
    begin
      L.logf ~level:`trace "cutting_plane_operator: ideal is already the full ring";
      polynomial_cone
    end
  else
    let (zeroes, positives) =
      ( Rewrite.generators (PolynomialCone.get_ideal polynomial_cone)
      , PolynomialCone.get_cone_generators polynomial_cone) in
    L.logf ~level:`trace
      "cutting_plane_operator: computing cut for:@;  @[zeroes: @[%a@]@;@[positives: @[%a@]@]@]@;"
      (pp_poly_list pp_dim) zeroes
      (pp_poly_list pp_dim) positives;

    let (linear, conic) = compute_cut transformation_data polynomial_cone in
    L.logf ~level:`trace "cutting_plane_operator: Cut computed@;";
    let cut_polycone = PolynomialCone.add_polys_to_cone polynomial_cone linear conic in
    L.logf ~level:`trace "cutting_plane_operator: result: @[%a@]"
      (PolynomialCone.pp pp_dim) cut_polycone;
    cut_polycone

(**
   [regular_cutting_plane_closure L C] computes the smallest regular
   polynomial cone that contains C and is closed with respect to the polynomial
   lattice L spanned by L (and the polynomial 1).

   - Compute basis B = { b_0 = 1, b_1, ..., b_n } for polynomial lattice L.
   - Compute context for L and C assigning monomials to set X of dimensions.
   - Compute transformation data containing fresh variables Y disjoint from X.
   - Iterate [cutting_plane_operator] until a fixed point is reached.

   Termination is guaranteed by the Hilbert Basis theorem.
 *)
let regular_cutting_plane_closure polylattice polynomial_cone =
  let { constant_poly = one ; basis_polys = basis ; _ } = polylattice in
  if basis = [] then
    (* CP-closure with only 1 in the lattice is just itself *)
    polynomial_cone
  else
    begin
      L.logf "regular_cutting_plane_closure: CP closure of:@;@[<v 0>@[%a@]@;  with respect to @[%a@]@]@;"
        (PolynomialCone.pp pp_dim) polynomial_cone
        (pp_poly_list pp_dim) basis;

      let (zeroes, positives) =
        ( Rewrite.generators (PolynomialCone.get_ideal polynomial_cone)
        , PolynomialCone.get_cone_generators polynomial_cone) in
      let ctxt_x = context_of (List.concat [zeroes ; positives ; [one]; basis]) in
      let tdata =
        (* Introduce fresh dimensions/variables and associated data *)
        compute_transformation polylattice ctxt_x
        |> (fun tdata -> L.logf ~level:`trace
                           "regular_cutting_plane_closure: Transformation data computed@;"; tdata)
      in
      (* The transformation is fixed for all iterations, because the lattice is fixed
       and the cutting plane closure does not introduce new monomials.
       *)
      let rec closure cone =
        let cone' = cutting_plane_operator tdata cone in
        if PolynomialCone.equal cone' cone then cone'
        else closure cone'
      in
      let final = closure polynomial_cone in
      L.logf "regular_cutting_plane_closure: closure is:@;  @[%a@]@;"
        (PolynomialCone.pp pp_dim)
        final;
      final
    end
