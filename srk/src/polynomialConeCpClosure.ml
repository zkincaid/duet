open BatPervasives
open Polynomial
open PolynomialUtil

module L = Log.Make(struct let name = "srk.polynomialConeCpClosure" end)

let _ = Log.set_verbosity_level "srk.polynomialConeCpClosure" `trace

module MonomialSet = BatSet.Make(Monomial)

let pp_dim = PrettyPrint.pp_numeric_dim "x"

let pp_poly_list = PolynomialUtil.PrettyPrint.pp_poly_list
let pp_vectors pp_elem = SrkUtil.pp_print_list pp_elem

let context_of ?ordering:(ordering=Monomial.degrevlex) polys =
  PolyVectorContext.mk_context ordering polys

let zzvector_to_qqvector vec =
  BatEnum.fold
    (fun v (scalar, dim) -> Linear.QQVector.add_term (QQ.of_zz scalar) dim v)
    Linear.QQVector.zero
    (Linear.ZZVector.enum vec)

(** A polynomial lattice L is of the form I + ZZ B,
    where I is an ideal and B is a finite set of polynomials that include 1
    and are reduced with respect to B.
    (The lattice is the same whether they are reduced or not.)
    1 is implicit in [affine_basis].
*)
type polylattice =
  { ideal : Rewrite.t
  ; affine_basis : QQXs.t list
  ; lattice_context : PolyVectorContext.t
  ; int_lattice : IntLattice.t
  }

let affine_generators polylattice = polylattice.affine_basis

let ideal_of polylattice = polylattice.ideal

let pp_polylattice pp_dim fmt polylattice =
  Format.fprintf fmt
    "{ affine_basis: @[<v 0>%a@]@;
       ideal: @[<v 0>%a@]
     }"
    (pp_poly_list pp_dim) polylattice.affine_basis
    (Rewrite.pp pp_dim) polylattice.ideal

let empty_polylattice ideal =
  { ideal
  ; affine_basis = []
  ; lattice_context = context_of []
  ; int_lattice = IntLattice.lattice_of []
  }

let polylattice_spanned_by ideal affine_polys : polylattice option =
  let affine_polys = BatList.filter_map
                       (fun p -> let p' = Rewrite.reduce ideal p in
                                 if QQXs.equal p' QQXs.zero then None
                                 else Some p')
                       (QQXs.one :: affine_polys) in
  let ctxt = context_of affine_polys in
  let open PolynomialUtil in
  let vectors =
    List.map (PolyVectorConversion.poly_to_vector ctxt) affine_polys in
  let lattice = IntLattice.lattice_of vectors in
  let (denominator, basis) = IntLattice.basis lattice in
  let (one, others) =
    List.partition
      (fun v ->
        Linear.QQVector.equal (zzvector_to_qqvector v)
          (Linear.const_linterm (QQ.of_zz denominator)))
      basis
  in
  L.logf "polylattice_spanned_by:
          @[input affine polynomials: @[%a@] @]@;
          @[transformed vectors: @[%a@] @]@;
          @[lattice: @[%a@] @]@;
          "
    (PolynomialUtil.PrettyPrint.pp_poly_list pp_dim) affine_polys
    (pp_vectors Linear.QQVector.pp) vectors
    IntLattice.pp lattice;

  let result =
    if (List.length one <> 1)
    then
      (* Since we add 1 above, this can only happen if the Hermite normal
     form contains 1/n for some integer n > 1.
     In that case, the cutting plane closure will be inconsistent:
     n(1/n) - 1 >= 0 --> 1/n - 1 >= 0 --> n <= 1, a contradiction.
     If the input polynomials have only integer coefficients,
     this cannot happen.
       *)
      None
    else
      let affine_basis =
        List.map (fun v ->
            zzvector_to_qqvector v
            |> Linear.QQVector.scalar_mul (QQ.inverse (QQ.of_zz denominator))
            |> PolyVectorConversion.vector_to_poly ctxt) others in
      Some { affine_basis
           ; ideal
           ; lattice_context = ctxt
           ; int_lattice = lattice
        }
  in
  result

let in_polylattice poly polylattice =
  let open PolynomialUtil in
  try
    Rewrite.reduce polylattice.ideal poly
    |> PolyVectorConversion.poly_to_vector polylattice.lattice_context
    |> (fun v -> IntLattice.member v polylattice.int_lattice)
  with PolyVectorContext.Not_in_context ->
    false

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

(**
   [compute_cut T C] computes [cl_{ZZ B}(C \cap QQ B)], where
   B = T.substitutions(T.codomain_dims) = { b_0 = 1, b_1, ..., b_n } is the
   basis for the lattice.

   - Expand the cone C to contain the rewrite polynomials
     { y_i - b_i : 1 <= i <= n } of T in its ideal, and have its Groebner
     basis be with respect to an elimination order X > Y.
     (We can ignore 1.)

   - Project this onto QQ[Y] and extract the affine polynomials in Y.

   - Convert these to vectors and consider them as constraints defining a polyhedron.

   - Compute the integral hull.

   - Convert back to polynomials and do the substitution y_i |-> b_i.
 *)
let compute_cut transform cone =

  (* 1. Expand the polynomial cone and project it onto QQ{1, y_1, ..., y_m}. *)
  let transform_polys = snd transform.rewrite_polys in
  let expanded = PolynomialCone.add_polys_to_cone cone transform_polys [] in
  (* Projection uses a graded elimination order with X > Y *)
  let projected = PolynomialCone.project expanded (fun x ->
                      let codims = Linear.const_dim :: snd transform.codomain_dims in
                      List.mem x codims) in
  let (linear_zeroes, linear_positives) =
    let f = List.filter (fun p -> QQXs.degree p <= 1) in
    ( f (Rewrite.generators (PolynomialCone.get_ideal projected))
    , f (PolynomialCone.get_cone_generators projected)) in

  L.logf ~level:`trace
    "compute_cut:
     @[zeroes: @[%a@]@]@;
     @[positives: @[%a@]@]@;"
    (pp_poly_list pp_dim) linear_zeroes
    (pp_poly_list pp_dim) linear_positives;

  (* 2. Convert to polyhedron *)
  let open PolynomialUtil in
  (* Conversion context to polyhedron.
     [linear_zeroes] and [linear_positives] are those of the expanded cone corresponding to
     [transform], so the fresh y_i's are already among them.
   *)
  let ctxt = context_of (List.concat [[QQXs.one] ; linear_zeroes; linear_positives])
  in

  L.logf ~level:`trace
    "compute_cut: conversion context for Y's is: @[%a@]@;"
    (PolyVectorContext.pp pp_dim)
    ctxt;

  let to_vector = PolyVectorConversion.poly_to_vector ctxt in
  let (linear_constraints, conic_constraints) =
    ( List.map (fun poly -> (`Zero, to_vector poly)) linear_zeroes
    , List.map (fun poly -> (`Nonneg, to_vector poly)) linear_positives ) in
  let polyhedron_to_hull =
    Polyhedron.of_constraints
      (BatList.enum (List.append linear_constraints conic_constraints)) in

  L.logf ~level:`trace "compute_cut: polyhedron to hull: @[%a@]@;
                        computing integer hull...@;"
    (Polyhedron.pp pp_dim) polyhedron_to_hull;

  (* 3. Integer hull *)
  let hull = Polyhedron.integer_hull polyhedron_to_hull in
  L.logf ~level:`trace
    "compute_cut: computed integer hull: @[%a@]@;"
    (Polyhedron.pp pp_dim) hull;

  (* 4. Substitute back *)
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
let cutting_plane_operator polynomial_cone polylattice =
  if (not (PolynomialCone.is_proper polynomial_cone)) || polylattice.affine_basis = []
  then
    (polynomial_cone, polylattice)
  else
    let (zeroes, positives) =
      ( Rewrite.generators (PolynomialCone.get_ideal polynomial_cone)
      , PolynomialCone.get_cone_generators polynomial_cone) in
    let ctxt_x = context_of (List.concat [zeroes ; positives ; polylattice.affine_basis]) in
    let tdata =
      (* Introduce fresh dimensions/variables and associated data *)
      compute_transformation polylattice.affine_basis ctxt_x in
    let (linear, conic) = compute_cut tdata polynomial_cone in
    L.logf ~level:`trace "cutting_plane_operator: Cut computed@;";
    let cut_polycone = PolynomialCone.add_polys_to_cone polynomial_cone linear conic in
    L.logf ~level:`trace "cutting_plane_operator: result: @[%a@]"
      (PolynomialCone.pp pp_dim) cut_polycone;
    let new_lattice =
      polylattice_spanned_by (PolynomialCone.get_ideal cut_polycone) polylattice.affine_basis
    in
    match new_lattice with
    | Some polylattice ->
       (cut_polycone, polylattice)
    | None ->
       let full_ring = PolynomialCone.trivial in
       (full_ring, empty_polylattice (PolynomialCone.get_ideal full_ring))

(**
   [regular_cutting_plane_closure C L] computes the smallest regular
   polynomial cone that contains C and is closed with respect to the polynomial
   lattice spanned by L (and the polynomial 1).

   Termination is guaranteed by the Hilbert Basis theorem.
 *)
let regular_cutting_plane_closure polynomial_cone lattice_polys =

  L.logf "regular_cutting_plane_closure:
          @[CP closure of: @[<v 0>%a@] @]@;
          @[  with respect to @[%a@] @]@;"
    (PolynomialCone.pp pp_dim) polynomial_cone
    (pp_poly_list pp_dim) lattice_polys;

  (* The transformation is fixed for all iterations, because the lattice is fixed
       and the cutting plane closure does not introduce new monomials.
   *)
  let num_rounds = ref 1 in
  let rec closure cone lattice =
    let (cone', lattice') = cutting_plane_operator cone lattice in
    if PolynomialCone.equal cone' cone then
      begin
        L.logf "regular_cutting_plane_closure: closure took %d rounds@;" !num_rounds;
        (cone', lattice')
      end
    else
      begin
        L.logf "regular_cutting_plane_closure: closure round %d@;" !num_rounds;
        num_rounds := !num_rounds + 1;
        closure cone' lattice'
      end
  in
  let polylattice = polylattice_spanned_by (PolynomialCone.get_ideal polynomial_cone) lattice_polys in
  let (final_cone, final_lattice) =
    match polylattice with
    | Some polylattice -> closure polynomial_cone polylattice
    | None ->
       let full_ring = PolynomialCone.trivial in
       (full_ring, empty_polylattice (PolynomialCone.get_ideal full_ring))
  in
  L.logf "regular_cutting_plane_closure: concluded, closure is:@;  @[%a@]@;"
    (PolynomialCone.pp pp_dim)
    final_cone;
  (final_cone, final_lattice)

