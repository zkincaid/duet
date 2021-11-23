open Polynomial
open PolynomialUtil

module L = Log.Make(struct let name = "srk.polynomialConeCpClosure" end)

let ( let* ) o f =
  match o with
  | Ok x -> f x
  | Error e -> Error e

let rec zeros n : Mpzf.t list =
  assert (n >= 0);
  if n = 0 then []
  else Mpzf.of_int 0 :: zeros (n - 1)

let one n pos : Mpzf.t list =
  assert (n > 0);
  List.concat [zeros pos; [Mpzf.of_int 1]; zeros (n - pos - 1)]

module type PolyhedralCone = sig
  type polycone
  type lattice

  val empty_polycone : polycone

  val add_conic_gens : polycone -> Mpzf.t list list -> polycone

  (** Add QQ-linear generators (two-sided generators) to the cone *)
  val add_linear_gens : polycone -> Mpzf.t list list -> polycone

  val empty_lattice : lattice

  val add_lattice_gens : lattice -> Mpzf.t list list -> lattice

  val get_conic_gens : polycone -> Mpzf.t list list

  val get_linear_gens : polycone -> Mpzf.t list list

  (** Row-hermite normal form *)
  val get_hermitized_lattice_basis : lattice -> Mpzf.t list list

  val get_lattice_dim : lattice -> int

  val intersect_cones : polycone -> polycone -> polycone

  (** Given
      (1) generators C for a polyhedral cone containing some rational r in QQ, and
      (2) a basis B consisting of vectors of the form r e_i for some r in QQ
          and standard vector e_i (a monomial), for a lattice containing 1,
      such that both sets reside within some R^d,
      compute cl_{ZZ B'} (QQ C \cap QQ B),
      where B' = {e_i : r e_i in B for some r in QQ}.

      See Corollary 4.2 (or thereabouts).
      Conditions 1 and 2 are needed for integer hull computation to coincide with
      the CP-closure.
  *)
  val standard_cutting_plane: ?verbose:bool -> ?asserts:bool
    -> polycone -> lattice -> polycone

  (** Given polyhedral cone generators C and a lattice basis B,
      both containing 1 in QQ, compute cl_{ZZ B}(QQ C).
  *)
  val cutting_plane_closure : ?verbose:bool -> ?asserts:bool
    -> polycone -> lattice -> polycone

  val pp_polycone : Format.formatter -> polycone -> unit

  val pp_lattice : Format.formatter -> lattice -> unit

end

module PolyhedralCone : PolyhedralCone = struct
  (** Cutting plane closure of polynomial cones in polyhedral form.

    A polynomial cone C is represented by its set of (QQ-conic + QQ-linear)
    generators, given in the form of vectors of type Mpz list list.
    The components of these vectors correspond to some fixed monomial order,
    and are such that the constant term must be in the first position.

    A lattice L is likewise represented by its set of ZZ-linear generators
    given in vector form, presented according to the same monomial order
    as that for the cone, with constant terms appearing in the first position.

    Given (C, L), [cutting_plane_closure C L] computes the cutting plane closure
    of C with respect to L.
  *)

  open Normalizffi
  open Normaliz

  type polycone = { conic: Mpzf.t list list;
                    linear: Mpzf.t list list ;
                    cone_dim : int }

  type lattice = { lattice_gens: Mpzf.t list list;
                   lattice_dim : int }

  let empty_polycone = { conic = []; linear = []; cone_dim = 0 }

  let empty_lattice = { lattice_gens = []; lattice_dim = 0 }

  let get_conic_gens polycone = polycone.conic
  let get_linear_gens polycone = polycone.linear
  (* let get_lattice_gens lattice = lattice.lattice_gens *)

  let get_hermitized_lattice_basis lattice =
    let lattice_gens_ptr = Flint.new_matrix lattice.lattice_gens in
    Flint.hermitize lattice_gens_ptr;
    Flint.zz_matrix_of_matrix lattice_gens_ptr

  let get_lattice_dim lattice = lattice.lattice_dim

  (* TODO: Refactor the following code; it is currently duplicated in normaliz.ml *)

  let add_vector vectors vector: ('a list list * int, string) result =
    if vectors = [] then Result.ok ([vector], List.length vector)
    else
      let ambient_dim = List.length (List.hd vectors) in
      let dim = List.length vector in
      if ambient_dim = dim then
        Result.ok ((vector :: vectors), dim)
      else
        let error_str =
          Format.sprintf "Trying to add vector of length %d to vectors of length %d"
            dim ambient_dim in
        Result.error error_str

  let add_vector_to_cone get set cone vec =
    let* (matrix, dim) = add_vector (get cone) vec in
    if cone.cone_dim = 0 || cone.cone_dim = dim then
      Result.ok { (set cone matrix) with cone_dim = dim }
    else
      let error_str =
        Format.sprintf "Trying to add vector of length %d to polynomial cone with ambient dimension %d"
          dim cone.cone_dim in
      Result.error error_str

  let add_conic_gen cone vec =
    add_vector_to_cone
      (fun cone -> cone.conic)
      (fun cone matrix -> { cone with conic = matrix })
      cone vec

  let add_linear_gen cone vec =
    add_vector_to_cone
      (fun cone -> cone.linear)
      (fun cone matrix -> { cone with linear = matrix })
      cone vec

  let add_lattice_gen lattice vec =
    let* (matrix, dim) = add_vector lattice.lattice_gens vec in
    if lattice.lattice_dim = 0 || lattice.lattice_dim = dim then
      Result.ok { { lattice with lattice_gens = matrix } with lattice_dim = dim}
    else
      let error_str =
        Format.sprintf "Trying to add vector of length %d to polynomial lattice with ambient dimension %d"
          dim lattice.lattice_dim in
      Result.error error_str

  let add_vectors add obj vecs  =
    List.fold_right
      (fun vec obj_opt ->
         let* obj' = obj_opt in
         add obj' vec)
      vecs (Result.ok obj)

  let add_conic_gens polycone generator =
    Result.get_ok (add_vectors add_conic_gen polycone generator)

  let add_linear_gens polycone generator =
    Result.get_ok (add_vectors add_linear_gen polycone generator)

  let add_lattice_gens polycone generator =
    Result.get_ok (add_vectors add_lattice_gen polycone generator)

  (* End duplication *)

  let pp_polycone fmt cone =
    Format.fprintf fmt
      "@[Polynomial cone:@;@[Conic generators:@; @[%a@]@]@;@[Linear generators:@;@[%a@]@]@]"
      PrettyPrintPoly.pp_zz_list cone.conic
      PrettyPrintPoly.pp_zz_list cone.linear

  let pp_lattice fmt lattice =
    Format.fprintf fmt "Lattice generators:@ @[%a@]"
      PrettyPrintPoly.pp_zz_list lattice.lattice_gens

  let is_scaled_monomial v =
    let (_zeroes, nonzeroes) =
      List.fold_left (fun (zeroes, nonzeroes) e ->
          if e = Mpzf.of_int 0 then (zeroes + 1, nonzeroes)
          else (zeroes, nonzeroes + 1)) (0, 0) v in
    (nonzeroes = 1)

  let is_scaled_monomial_lattice lattice =
    List.for_all is_scaled_monomial lattice.lattice_gens

  (*
  let negate_vectors ll =
    List.map (fun l -> List.map (fun x -> Mpzf.neg x) l) ll
  *)

  let vertical_concat_matrices (matrix_list : 'a list list list) =
    let adjoin_row row mat_opt =
      let* mat = mat_opt in
      if mat = [] then
        Result.ok [row]
      else
        let (row_len, matrix_dim) = (List.length row, List.length (List.hd mat)) in
        if row_len = matrix_dim then
          Result.ok (row :: mat)
        else
          let error_str =
            Format.sprintf "Concatenation: Trying to add vector of length %d to vectors of length %d"
              row_len matrix_dim in
          Result.error error_str in
    let adjoin_matrix mat mat_opt =
      List.fold_right adjoin_row mat mat_opt in
    List.fold_right adjoin_matrix matrix_list (Result.ok [])

  let intersect_cones polycone1 polycone2 =
    let cone1 = Result.get_ok (add_rays empty_cone polycone1.conic) in
    let cone1 = Result.get_ok (add_equalities cone1 polycone1.linear) in
    let cone2 = Result.get_ok (add_rays empty_cone polycone2.conic) in
    let cone2 = Result.get_ok (add_equalities cone2 polycone2.linear) in
    let cone_ptr1 = new_cone cone1 in
    let cone_ptr2 = new_cone cone2 in
    let projection = Result.get_ok (intersect_cone cone_ptr1 cone_ptr2) in
    let cone_ptr = cone_ptr_of_hom projection in
    { conic = get_extreme_rays cone_ptr
    ; linear = get_lineality_space cone_ptr
    ; cone_dim = get_embedding_dimension cone_ptr
    }

  (** Given
      (1) generators C for a polyhedral cone containing some rational r in QQ, and
      (2) a basis B consisting of vectors of the form r e_i for some r in QQ
          and standard vector e_i (a monomial), for a lattice containing 1,
      such that both sets reside within some R^d,
      compute cl_{ZZ B'} (QQ C \cap QQ B),
      where B' = {e_i : r e_i in B for some r in QQ}.

      See Corollary 4.2 (or thereabouts).
      Conditions 1 and 2 are needed for integer hull computation to coincide with
      the CP-closure.
  *)
  let standard_cutting_plane_
      ?verbose:(verbose=false)
      ?asserts:(asserts=false)
      polycone lattice =
    let* cone = add_rays empty_cone polycone.conic in
    let* cone = add_equalities cone polycone.linear in
    let* lat =
      (* let* gens = vertical_concat_matrices [monomial_lattice_generators;
                                            negate_vectors monomial_lattice_generators]
         in *)
      add_subspace_generators empty_cone lattice.lattice_gens in
    let cone_ptr = new_cone cone in
    let lattice_ptr = new_cone lat in
    let* projection = intersect_cone cone_ptr lattice_ptr in
    let* () =
      if asserts then
        if (not (is_scaled_monomial_lattice lattice)) then
          Result.error "standard_cutting_plane: lattice generators must be standard vectors"
        else if (polycone.cone_dim = 0 || lattice.lattice_dim = 0) then
          Result.error "standard_cutting_plane: dimensions must be positive"
        else if polycone.cone_dim <> lattice.lattice_dim then
          Result.error "standard_cutting_plane: dimensions of cone and lattice must match"
        else
          let dim = get_embedding_dimension (cone_ptr_of_hom projection) in
          let one = one dim 0 in
          let* one_in_cone = contains cone_ptr one in
          let* one_in_lattice = contains lattice_ptr one in
          if not (one_in_cone && one_in_lattice) then
            Result.error "Both cone and lattice should contain 1"
          else
            Result.ok ()
      else Result.ok () in
    let transposed = generators_to_constraints projection in
    let dehomogenized = dehomogenize transposed in
    let () = hull dehomogenized in
    let ineqs = get_int_hull_inequalities dehomogenized in
    let eqns = get_int_hull_equations dehomogenized in
    (* This is for Lemma 4.3 rather than Corollary 4.2, and we don't actually
       need to implement the former; see proof in [cutting_plane_closure].

       let* final_cone = add_rays empty_cone ineqs in
       let* final_cone = add_rays final_cone cone_generators in
       let* final_cone = add_subspace_generators final_cone eqns in
       let final_cone_ptr = new_cone final_cone in
       let rays = get_extreme_rays (cone_ptr_of_hom final_cone_ptr) in
       let lineality = get_lineality_space (cone_ptr_of_hom final_cone_ptr) in
       Result.ok { conic = rays;
                linear = lineality }
    *)
    if verbose then
      (L.logf "standard_cutting_plane: Intersection is:\n%a"
         pp_hom projection;
       L.logf "Polyhedron to hull is:\n%a\n" pp_inhom dehomogenized
      )
    else ();
    Result.ok { conic = ineqs;
                linear = eqns;
                cone_dim = get_embedding_dimension (cone_ptr_of_hom transposed)
              }

  let standard_cutting_plane
      ?verbose:(verbose=false)
      ?asserts:(asserts=false)
      polycone lattice =
    Result.get_ok (standard_cutting_plane_ ~verbose ~asserts polycone lattice)

  (** Given a lattice basis B \in ZZ^{m x n} in row Hermite Normal Form
      (not necessarily full rank), return a tuple (G, F, d), where
      - d is an integer (representing a denominator)
      - F is a linear map from R^n containing QQ B to R^l, where l is the rank of B.
        Moreover, F maps the rows {b_1, b_2, ...} of B to {d e_i: 1 <= i <= l}
        (preserving order of the indices), where e_i is the standard vector with
        1 in the i-th position and 0 everywhere else.
      - G is linear map from R^l to R^d such that G is the inverse of 1/d F.

      See Lemma 4.4 (or thereabouts).
  *)

  let get_transformation_matrices ?verbose:(verbose=false)
      (lattice_basis: Flint.rational_matrix_ptr) =
    let extended_basis_ptr = Flint.extend_hnf_to_basis lattice_basis in
    let extended_basis = Flint.zz_matrix_of_matrix extended_basis_ptr in
    let transformation_ptr = Flint.matrix_inverse extended_basis_ptr in
    let (denominator, transformation) =
      Flint.zz_denom_matrix_of_rational_matrix transformation_ptr in

    if verbose then
      (Format.printf "@[Extended basis: %a@]@;" PrettyPrintPoly.pp_zz_list extended_basis;
       Format.printf "@[Inverse: %a@]@;" PrettyPrintPoly.pp_zz_list transformation)
    else
      ();

    (* Note the post-multiplication because basis vectors are arranged in rows *)
    let transform mat_ptr = Flint.matrix_multiply mat_ptr transformation_ptr in
    let inverse_transform mat_ptr = Flint.matrix_multiply mat_ptr extended_basis_ptr in
    (inverse_transform, transform, denominator)

  (** Given polyhedral cone generators C and a lattice basis B,
      both containing 1 in QQ, compute cl_{ZZ B}(QQ C).
  *)
  let cutting_plane_closure_ ?verbose:(verbose=false) ?asserts:(asserts=false)
      polycone lattice =
    if verbose then
      Format.printf "Computing cutting plane closure...\n"
    else
      ();
    let lattice_gens_ptr = Flint.new_matrix lattice.lattice_gens in
    let generators = Flint.zz_matrix_of_matrix lattice_gens_ptr in
    let hermite_generators = get_hermitized_lattice_basis lattice in

    if verbose then
      (Format.printf "@[Original lattice generators: %a@]@;"
         PrettyPrintPoly.pp_zz_list generators;
       Format.printf "@[Hermitized lattice generators: %a@]@;"
         PrettyPrintPoly.pp_zz_list hermite_generators;
       Format.printf "@[Original polycone conic generators: %a@]@;"
         PrettyPrintPoly.pp_zz_list polycone.conic;
       Format.printf "@[Original polycone linear generators: %a@]@;"
         PrettyPrintPoly.pp_zz_list polycone.linear)
    else
      ();

    let* () =
      if asserts then
        if (polycone.cone_dim = 0 || lattice.lattice_dim = 0
            || polycone.cone_dim <> lattice.lattice_dim) then
          Result.error "cutting_plane_closure: dimensions of polynomial cone and lattice must be positive and equal"
        else
          let is_one v = (v = one polycone.cone_dim 0) in
          if not (List.exists is_one polycone.conic) && not (List.exists is_one polycone.linear) then
            Result.error "cutting_plane_closure: 1 is not in polynomial cone"
          else if not (List.exists is_one lattice.lattice_gens) then
            Result.error "cutting_plane_closure: 1 is not in lattice"
          else
            Result.ok ()
      else
        Result.ok ()
    in

    let (inv_transform_G, transform_dF, _denom_d) =
      get_transformation_matrices lattice_gens_ptr in
    (* Since we are operating in row form, changing the basis is by post-multiplying.
       Also, we disregard the denominator in the transformation.

       Proof: Let F be the transformation we should apply (taking denominator d
       into account), so dF is the transformation (transform_dF)
       we are applying here.

       Let B and C be the basis for the lattice and generators for the cone
       respectively.
       We are computing:

       cl_{ZZ B}(QQ C) = F^{-1}(F(cl_{ZZ B} (QQ C)))
                       = F^{-1} cl_{ZZ F(B)} (QQ F(C))
                       = F^{-1} QQ (QQ F(C) \cup cl_{ZZ F(B)} (QQ F(C) \cap QQ F(B)))
                       = F^{-1} QQ (QQ F(C) \cup cl_{ZZ F(B)} (QQ dF(C) \cap QQ dF(B)))
                       = QQ (C \cup F^{-1} (cl_{ZZ F(B)} (QQ dF(C) \cap QQ dF(B))))
                       = QQ (C \cup d F^{-1} (cl_{ZZ F(B)} (QQ dF(C) \cap QQ dF(B)))).

       dF(B) = { d e_i: 1 <= i <= l ], where l is the number of vectors in B.

       So we can stick with dF and use [standard_cutting_plane] to compute
       cl_{ZZ F(B)}(QQ dF(C) \cap QQ dF(B)).
       Then we can apply d F^{-1} =  (the extended basis matrix) to this set and
       add C to give us the set of generators for cl_{ZZ B}(QQ C).

       See Theorem 4.5 (or thereabouts).
    *)

    let transformed_lat_gens_ptr = transform_dF lattice_gens_ptr in
    let transformed_lattice = Flint.zz_matrix_of_matrix transformed_lat_gens_ptr in
    let conic_gens_ptr = Flint.new_matrix polycone.conic in
    let transformed_conic_gens_ptr = transform_dF conic_gens_ptr in
    let transformed_conic_gens = Flint.zz_matrix_of_matrix transformed_conic_gens_ptr in
    let linear_gens_ptr = Flint.new_matrix polycone.linear in
    let transformed_linear_gens_ptr = transform_dF linear_gens_ptr in
    let transformed_linear_gens = Flint.zz_matrix_of_matrix transformed_linear_gens_ptr in

    let print_transformed () =
      L.logf "@[New lattice generators: %a@]@;"
        PrettyPrintPoly.pp_zz_list transformed_lattice;
      L.logf "@[New conic generators: %a@]@;"
        PrettyPrintPoly.pp_zz_list transformed_conic_gens;
      L.logf "@[New linear generators: %a@]@;"
        PrettyPrintPoly.pp_zz_list transformed_linear_gens in
    if verbose then
      print_transformed ()
    else ();

    let cut_generators =
      let dim =
        if transformed_conic_gens <> [] then
          List.length (List.hd transformed_conic_gens)
        else List.length (List.hd transformed_linear_gens) in
      standard_cutting_plane ~verbose:verbose ~asserts:asserts
        { conic = transformed_conic_gens;
          linear = transformed_linear_gens;
          cone_dim = dim }
        { lattice_gens = transformed_lattice;
          lattice_dim = List.length (List.hd transformed_lattice) }
    in

    let ineqs_matrix = Flint.new_matrix cut_generators.conic in
    let eqns_matrix = Flint.new_matrix cut_generators.linear in
    let target_ineqs_ptr = inv_transform_G ineqs_matrix in
    let target_eqns_ptr = inv_transform_G eqns_matrix in
    let target_ineqs = Flint.zz_matrix_of_matrix target_ineqs_ptr in
    let target_eqns = Flint.zz_matrix_of_matrix target_eqns_ptr in

    if verbose then
      (print_hull_constraints "new space" (cut_generators.conic, cut_generators.linear);
       print_hull_constraints "original space" (target_ineqs, target_eqns))
    else ();

    let* conic_generators =
      vertical_concat_matrices [polycone.conic; target_ineqs] in

    let* linear_generators =
      vertical_concat_matrices [polycone.linear; target_eqns] in

    if verbose then
      (L.logf "@[Final conic generators before simplifying: %a@]@;"
         PrettyPrintPoly.pp_zz_list conic_generators;
       L.logf "@[Final subspace generators before simplifying: %a@]@;"
         PrettyPrintPoly.pp_zz_list linear_generators)
    else ();

    let* final_cone = add_rays empty_cone conic_generators in
    let* final_cone = add_subspace_generators final_cone target_eqns in
    let final_cone_ptr = new_cone final_cone in
    let rays = get_extreme_rays (cone_ptr_of_hom final_cone_ptr) in
    let lineality = get_lineality_space (cone_ptr_of_hom final_cone_ptr) in
    Result.ok { conic = rays;
                linear = lineality;
                cone_dim = polycone.cone_dim
              }

  let cutting_plane_closure ?verbose:(verbose=false) ?asserts:(asserts=false)
      polycone lattice =
    Result.get_ok (cutting_plane_closure_ ~verbose ~asserts polycone lattice)

end

(** The polynomial 1 with the other basis polynomials *)
type lattice = QQXs.t * QQXs.t list

(*
let print_polys pp_dim =
  Format.pp_print_list
    ~pp_sep:(fun fmt _unit -> Format.fprintf fmt ",@ ")
    (QQXs.pp pp_dim)
*)

let pp pp_dim fmt lattice =
  Format.fprintf fmt "@[(@[%a@], @[%a@])@]" (QQXs.pp pp_dim) (fst lattice)
    (PrettyPrintPoly.pp_poly_list pp_dim) (snd lattice)

let clear_denoms mpqf_list =
  let pairs = List.map Mpqf.to_mpzf2 mpqf_list in
  let max_denom = List.fold_left
      (fun curr_max curr_pair ->
         if Mpzf.cmp (snd curr_pair) curr_max > 0 then snd curr_pair else curr_max)
      (Mpzf.of_int 0) pairs in
  List.map (fun r -> fst (Mpqf.to_mpzf2 (Mpqf.mul r (Mpqf.of_mpz max_denom)))) mpqf_list

let vectorize_and_add ctxt add_kind base polys =
  add_kind base
    (List.map
       (fun p -> clear_denoms (PolyVectorConversion.rational_poly_to_scalars ctxt p))
       polys)

let vector_to_poly ctxt v =
  PolyVectorConversion.scalars_to_rational_poly ctxt (List.map Mpqf.of_mpz v)

module MonomialSet = BatSet.Make(Monomial)

let monomials_in p =
  BatEnum.fold (fun s (_scalar, monomial) -> MonomialSet.add monomial s)
    MonomialSet.empty (QQXs.enum p)

let all_monomials_in ps =
  List.fold_left (fun s p -> MonomialSet.union s (monomials_in p)) MonomialSet.empty ps

let context_of_monomials monomials =
  PolyVectorContext.context Monomial.degrevlex monomials

let build_context polys =
  let monomials = all_monomials_in polys in
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
  context_of_monomials (MonomialSet.to_list monomials)

(** Compute basis for the lattice *)
let lattice_spanned_by polys : lattice =
  let polys = QQXs.one :: polys in
  let monomials = MonomialSet.to_list (all_monomials_in polys) in
  let ctxt = PolyVectorContext.context Monomial.degrevlex monomials in
  (* TODO: Verify that ctxt has the monomial 1 in position 0. *)
  let open PolyVectorConversion in
  let open PolyhedralCone in
  let polyvectors = List.map (fun poly -> clear_denoms (rational_poly_to_scalars ctxt poly))
      polys in
  let lattice = add_lattice_gens empty_lattice polyvectors in
  let basis = get_hermitized_lattice_basis lattice in
  (* Is this necessary? *)
  let (one, others) =
    let equal_vec l1 l2 =
      List.for_all2 (fun a b -> Mpqf.equal (Mpqf.of_mpz a) (Mpqf.of_mpz b)) l1 l2 in
    List.partition
      (fun v -> equal_vec v (one (get_lattice_dim lattice) 0))
      basis in
  assert (List.length one = 1);
  (List.hd (List.map (vector_to_poly ctxt) one), List.map (vector_to_poly ctxt) others)

(*
type transformation_data =
  { groebner_basis: Rewrite.t
  (* { y_i - b_i }, where each b_i is in the lattice and y_i is fresh *)
  ; substitution: Monomial.dim -> QQXs.t
  (* \y_dim. y_dim -> b *)
  ; codomain_one: Monomial.dim
  (* monomial in the codomain that corresponds to 1 in the domain *)
  ; codomain_rest: Monomial.dim list
  (* { y_i } except 1  *)
  }
*)

type transformation_data =
  { rewrite_polys: QQXs.t list
  (* { y_i - b_i }, where each b_i is in the lattice and y_i is fresh *)
  ; substitution: Monomial.dim -> QQXs.t
  (* \y_dim. y_dim -> b *)
  ; codomain_one: Monomial.dim
  (* monomial in the codomain that corresponds to 1 in the domain; 
     also the smallest fresh variable/dimension introduced
  *)
  ; codomain_rest: Monomial.dim list
  (* { y_i } except 1  *)
  }

let pp_transformation_data pp_dim fmt transformation_data =
  Format.fprintf fmt "Transformation data:@;@[Rewrites: %a@]@;@[codomain_one: %a@]@;@[codomain_rest:%a@]@;"
    (PrettyPrintPoly.pp_poly_list (PrettyPrintDim.pp_numeric "x")) transformation_data.rewrite_polys
    pp_dim transformation_data.codomain_one
    (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_dim)
    transformation_data.codomain_rest

let monomial_to_polynomial mono = QQXs.add_term QQ.one mono QQXs.zero


(** Given a lattice containing 1, compute a Groebner basis that essentially 
    implements a linear map sending the lattice to a standard lattice over the 
    affine space spanned by a set of fresh variables.
    The input is the lattice itself and a set of monomials that fresh variables
    should be distinct from.

   This implements Lemma 6.4 (or thereabouts).
*)
let compute_transformation ?verbose:(verbose=false) lattice monomials : transformation_data =
  let lattice1 = fst lattice :: snd lattice in
  let ctxt = context_of_monomials
      (List.concat [MonomialSet.to_list (all_monomials_in lattice1); monomials]) in

  if verbose then
    L.logf "compute_transformation: transformation context: %a\n"
      (PolyVectorContext.pp (PrettyPrintDim.pp_numeric "x"))
      ctxt
  else ();

  let fresh_start = Option.value ~default:0 (PolyVectorContext.max_dimension ctxt) + 1 in
  if verbose then
    L.logf "compute_transformation: fresh variables range from %d to %d\n"
      fresh_start (fresh_start + List.length lattice1 - 1)
  else ();

  let (ones, codomain_rest, substitution, transformation_polys) =
    (* { y_i - b_i } *)
    BatList.fold_lefti (fun (ones, monos, substitution, transform) dim poly ->
        let fresh = dim + fresh_start in
        let fresh_var = Monomial.singleton fresh 1 in
        let transformation_poly = (QQXs.sub (monomial_to_polynomial fresh_var) poly) in
        let is_one = if QQXs.equal poly QQXs.one then true else false in
        ( (if is_one then SrkUtil.Int.Set.add fresh ones else ones)
        , (if is_one then monos else fresh :: monos)
        , (fun i -> if i = dim + fresh_start then poly else substitution i)
        , transformation_poly :: transform))
      (SrkUtil.Int.Set.empty, [], (fun _ -> QQXs.zero), []) lattice1 in
  assert (SrkUtil.Int.Set.cardinal ones = 1);
  (* let transformation_ideal' = List.fold_left Rewrite.add_saturate ideal transformation_polys in
  let elim_order =
    (* *)
    Monomial.block [fun dim -> dim <= fresh_start]
      Monomial.degrevlex in *)
  let data =
    { rewrite_polys = transformation_polys
      (* groebner_basis = Rewrite.reduce_rewrite
          (Rewrite.reorder_groebner elim_order transformation_ideal') *)
    ; substitution = substitution
    ; codomain_one = List.hd (SrkUtil.Int.Set.to_list ones)
    (* TODO: We should be able to assume that only the first fresh variable
       corresponds to 1, since we control where 1 is in the input lattice. *)
    ; codomain_rest = codomain_rest
    }
  in
  if verbose then
    L.logf "@[compute_transformation: %a@]"
      (pp_transformation_data (PrettyPrintDim.pp_numeric "x")) data
  else
    ();
  data

(** Apply the linear map that sends the input lattice to the standard lattice,
    to the input polynomial cone.
*)
let rewrite_with_linear_map ?verbose:(verbose=false) lattice polynomial_cone =
  let ideal = PolynomialCone.get_ideal polynomial_cone in
  let positives = PolynomialCone.get_cone_generators polynomial_cone in
  let polycone_polys = List.concat [Rewrite.generators ideal; positives] in

  (* 1. Compute linear map *)
  let transform = compute_transformation ~verbose lattice
      (MonomialSet.to_list (all_monomials_in polycone_polys)) in
  let elim_order =
    (* order must have original x > fresh y's and be graded on y's. *)
    Monomial.block [fun dim -> dim < transform.codomain_one]
      Monomial.degrevlex in
  let transformation_ideal = List.fold_left Rewrite.add_saturate ideal
      transform.rewrite_polys in
  let groebner_basis =
    Rewrite.reduce_rewrite
      (Rewrite.reorder_groebner elim_order transformation_ideal) in
  let transformed_positives = List.map (Rewrite.reduce groebner_basis) positives in
  if verbose then
    L.logf "@[rewrite_with_linear_map:@;GB:@ %a@;positives: %a@]"
      (PrettyPrintPoly.pp_poly_list (PrettyPrintDim.pp_numeric "x"))
      (Rewrite.generators groebner_basis)
      (PrettyPrintPoly.pp_poly_list (PrettyPrintDim.pp_numeric "x"))
      transformed_positives
  else
    ();

  (* 2. Intersect polyhedra generated by GB and positives *)
  let lattice1 = fst lattice :: snd lattice in    
  let intersection_ctxt =
    (* TODO: Extend context API to have incremental extension rather than computing from scratch *)
    (* This context does not have to respect the dimension choices for the fresh
       (codomain) monomials made earlier; those were for polynomial operations,
       and the one here is for polyhedral operations.
    *)
    build_context (List.concat
                     [lattice1;
                      Rewrite.generators groebner_basis;
                      transformed_positives])
  in
  (* Compute QQys, the linear space spanned by the fresh variables ys. *)
  let codomain =
    let monomials = List.map monomial_to_polynomial
        (List.map (fun dim -> Monomial.singleton dim 1)
           (transform.codomain_one :: transform.codomain_rest)) in
    vectorize_and_add intersection_ctxt
      PolyhedralCone.add_linear_gens PolyhedralCone.empty_polycone
      monomials in
  let polyhedral_cone =
    let c1 =
      vectorize_and_add intersection_ctxt
        PolyhedralCone.add_linear_gens PolyhedralCone.empty_polycone
        (Rewrite.generators groebner_basis) in
    let c2 =
      vectorize_and_add intersection_ctxt
        PolyhedralCone.add_conic_gens c1
        transformed_positives in
    c2
  in
  let projected_polycone = PolyhedralCone.intersect_cones
      polyhedral_cone codomain in
  let pre_substitution_linear = PolyhedralCone.get_linear_gens projected_polycone in
  let pre_substitution_conic = PolyhedralCone.get_conic_gens projected_polycone in
  let pre_substitution_zeros =
    List.map (vector_to_poly intersection_ctxt) pre_substitution_linear in

  let pre_substitution_positives =
    List.map (vector_to_poly intersection_ctxt) pre_substitution_conic in

  if verbose then
    (L.logf "cutting_plane_closure: @[intersection context: %a@]"
       (PolyVectorContext.pp (PrettyPrintDim.pp_numeric "x")) intersection_ctxt;
     L.logf "cutting_plane_closure: @[codomain:@;@[%a@]@]"
       PolyhedralCone.pp_polycone codomain;
     L.logf "cutting_plane_closure: @[zeros before intersection:@;@[%a@]@]@;"
       (PrettyPrintPoly.pp_poly_list (PrettyPrintDim.pp_numeric "x"))
       (Rewrite.generators groebner_basis);
     L.logf "cutting_plane_closure: @[positive polynomials before intersection:@;@[%a@]@]@;"
       (PrettyPrintPoly.pp_poly_list (PrettyPrintDim.pp_numeric "x")) transformed_positives;
     L.logf "cutting_plane_closure: @[polyhedral cone before intersection:@;@[%a@]@]@;"
       PolyhedralCone.pp_polycone polyhedral_cone;
     L.logf "cutting_plane_closure: @[polyhedral cone after intersection:@ %a@]@;"
       PolyhedralCone.pp_polycone projected_polycone;
     L.logf "cutting_plane_closure: @[zeros after intersection:@ %a@]@;"
       (PrettyPrintPoly.pp_poly_list (PrettyPrintDim.pp_numeric "x"))
       pre_substitution_zeros;
     L.logf "cutting_plane_closure: @[positives after intersection:@ %a@]@;"
       (PrettyPrintPoly.pp_poly_list (PrettyPrintDim.pp_numeric "x"))
       pre_substitution_positives;
    )
  else ();

  (* 3. Resubstitute 1 into the monomial y0 corresponding to 1.
        We can't apply standard cutting plane directly because these vectors
        are in the vector space spanned by all monomials, not just the fresh ys;
        in particular, y0 and 1 are different dimensions.
     
        TODO: Maybe optimize this by reordering coordinates within vectors 
        so that the cut that comes later can be done immediately instead of 
        converting to polynomials and back. This may be a trade-off between 
        doing cutting plane in a higher dimensional ambient space (with lower 
        intrinsic dimension) vs. polynomial-vector conversions.
  *)
  let resubstitute poly =
    (* TODO: See if there is a more efficient way to do this substitution. *)
    let mono = Monomial.singleton transform.codomain_one 1 in
    let coeff = QQXs.coeff mono poly in
    let poly' = QQXs.sub poly (QQXs.add_term coeff mono QQXs.zero) in
    QQXs.add poly' (QQXs.scalar coeff) in
  let resubstituted_zeros = List.map resubstitute pre_substitution_zeros in
  let resubstituted_positives = List.map resubstitute pre_substitution_positives in
  (transform, resubstituted_zeros, resubstituted_positives)

(** Lemma 6.10 (or thereabouts) *)  
let cutting_plane_closure ?verbose:(verbose=false) lattice polynomial_cone =
  if verbose then
    L.logf "cutting_plane_closure: @[pcone to cut:@; @[%a@]@]@;@[wrt lattice:@; @[%a@]@]"
      (PolynomialCone.pp (PrettyPrintDim.pp_numeric "x")) polynomial_cone
      (pp (PrettyPrintDim.pp_numeric "x")) lattice
  else ();

  (* 1. Apply the linear map that sends the lattice to the standard lattice
        to the polynomial cone.
  *)
  let (transform, transformed_zeros, transformed_positives) =
    rewrite_with_linear_map ~verbose lattice polynomial_cone in
  let lattice1 = fst lattice :: snd lattice in

  (* Transform back into polyhedral vectors, now in dimensions y1, y2, ...,
     i.e., spanned by the fresh variables except for the one corresponding to 1.
  *)
  let cutting_plane_ctxt =
    (* TODO: Verify that codomain_one is mapped to position 0 *)
    let mono_of m = Monomial.singleton m 1 in
    build_context
      (QQXs.one
       :: List.map (fun m -> monomial_to_polynomial (mono_of m)) transform.codomain_rest) in
  let cone_to_cut =
    let c1 = vectorize_and_add cutting_plane_ctxt
        PolyhedralCone.add_linear_gens PolyhedralCone.empty_polycone transformed_zeros in
    let c2 = vectorize_and_add cutting_plane_ctxt
        PolyhedralCone.add_conic_gens c1 transformed_positives in
    c2
  in
  let polyhedral_lattice =
    vectorize_and_add cutting_plane_ctxt
      PolyhedralCone.add_lattice_gens PolyhedralCone.empty_lattice
      lattice1 in

  (* 3. Do cutting plane closure in standard lattice, i.e., Corollary 4.2 (or thereabouts) *)
  let polyhedral_closure = PolyhedralCone.standard_cutting_plane cone_to_cut polyhedral_lattice in

  (* 4. Now resubstitute all ys back into the lattice vectors *)
  let positive_polys = List.map (vector_to_poly cutting_plane_ctxt)
      (PolyhedralCone.get_conic_gens polyhedral_closure) in
  let ideal_polys = List.map (vector_to_poly cutting_plane_ctxt)
      (PolyhedralCone.get_linear_gens polyhedral_closure) in
  let cp_positives = List.map (QQXs.substitute transform.substitution) positive_polys in
  let cp_ideal = List.map (QQXs.substitute transform.substitution) ideal_polys in
  PolynomialCone.add_polys_to_cone
    PolynomialCone.empty
    (* The original ideal is unchanged *)
    (Rewrite.generators (PolynomialCone.get_ideal polynomial_cone))
    (* Polyhedral closure is added to the positives *)
    (List.concat [cp_positives; cp_ideal; List.map QQXs.negate cp_ideal])
