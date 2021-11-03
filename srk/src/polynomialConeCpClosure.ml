open Normalizffi
open Normaliz
open Flint

let ( let* ) o f =
  match o with
  | Ok x -> f x
  | Error e -> Error e

let pp_list_list fmt l =
  let p = List.iter (fun x -> Format.fprintf fmt "%s, " (Mpzf.to_string x)) in
  List.iter (fun x -> p  x; Format.fprintf fmt "\n") l

type polycone = { conic: Mpzf.t list list;
                  linear: Mpzf.t list list ;
                  cone_dim : int }

type lattice = { lattice_gens: Mpzf.t list list;
                 lattice_dim : int }

let empty_polycone = { conic = []; linear = []; cone_dim = 0 }

let empty_lattice = { lattice_gens = []; lattice_dim = 0 }

let get_conic_gens polycone = polycone.conic
let get_linear_gens polycone = polycone.linear
let get_lattice_gens lattice = lattice.lattice_gens

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

let add_conic_gens = add_vectors add_conic_gen

let add_linear_gens = add_vectors add_linear_gen

let add_lattice_gens = add_vectors add_lattice_gen

(* End duplication *)

let pp_polycone fmt cone =
  Format.fprintf fmt "Polynomial cone:\nConic generators:\n%aLinear generators: %a\n"
    pp_list_list cone.conic
    pp_list_list cone.linear

let pp_lattice fmt lattice =
  Format.fprintf fmt "Lattice generators:\n%a"
    pp_list_list lattice.lattice_gens

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

let rec zeros n : Mpzf.t list =
  assert (n >= 0);
  if n = 0 then []
  else Mpzf.of_int 0 :: zeros (n - 1)

let one n pos : Mpzf.t list =
  assert (n > 0);
  List.concat [zeros pos; [Mpzf.of_int 1]; zeros (n - pos - 1)]

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

(** Given
    (1) generators C for a cone containing some rational r in QQ, and
    (2) a basis B consisting of vectors of the form r e_i for some r in QQ
        and standard vector e_i (a monomial), for a lattice containing 1,
    such that both sets reside within some R^d,
    compute cl_{ZZ B'} (QQ C \cap QQ B),
    where B' = {e_i : r e_i in B for some r in QQ}.

    See Corollary 4.2 (or thereabouts).
    Conditions 1 and 2 are needed for integer hull computation to coincide with
    the CP-closure.
*)
let standard_cutting_plane
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
    (Format.printf "standard_cutting_plane: Intersection is:\n%a"
       pp_hom projection;
     Format.printf "Polyhedron to hull is:\n%a\n" pp_inhom dehomogenized
    )
  else ();
  Result.ok { conic = ineqs;
              linear = eqns;
              cone_dim = get_embedding_dimension (cone_ptr_of_hom transposed)
            }

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
    (lattice_basis: rational_matrix_ptr) =
  let extended_basis_ptr = extend_hnf_to_basis lattice_basis in
  let extended_basis = zz_matrix_of_matrix extended_basis_ptr in
  let transformation_ptr = matrix_inverse extended_basis_ptr in
  let (denominator, transformation) =
    zz_denom_matrix_of_rational_matrix transformation_ptr in

  if verbose then
    (Format.printf "Extended basis: %a\n" pp_list_list extended_basis;
     Format.printf "Inverse: %a\n" pp_list_list transformation)
  else
    ();

  (* Note the post-multiplication because basis vectors are arranged in rows *)
  let transform mat_ptr = matrix_multiply mat_ptr transformation_ptr in
  let inverse_transform mat_ptr = matrix_multiply mat_ptr extended_basis_ptr in
  (inverse_transform, transform, denominator)

(** Given cone generators C and a lattice basis B, both containing 1 in QQ,
    compute cl_{ZZ B}(QQ C).
*)
let cutting_plane_closure ?verbose:(verbose=false) ?asserts:(asserts=false)
    polycone lattice =
  if verbose then
    Format.printf "Computing cutting plane closure...\n"
  else
    ();
  let lattice_gens_ptr = new_matrix lattice.lattice_gens in
  let generators = zz_matrix_of_matrix lattice_gens_ptr in
  hermitize lattice_gens_ptr;
  let hermite_generators = zz_matrix_of_matrix lattice_gens_ptr in

  if verbose then
    (Format.printf "Original lattice generators: %a\n" pp_list_list generators;
     Format.printf "Hermitized lattice generators: %a\n" pp_list_list hermite_generators;
     Format.printf "Original polycone conic generators: %a\n" pp_list_list polycone.conic;
     Format.printf "Original polycone linear generators: %a\n" pp_list_list polycone.linear)
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
  let transformed_lattice = zz_matrix_of_matrix transformed_lat_gens_ptr in
  let conic_gens_ptr = new_matrix polycone.conic in
  let transformed_conic_gens_ptr = transform_dF conic_gens_ptr in
  let transformed_conic_gens = zz_matrix_of_matrix transformed_conic_gens_ptr in
  let linear_gens_ptr = new_matrix polycone.linear in
  let transformed_linear_gens_ptr = transform_dF linear_gens_ptr in
  let transformed_linear_gens = zz_matrix_of_matrix transformed_linear_gens_ptr in

  let print_transformed () =
    Format.printf "New lattice generators: %a\n" pp_list_list transformed_lattice;
    Format.printf "New conic generators: %a\n" pp_list_list transformed_conic_gens;
    Format.printf "New linear generators: %a\n" pp_list_list transformed_linear_gens in
  if verbose then
    print_transformed ()
  else ();

  let* cut_generators =
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

  let ineqs_matrix = new_matrix cut_generators.conic in
  let eqns_matrix = new_matrix cut_generators.linear in
  let target_ineqs_ptr = inv_transform_G ineqs_matrix in
  let target_eqns_ptr = inv_transform_G eqns_matrix in
  let target_ineqs = zz_matrix_of_matrix target_ineqs_ptr in
  let target_eqns = zz_matrix_of_matrix target_eqns_ptr in

  if verbose then
    (print_hull_constraints "new space" (cut_generators.conic, cut_generators.linear);
     print_hull_constraints "original space" (target_ineqs, target_eqns))
  else ();

  let* conic_generators =
    vertical_concat_matrices [polycone.conic; target_ineqs] in

  let* linear_generators =
    vertical_concat_matrices [polycone.linear; target_eqns] in

  if verbose then
    (Format.printf "Final conic generators before simplifying: %a\n" pp_list_list
       conic_generators;
     Format.printf "Final subspace generators before simplifying: %a\n" pp_list_list
       linear_generators)
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
