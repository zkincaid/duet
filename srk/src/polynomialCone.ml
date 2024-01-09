open Polynomial
open BatPervasives

include Log.Make(struct let name = "srk.polynomialCone" end)

(* Invariant: positive generators are always reduced w.r.t. zero. *)
type t =
  { zero : Rewrite.t
  ; positive : QQXs.t BatList.t }

module V = Linear.QQVector

module QQXs = Polynomial.QQXs
module PV = Polynomial.LinearQQXs

let pp pp_dim formatter pc =
  Format.fprintf
    formatter
    "@[<v 0>Zero:@;  @[<v 0>%a@]@;Positive:@;  @[<v 0>%a@]@]"
    (Rewrite.pp pp_dim) pc.zero
    (SrkUtil.pp_print_enum_nobox
       ~pp_sep:Format.pp_print_space (QQXs.pp pp_dim))
    (BatList.enum pc.positive)

let get_ideal pc = pc.zero

let make_cone zero positive =
  let positive =
    BatList.filter_map (fun p ->
        let p = Rewrite.reduce zero p in
        if QQXs.equal QQXs.zero p then None
        else Some p)
      positive
  in
  { zero; positive }

let get_cone_generators pc = pc.positive

(* Change monomial ordering of a polynomial cone. *)
let change_monomial_ordering pc order =
  make_cone (Rewrite.reorder_groebner order pc.zero) pc.positive

(* Treat a list of polynomials as a constraint representation of a polyhedral
   cone. *)
let polyhedron_of_cone cone_generators ctx =
  BatList.enum cone_generators
  /@ (fun p -> (`Nonneg, PV.densify ctx p))
  |> Polyhedron.of_constraints

(* Compute generator reprerepresentation of the cone of valid inequalities of
   a polyhedral cone, converting vectors to polynomials. *)
let cone_of_polyhedron polyhedron ctx =
  BatEnum.fold (fun cone (kind, vec) ->
      let p = PV.sparsify ctx vec in
      match kind with
      | `Zero -> (QQXs.negate p)::(p::cone)
      | `Nonneg -> p::cone
      | `Pos -> assert false)
    []
    (Polyhedron.enum_constraints polyhedron)

let regularize pc =
  let rec go pc =
    let ctx = PV.min_context (BatList.enum pc.positive) in
    let dim = PV.dim ctx in
    let linear_cone =
      Cone.make ~lines:[] ~rays:(BatList.map (PV.densify ctx) pc.positive) dim
    in
    Cone.normalize linear_cone;
    match Cone.lines linear_cone with
    | [] -> pc
    | zero' ->
      let new_zero =
        BatList.fold_left
          (fun new_zero z -> Rewrite.add_saturate new_zero z)
          pc.zero
          (List.map (PV.sparsify ctx) zero')
      in
      go (make_cone new_zero (List.map (PV.sparsify ctx) (Cone.rays linear_cone)))
  in
  go { pc with positive = QQXs.one::pc.positive }

let add_generators ?zeros ?nonnegatives pc =
  let zero_polys = match zeros with None -> [] | Some p -> p in
  let nonneg_polys = match nonnegatives with None -> [] | Some p -> p in
  let new_zero =
    BatList.fold_left
      (fun new_zero zero_poly -> Rewrite.add_saturate new_zero zero_poly)
      pc.zero
      zero_polys
  in
  make_cone new_zero (nonneg_polys @ pc.positive)


let top = { zero = Rewrite.mk_rewrite Monomial.degrevlex [QQXs.one]
          ; positive = [] }

(* Project a finitely-generated cone onto the set of monomials that satisfy
   the predicate pred *)
let project_polyhedral_cone cone_generators pred =
  let ctx = PV.min_context (BatList.enum cone_generators) in
  let elim_dims =
    (0 -- (PV.dim ctx - 1))
    |> BatEnum.filter (fun i -> not (pred (PV.dim_of_int ctx i)))
    |> BatList.of_enum
  in
  let projected_polyhedron =
    polyhedron_of_cone cone_generators ctx
    |> Polyhedron.project_dd elim_dims
  in
  cone_of_polyhedron projected_polyhedron ctx

let restrict f pc = { zero = Rewrite.restrict f pc.zero
                    ; positive = project_polyhedral_cone pc.positive f }

let monomial_over pred monomial =
  BatEnum.for_all (fun (d, _) -> pred d) (Monomial.enum monomial)

let polynomial_over pred polynomial =
  BatEnum.for_all (fun (_, m) -> monomial_over pred m) (QQXs.enum polynomial)

let project pc pred =
  let elim_order = Monomial.block [not % pred] Monomial.degrevlex in
  let pc = change_monomial_ordering pc elim_order in
  let elim m = BatEnum.for_all (pred % fst) (Monomial.enum m) in
  let projected_ideal =
    Rewrite.generators pc.zero
    |> List.filter (polynomial_over pred)
    |> Rewrite.mk_rewrite Monomial.degrevlex
  in
  { zero = projected_ideal
  ; positive = project_polyhedral_cone pc.positive elim }

let max_dim polynomials a =
  List.fold_left
    (fun m p ->
       try max m (SrkUtil.Int.Set.max_elt (QQXs.dimensions p))
       with Not_found -> m)
    a
    polynomials

let intersection pc1 pc2 =
  let i1_gen = Rewrite.generators pc1.zero in
  let i2_gen = Rewrite.generators pc2.zero in
  let fresh_var =
    1 + (max_dim i1_gen 0
         |> max_dim i2_gen
         |> max_dim pc1.positive
         |> max_dim pc2.positive)
  in
  let dims_to_elim = fun x -> x = fresh_var in
  let t = QQXs.of_dim fresh_var in
  let t' = QQXs.sub (QQXs.scalar QQ.one) t in
  let zero =
    (List.map (QQXs.mul t) i1_gen)@(List.map (QQXs.mul t') i2_gen)
    |> Rewrite.mk_rewrite (Monomial.block [dims_to_elim] Monomial.degrevlex)
    |> Rewrite.grobner_basis
  in
  let positive =
    (List.map (QQXs.mul t) pc1.positive)@(List.map (QQXs.mul t') pc2.positive)
  in
  make_cone zero positive
  |> restrict (BatEnum.for_all (fun (v, _) -> v != fresh_var) % Monomial.enum)

let inverse_homomorphism pc hom =
  let (dims, transform_polys) =
    List.fold_left (fun (dims, transforms) (y, image) ->
        ( y :: dims
        , QQXs.sub (QQXs.of_dim y) image :: transforms))
      ([], [])
      hom
  in
  let expanded = add_generators ~zeros:transform_polys pc in
  (* The constant dimension is always present in a polynomial cone and
     1 is always preserved by ring homomorphisms.
  *)
  let dims = Linear.const_dim :: dims in
  project expanded (fun x -> List.mem x dims)

let inverse_linear_map pc hom =
  let preimage = inverse_homomorphism pc hom in
  let (linear_zeros, linear_positives) =
    (* Projection uses a graded elimination order keeping Y.
       TODO: Figure out if we actually need this.
    *)
    let p =
      restrict (fun m -> Monomial.total_degree m <= 1) preimage
    in
    ( Rewrite.generators (get_ideal p)
    , get_cone_generators p) in
  (linear_zeros, linear_positives)

let to_formula srk term_of_dim pc =
  let open Syntax in
  let zero = mk_zero srk in
  let is_zero = mk_eq srk zero % QQXs.term_of srk term_of_dim in
  let is_nonneg = mk_leq srk zero % QQXs.term_of srk term_of_dim in
  mk_and srk ((List.map is_zero (Rewrite.generators pc.zero))
              @ (List.map is_nonneg pc.positive))

let mem p pc =
  let reduced = Rewrite.reduce pc.zero p in
  let ctx = PV.min_context (BatList.enum pc.positive) in
  (* Optimization: if a monomial appears in reduced but not cone_generators
     then return false immediately *)
  if BatEnum.exists (fun (_, p_mono) ->
      not (PV.mem ctx p_mono))
      (QQXs.enum reduced)
  then
    false
  else
    begin
      let vec_target_poly = PV.densify ctx reduced in
      let dim = PV.dim ctx in
      let cone =
        let rays =
          BatList.map (PV.densify ctx) pc.positive
        in
        Cone.make ~lines:[] ~rays dim
      in
      Cone.mem vec_target_poly cone
    end

let leq pc1 pc2 =
  Rewrite.subset pc1.zero pc2.zero
  && List.for_all (fun p -> mem p pc2) pc1.positive

let equal pc1 pc2 =
  Rewrite.equal pc1.zero pc2.zero
  && List.for_all (fun p -> mem p pc2) pc1.positive
  && List.for_all (fun p -> mem p pc1) pc2.positive

let is_proper pc =
  not (QQXs.equal QQXs.zero (Rewrite.reduce pc.zero QQXs.one))

let inverse_image pc map =
  let dim = Array.length map in
  (* Shift polynomials by dim dimensions, to ensure the variables 0...dim-1
     are free to use *)
  let shift =
    QQXs.substitute (fun i ->
        let i' = if i >= 0 then i + dim else i in
        QQXs.of_dim i')
  in
  (* Elimination order that is compatible with the monomial order of pc; after
     shifting pc.zero, it's still a Groebner basis w.r.t. this order. *)
  let elim_ord =
    let base_order = Rewrite.get_monomial_ordering pc.zero in
    let split m =
      BatEnum.fold (fun (t,f) (cdim, pow) ->
          if cdim >= dim then
            (Monomial.mul_term (cdim - dim) pow t, f)
          else
            (t, Monomial.mul_term cdim pow f))
        (Monomial.one, Monomial.one)
        (Monomial.enum m)
    in
    (fun m1 m2 ->
       let (m1, m1') = split m1 in
       let (m2, m2') = split m2 in
       match base_order m1 m2 with
       | `Eq -> Monomial.degrevlex m1' m2'
       | other -> other)
  in
  let shift_zero =
    Rewrite.generators pc.zero
    |> List.map shift
    |> Rewrite.mk_rewrite elim_ord
  in
  (* Augument shift_zero with { shift(map.(i)) - i : i in [0, dim) } *)
  let zero_map =
    BatArray.fold_lefti (fun ideal i p ->
        let i_monomial = Monomial.singleton i 1 in
        Rewrite.add_saturate
          ideal
          (QQXs.add_term (QQ.of_int (-1)) i_monomial (shift p)))
      shift_zero
      map
  in
  let pc_map =
    make_cone zero_map (List.map shift pc.positive)
  in
  restrict (monomial_over (fun d ->  d < dim)) pc_map
