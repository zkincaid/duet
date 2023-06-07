open BatEnum.Infix
module P = Polyhedron
module L = IntLattice
module V = Linear.QQVector
module LM = Linear.MakeLinearMap(QQ)(SrkUtil.Int)(V)(V)

module IntSet = SrkUtil.Int.Set

include Log.Make(struct let name = "srk.abstractLia" end)

(** Abstract domain that supports symbolic abstraction *)
module type AbstractDomain = sig
  type t
  type context
  val context : context Syntax.context

  val bottom : t
  val join : t -> t -> t
  val concretize : t -> context Syntax.formula
  val abstract : context Syntax.formula -> context Interpretation.interpretation -> t

  val pp : Format.formatter -> t -> unit

end

module type Target = sig

  type context
  val context : context Syntax.context

  (** Symbols that the input formula is in *)
  val formula_symbols : Syntax.Symbol.Set.t

  (** Constraints of the integer hull are to be linear in these terms *)
  val terms : context Syntax.arith_term BatArray.t

end

(** Convert between implicants over [Target.formula_symbols] and
    constraints in some vector space, and between interpretations of the implicant
    and valuations of vectors in the vector space.
    [Target.terms] are mapped to the lowest dimensions in this vector space,
    and other symbols of the implicant are mapped to higher dimensions.

    - [valuation(interp)(i) = interp(Target.terms[i])]
 *)
module ImplicantConstraintConversion (Target : Target) : sig

  val dimensions_to_eliminate : int list

  val ambient_dimension : int

  val valuation : Target.context Interpretation.interpretation -> int -> Q.t

  val constraints_of_implicant :
    Target.context Syntax.formula list ->
    ([> `Nonneg | `Zero ] * V.t) list * V.t list

  val implicant_of_polyhedral_constraints :
    ([< `Nonneg | `Pos | `Zero ] * V.t) BatEnum.t -> Target.context Syntax.formula list

  val implicant_of_int_constraints :
    V.t BatEnum.t -> Target.context Syntax.formula list

end = struct

  let (basis, map_to_fresh_dims) =
    let open Syntax in
    let basis = BatDynArray.create () in
    let map =
      let neg_one = V.of_term QQ.one Linear.const_dim in
      BatArray.fold_lefti (fun map i t ->
          let vec = Linear.linterm_of Target.context t in
          BatDynArray.add basis vec;
          LM.may_add vec (V.of_term QQ.one i) map)
        (LM.add_exn neg_one neg_one LM.empty)
        Target.terms
      |> Symbol.Set.fold (fun symbol map ->
             if (Syntax.typ_symbol Target.context symbol <> `TyInt) then
               logf ~level:`always "Warning: Formula contains non-integer symbol %a; treating it as integer type"
                 (Syntax.pp_symbol Target.context) symbol
             else ();
             let symbol_vec = V.of_term QQ.one (Linear.dim_of_sym symbol) in
             let ambient_dim = BatDynArray.length basis in
             match LM.add symbol_vec (V.of_term QQ.one ambient_dim) map with
             | Some map' ->
                BatDynArray.add basis symbol_vec;
                map'
             | None -> map
           )
           Target.formula_symbols
    in (basis, map)

  let ambient_dimension = BatDynArray.length basis

  let dimensions_to_eliminate =
    let dim = Array.length Target.terms in
    BatList.of_enum (dim --^ ambient_dimension)

  let valuation interp i =
    Linear.evaluate_linterm
      (Interpretation.real interp)
      (BatDynArray.get basis i)

  let term_of_vector v =
    Linear.term_of_vec Target.context
      (fun i -> if i = Linear.const_dim then Syntax.mk_real Target.context QQ.one
                else Target.terms.(i)) v

  let atom_of_polyhedral_constraint (ckind, vector) =
    let zero = Syntax.mk_zero Target.context in
    let term = term_of_vector vector in
    let mk_compare cmp term = Syntax.mk_compare cmp Target.context zero term in
    match ckind with
    | `Zero -> mk_compare `Eq term
    | `Nonneg -> mk_compare `Leq term
    | `Pos -> mk_compare `Lt term

  let implicant_of_polyhedral_constraints cnstrnts =
    cnstrnts /@ atom_of_polyhedral_constraint |> BatList.of_enum

  let implicant_of_int_constraints cnstrnts =
    cnstrnts /@ (fun v -> Syntax.mk_is_int Target.context (term_of_vector v))
    |> BatList.of_enum

  let linearize t =
    try
      Linear.linterm_of Target.context t
    with Linear.Nonlinear ->
      let s = Format.asprintf "Term %a is not linear" (Syntax.ArithTerm.pp Target.context) t
      in
      failwith s

  let constraint_of_atom atom =
    let image v = LM.apply map_to_fresh_dims v |> BatOption.get in
    match atom with
    | `ArithComparison (`Lt, t1, t2) ->
       (* Assuming that all symbols are integer-valued *)
       let v = V.sub (linearize t2) (linearize t1) in
       let offset = QQ.inverse (QQ.of_zz (V.common_denominator v)) in
       let v' = V.sub v (V.of_term offset Linear.const_dim) in
       `Ineq (`Nonneg, image v')
    | `ArithComparison (`Leq, t1, t2) ->
       `Ineq (`Nonneg, image (V.sub (linearize t2) (linearize t1)))
    | `ArithComparison (`Eq, t1, t2) ->
       `Ineq (`Zero, image (V.sub (linearize t2) (linearize t1)))
    | `IsInt s ->
       `InLat (image (linearize s))
    | `Literal _
      | `ArrEq _ -> failwith "Cannot handle atoms"

  let constraints_of_implicant atoms =
    List.fold_left
      (fun (inequalities, lattice_constraints) atom ->
        match constraint_of_atom
                (Interpretation.destruct_atom Target.context atom) with
        | `Ineq cnstrnt -> (cnstrnt :: inequalities, lattice_constraints)
        | `InLat v -> (inequalities, v :: lattice_constraints)
      )
      ([], [])
      atoms

end

module IntHullProjection (Target : Target)
       : (AbstractDomain with type t = DD.closed DD.t
                          and type context = Target.context) = struct

  include ImplicantConstraintConversion(Target)

  type t = DD.closed DD.t
  type context = Target.context
  let context = Target.context

  let bottom = P.dd_of ambient_dimension P.bottom

  let join p1 p2 = DD.join p1 p2

  let concretize p =
    let p_formulas = implicant_of_polyhedral_constraints (DD.enum_constraints p) in
    Syntax.mk_and context p_formulas

  let abstract formula interp =
    let implicant =
      match Interpretation.select_implicant interp formula with
      | Some implicant -> implicant
      | None -> failwith "No implicant found" in
    let (inequalities, _lattice_constraints) = constraints_of_implicant implicant in
    let p = DD.of_constraints_closed ambient_dimension (BatList.enum inequalities) in
    let hull = DD.integer_hull p in
    DD.project dimensions_to_eliminate hull

  let pp fmt p =
    Format.fprintf fmt "{ polyhedron : %a }"
      (DD.pp (fun fmt d -> Format.fprintf fmt "%d" d)) p

end

module CooperProjection (Target : Target)
       : (AbstractDomain with type t = DD.closed DD.t * IntLattice.t
                          and type context = Target.context) = struct

  include ImplicantConstraintConversion(Target)

  (* (P, L) s.t. P is integral with respect to the lattice satisfying L.
     L is the lattice generated by the vectors in Int(-), i.e., it is the
     dual lattice.
   *)
  type t = DD.closed DD.t * IntLattice.t

  type context = Target.context
  let context = Target.context

  let bottom = ( P.dd_of ambient_dimension P.bottom
               , IntLattice.hermitize [V.of_term QQ.one Linear.const_dim]
               )

  let join (p1, l1) (p2, l2) = (DD.join p1 p2, IntLattice.intersect l1 l2)

  let concretize (p, l) =
    let p_formulas = implicant_of_polyhedral_constraints (DD.enum_constraints p) in
    let l_formulas = implicant_of_int_constraints (BatList.enum (IntLattice.basis l)) in
    Syntax.mk_and Target.context (p_formulas @ l_formulas)

  let pp_dim = fun fmt d -> Format.fprintf fmt "%d" d

  let abstract formula interp =
    let implicant = match Interpretation.select_implicant interp formula with
      | Some implicant -> implicant
      | None -> failwith "No implicant found" in
    let (inequalities, lattice_constraints) = constraints_of_implicant implicant in
    let p = P.of_constraints (BatList.enum inequalities) in
    let l =
      let symbol_dimensions = (0 --^ ambient_dimension)
                              /@ V.of_term QQ.one
                              |> BatList.of_enum in
      logf "symbol dimensions: %a ambient dimension:%d@."
        (Format.pp_print_list V.pp) symbol_dimensions
        ambient_dimension;
      logf "lattice constraints: %a@." (Format.pp_print_list V.pp)
        lattice_constraints;
      IntLattice.hermitize (lattice_constraints @ symbol_dimensions)
    in
    logf "Polyhedron to project: %a@." (Polyhedron.pp pp_dim) p;
    logf "Lattice: %a@." IntLattice.pp l;
    logf "Dimensions to eliminate: %a@."
      (Format.pp_print_list Format.pp_print_int) dimensions_to_eliminate;
    let (projected_p, projected_l) =
      LatticePolyhedron.local_project_cooper (valuation interp)
        ~eliminate:dimensions_to_eliminate (p, l) in
    logf "Polyhedron after projection: %a@."
      (Polyhedron.pp pp_dim) projected_p;
    logf "Lattice after projection: %a@."
      IntLattice.pp projected_l;
    logf "Computing lattice polyhedron...@;";
    let hull = LatticePolyhedron.lattice_polyhedron_of projected_p projected_l in
    logf "Computed lattice polyhedron: %a@." (P.pp pp_dim) hull;
    ( DD.of_constraints_closed ambient_dimension (P.enum_constraints hull)
    , projected_l)

  let pp fmt (p, l) =
    Format.fprintf fmt "{ polyhedron : %a @. lattice: %a }"
      (DD.pp (fun fmt d -> Format.fprintf fmt "%d" d)) p
      IntLattice.pp l

end

module Abstract (A : AbstractDomain) : sig

  val abstract : A.context Syntax.formula -> A.t

end = struct

  let init formula =
    let solver = Smt.mk_solver A.context in
    Smt.Solver.add solver [formula];
    (solver, A.bottom)

  let abstract formula =
    let (solver, initial_value) = init formula in
    let rec go n value =
      logf "Iteration %d@." n;
      match Smt.Solver.get_model solver with
      | `Sat interp ->
         let rho = A.abstract formula interp in
         logf "abstract: abstracted, now joining";
         let joined = A.join value rho in
         logf "abstract: joining rho %a with %a to get %a@."
           A.pp rho
           A.pp value
           A.pp joined;
         let formula = A.concretize joined in
         logf "abstract: new constraint to negate: %a@."
           (Syntax.pp_smtlib2 A.context) formula;
         Smt.Solver.add solver
           [Syntax.mk_not A.context formula];
         go (n + 1) joined
      | `Unsat ->
         value
      | `Unknown -> failwith "Can't get model"
    in go 1 initial_value

end

let integer_hull (type a) (srk : a Syntax.context) ~how (phi : a Syntax.formula)
      terms =
  let module Target = struct
      type context = a
      let context = srk
      let formula_symbols = Syntax.symbols phi
      let terms = terms
    end in
  match how with
  | `Standard ->
     let module Compute = Abstract(IntHullProjection(Target)) in
     Compute.abstract phi
  | `Cooper ->
     let module Compute = Abstract(CooperProjection(Target)) in
     fst (Compute.abstract phi)
  | `Cone ->
     failwith "Not implemented yet"
