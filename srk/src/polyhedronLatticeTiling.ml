(**
   TODOs:

   - Change signature of [abstract_to_plt] to output term definitions of new dimensions
     This helps debugging and local-global iteration at any point.

   - Always expand floor, mod; generalize is_int translation to allow the
     possibility of translating is_int into a standard lattice by introducing
     new variables.

   - Run experiments to verify that everything is consistent.
 *)

open Syntax
module P = Polyhedron
module L = IntLattice

module V = Linear.QQVector

include Log.Make (struct let name = "polyhedronLatticeTiling" end)

let () = my_verbosity_level := `info
let test_convex_hull = ref false
let test_level = ref `debug

(* Some small constant *)
let _epsilon = QQ.of_frac 1 10

module LocalAbstraction : sig

  type ('concept1, 'point1, 'concept2, 'point2) t =
    {
      abstract: 'point1 -> 'concept1 -> 'concept2 * ('point1 -> 'point2)
    }

  val apply:
    ('concept1, 'point1, 'concept2, 'point2) t -> 'point1 -> 'concept1 -> 'concept2

  val apply2:
    ('concept1, 'point1, 'concept2, 'point2) t -> 'point1 -> 'concept1 ->
    'concept2 * ('point1 -> 'point2)

  val compose:
    ('concept2, 'point2, 'concept3, 'point3) t ->
    ('concept1, 'point1, 'concept2, 'point2) t ->
    ('concept1, 'point1, 'concept3, 'point3) t

end = struct

  (** A concept space consists of a universe of points and a set of
      concepts that defines a set of points in some way, e.g., logical satisfaction.

      Let C1, C2 be sets of concepts and P1, P2 be universes of points.
      A local abstraction consists of a function
      [abstract: P1 -> C1 -> C2 * (P1 -> P2)]
      such that whenever [p1] satisfies [c1],
      [abstract(p1, c1) = (c2, univ_translation)] only if
      - univ_translation(p1) satisfies c2
      - for all c2' in C2,
        if all points in univ_translation({x in P1: x satisfies c1}) satisfy c2',
        then all points in univ_translation({x in P2: x satisfies c2}) also
        satisfy c2'.
      This is a generalization of local abstractions where the universe
      translation is constant. This generalization allows local abstractions
      to "expand" the target universe/ambient space by introducing new dimensions
      depending on the concept being abstracted and the point within it,
      but all expansions agree on the intended target subspace and the intended
      universe translation.
   *)

  type ('concept1, 'point1, 'concept2, 'point2) t =
    {
      abstract: 'point1 -> 'concept1 -> 'concept2 * ('point1 -> 'point2)
    }

  let apply t x c = fst (t.abstract x c)

  let apply2 t x c = t.abstract x c

  let compose
        (t2: ('concept2, 'point2, 'concept3, 'point3) t)
        (t1: ('concept1, 'point1, 'concept2, 'point2) t) =
    let abstract x c =
      let (c2, translation12) = t1.abstract x c in
      let (c3, translation23) = t2.abstract (translation12 x) c2 in
      (c3, fun m -> translation23 (translation12 m))
    in
    { abstract }

end

module IntSet = SrkUtil.Int.Set
module IntMap = SrkUtil.Int.Map

let term_of_vector srk term_of_dim v =
  let open Syntax in
  V.enum v
  |> BatEnum.fold
       (fun summands (coeff, dim) ->
         if dim <> Linear.const_dim then
           mk_mul srk [mk_real srk coeff; term_of_dim dim] :: summands
         else
           mk_real srk coeff :: summands)
       []
  |> mk_add srk

let formula_p srk term_of_dim (kind, v) =
  let t = term_of_vector srk term_of_dim v in
  match kind with
  | `Zero -> mk_eq srk t (mk_zero srk)
  | `Nonneg -> mk_leq srk (mk_zero srk) t
  | `Pos -> mk_lt srk (mk_zero srk) t

let formula_l srk term_of_dim v =
  let t = term_of_vector srk term_of_dim v in
  mk_is_int srk t

let formula_t srk term_of_dim v =
  let t = term_of_vector srk term_of_dim v in
  mk_not srk (mk_is_int srk t)

let formula_of_dd srk term_of_dim dd =
  DD.enum_constraints dd
  |> BatEnum.fold
       (fun atoms (kind, v) -> formula_p srk term_of_dim (kind, v) :: atoms) []
  |> List.rev
  |> mk_and srk

let collect_dimensions vector_of add_dim constraints =
  let dims = ref IntSet.empty in
  BatList.iter
    (fun constr ->
      V.enum (vector_of constr)
      |> BatEnum.iter
           (fun (_, dim) ->
             if dim <> Linear.const_dim && add_dim dim
             then dims := IntSet.add dim !dims
             else ())
    )
    constraints;
  !dims

let pp_dim fmt dim = Format.fprintf fmt "(dim %d)" dim

let pp_vector = V.pp_term pp_dim

let pp_pconstr fmt (kind, v) =
  match kind with
  | `Zero -> Format.fprintf fmt "@[%a@] = 0" pp_vector v
  | `Nonneg -> Format.fprintf fmt "@[%a@] >= 0" pp_vector v
  | `Pos -> Format.fprintf fmt "@[%a@] > 0" pp_vector v

let pp_term_of_dim srk fmt map =
  IntMap.iter
    (fun dim term ->
      Format.fprintf fmt "(%d: %a), "
        dim
        (Syntax.ArithTerm.pp srk) term)
    map

let log_plt_constraints ~level str (p, l, t) =
  logf ~level
    "%s: p_constraints: @[%a@]@\n" str
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
       pp_pconstr) p;
  logf ~level
    "%s: l_constraints: @[%a@]@\n" str
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
       pp_vector) l;
  logf ~level
    "%s: t_constraints: @[%a@]@\n" str
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
       pp_vector) t

let test_point_in_polyhedron str m p =
  if Log.level_leq !my_verbosity_level !test_level then
    List.iter
      (fun (kind, v) ->
        logf ~level:`debug "%s: testing @[%a@]" str pp_pconstr (kind, v);
        let result = Linear.evaluate_affine m v in
        match kind with
        | `Zero ->
           if not (QQ.equal result QQ.zero) then
             failwith
               (Format.asprintf "%s: evaluated vector to %a, expected 0"
                  str QQ.pp result)
           else ()
        | `Nonneg -> assert (QQ.leq QQ.zero result)
        | `Pos -> assert (QQ.lt QQ.zero result)
      )
      p
  else ()

let test_point_in_lattice is_int str m l =
  if Log.level_leq !my_verbosity_level !test_level then
    List.iter
      (fun v ->
        logf ~level:`debug "%s: testing %a(%a)"
          str
          (fun fmt is_int -> match is_int with
                             | `IsInt -> Format.fprintf fmt "Int"
                             | `NotInt -> Format.fprintf fmt "~Int")
          is_int
          Linear.QQVector.pp v;
        let result = Linear.evaluate_affine m v in
        match QQ.to_zz result, is_int with
        | Some _, `IsInt -> ()
        | None, `NotInt -> ()
        | None, `IsInt ->
           failwith
             (Format.asprintf "%s: evaluated vector to %a, expected an integer"
                str QQ.pp result)
        | Some _, `NotInt ->
           failwith
             (Format.asprintf "%s: evaluated vector to %a, expected a non-integer"
                str QQ.pp result)
      )
      l
  else ()

let test_implication str solver consequence =
  if Log.level_leq !my_verbosity_level !test_level then
    begin
      logf str;
      let srk = Abstract.Solver.get_context solver in
      let phi = Abstract.Solver.get_formula solver in
      let goal = Syntax.mk_and srk [phi; Syntax.mk_not srk consequence] in
      let solver = SrkZ3.Solver.make srk in
      let msg status =
        Format.asprintf "@[%a@]@\n %s @\n@[%a@]@;"
          (Syntax.Formula.pp srk) phi
          status
          (Syntax.Formula.pp srk) consequence
      in
      SrkZ3.Solver.add solver [goal];
      if (SrkZ3.Solver.check solver = `Unsat) then
        logf "Test passed: %s" (msg "implies")
      else
        failwith (msg "does not imply")
    end
  else ()

let test_hull solver terms dd =
  if Log.level_leq !my_verbosity_level !test_level && !test_convex_hull then
    let srk = Abstract.Solver.get_context solver in
    let consequence = formula_of_dd srk (fun dim -> terms.(dim)) dd in
    test_implication
      "Checking if convex hull is consistent with input formula..."
      solver consequence
  else
    ()

module Plt : sig

  type standard
  type intfrac =
    {
      start_of_term_int_frac: int
    ; start_of_symbol_int_frac: int
    }

  type 'layout t

  (* val subset: 'layout t -> 'layout t -> bool *)

  val int_frac_layout: num_terms:int -> intfrac

  val formula_of_plt:
    'a context -> (int -> 'a arith_term) -> 'layout t -> 'a formula

  val constrained_dimensions: 'layout t -> IntSet.t

  val ceiling_int_frac:
    (int -> QQ.t) -> V.t -> (V.t * (P.constraint_kind * V.t) list * V.t list)

  (* An expansion defines how terms are expanded into vectors;
     floor and modulo terms correspond to fresh dimensions starting at free_dim.
   *)

  (*
  type 'a expansion

  val mk_standard_expansion:
    'a Syntax.context -> dim_of_symbol:(Syntax.symbol -> int) -> free_dim:int -> 'a expansion

  val abstract_to_plt:
    'a expansion ->
    'a context ->
    ?term_of_new_dims_to_set:(('a Syntax.arith_term) IntMap.t) ref option ->
    ?universe_p:(P.constraint_kind * V.t) list ->
    ?universe_l:V.t list ->
    ?universe_t:V.t list ->
    ('a Interpretation.interpretation -> int -> Q.t) ->
    ('a formula, 'a Interpretation.interpretation, 'b t, int -> Q.t)
      LocalAbstraction.t
   *)

  (** A standard PLT lives in a space where dimensions are partitioned into
      three parts:
      - Dimensions i between 0 to (Array.length terms) exclusive correspond to
        term i in the term array.
      - Dimensions i from Array.length terms to
        Array.length terms + max int_of_symbol over symbols correspond to symbol
        (i - Array.length terms)
      - "New dimensions" that start from the maximum of
        (Array.length terms + max int_of_symbol over symbols + 1) and
        the largest dimension in the support of [term_of_new_dims_to_set].

      Each time the local abstraction is applied, [term_of_new_dims_to_set] is
      extended with term definitions for new dimensions that are introduced
      in the space that the output PLT lives in.
   *)
  val abstract_to_standard_plt:
    [`ExpandModFloor | `NoExpandModFloor] ->
    'a context ->
    ?term_of_new_dims_to_set:(('a Syntax.arith_term) IntMap.t) ref option ->
    'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, standard t, int -> Q.t)
      LocalAbstraction.t

  val abstract_to_intfrac_plt:
    [`ExpandModFloor | `NoExpandModFloor] ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, intfrac t, int -> Q.t)
      LocalAbstraction.t

  val poly_part: 'layout t -> P.t
  val lattice_part: 'layout t -> L.t
  val tiling_part: 'layout t -> L.t

  val mk_plt:
    poly_part:P.t -> lattice_part:L.t -> tiling_part:L.t -> 'layout t

  val abstract_poly_part:
    (P.t, int -> Q.t, P.t, int -> Q.t) LocalAbstraction.t ->
    ('layout t, int -> Q.t, 'layout t, int -> Q.t) LocalAbstraction.t

  (** Given a point [m] in [plt] and a direction [dirn],
      [extrapolate m dirn plt] is the list of (one or two) extreme points
      that lie in [plt] and the line parallel to [dirn] passing through [m].

  val extrapolate:
    integer_point:V.t -> direction:V.t -> 'layout t -> V.t list
   *)

  (** Given a point [m] in [plt] that is a subset of RR^{[max_dim]},
      [polytope_of_far_lattice_points max_dim m plt] is a polyhedron that
      contains [m], whose vertices are in [plt], and whose recession cone is
      [rec.cone(poly_part(plt))].
      The vertices are far from [m] by being close to vertices of the
      polyhedral part of [plt], selected using the procedure in Lemma 4.8 of
      Haase, Krishna, Madnani, Mishra, Zetzsche: "An efficient quantifier
      elimination procedure for Presburger arithmetic".
   *)
  val polyhedron_of_far_lattice_points:
    man:(DD.closed Apron.Manager.t) -> max_dim:int ->
    (int -> Q.t) -> 'layout t -> DD.closed DD.t

end = struct

  type standard = unit

  type intfrac =
    {
      start_of_term_int_frac: int
    ; start_of_symbol_int_frac: int
    }

  type 'layout t =
    {
      poly_part: P.t
    ; lattice_part: L.t
    ; tiling_part: L.t
    }

  let poly_part plt = plt.poly_part
  let lattice_part plt = plt.lattice_part
  let tiling_part plt = plt.tiling_part
  let mk_plt ~poly_part ~lattice_part ~tiling_part =
    {
      poly_part
    ; lattice_part
    ; tiling_part
    }

  let constrained_dimensions plt =
    let p = BatList.of_enum (P.enum_constraints plt.poly_part) in
    let l = L.basis plt.lattice_part in
    let t = L.basis plt.tiling_part in
    collect_dimensions (fun (_, v) -> v) (fun _ -> true) p
    |> IntSet.union (collect_dimensions (fun v -> v) (fun _ -> true) l)
    |> IntSet.union (collect_dimensions (fun v -> v) (fun _ -> true) t)

  (*
  let top =
    {
      poly_part = Polyhedron.top
    ; lattice_part = L.bottom
    ; tiling_part = L.bottom
    }
   *)

  let real_of v =
    let (r, v') = V.pivot Linear.const_dim v in
    if V.is_zero v' then r
    else invalid_arg "not a constant"

  let mul_vec v1 v2 =
    try V.scalar_mul (real_of v1) v2
    with Invalid_argument _ ->
      begin
        try V.scalar_mul (real_of v2) v1
        with
          Invalid_argument _ ->
          raise Linear.Nonlinear
      end

  type lin_cond =
    {
      p_cond: (P.constraint_kind * V.t) list
    ; l_cond: V.t list
    ; t_cond: V.t list
    }

  let tru =
    {
      p_cond = []
    ; l_cond = []
    ; t_cond = []
    }

  let fls =
    {
      p_cond = [(`Zero, Linear.const_linterm QQ.one)]
    ; l_cond = []
    ; t_cond = []
    }

  let conjoin lin1 lin2 =
    {
      p_cond = List.rev_append lin1.p_cond lin2.p_cond
    ; l_cond = List.rev_append lin1.l_cond lin2.l_cond
    ; t_cond = List.rev_append lin1.t_cond lin2.t_cond
    }

  let lift_binop op (v1, lin1) (v2, lin2) =
    (op v1 v2, conjoin lin1 lin2)

  (*
  type term_vector =
    | TV_real of QQ.t
    | TV_mod of V.t * QQ.t
    | TV_floor of V.t
   *)

  let lin_mod
        ~vec_of_free_dim
        ~int_cond
        ~next_free_dim
        ~add_term_of_dim
        srk
        ~free_dim term_of_dim v1 v2 t1 t2 =
    let modulus =
      try real_of v2 with
      | Invalid_argument _ -> raise Linear.Nonlinear
    in
    let () =
      if QQ.equal modulus QQ.zero then invalid_arg "Division by zero"
      else ()
    in
    let quotient = vec_of_free_dim free_dim in
    logf ~level:`debug
      "lin_mod: introducing dimension %d for quotient in @[%a@] modulo %a (@[%a@] modulo %a)"
      free_dim pp_vector v1 QQ.pp modulus
      (ArithTerm.pp srk) t1 (ArithTerm.pp srk) t2;
    let remainder = V.sub v1 (V.scalar_mul modulus quotient) in
    let (intcond_p, intcond_l) = int_cond free_dim in
    let lincond =
      {
        p_cond = [(`Nonneg, remainder); (`Pos, V.sub v2 remainder)]
                 @ intcond_p
      ; l_cond = intcond_l
      ; t_cond = []
      }
    in
    let quotient_term =
      mk_div srk (mk_sub srk t1 (mk_mod srk t1 t2)) t2 in
    ( remainder
    , lincond
    , next_free_dim free_dim
    , add_term_of_dim free_dim quotient_term term_of_dim
    )

  let lin_floor
        ~vec_of_free_dim ~int_cond ~next_free_dim ~add_term_of_dim
        srk ~free_dim term_of_dim v t =
    let floored = vec_of_free_dim free_dim in
    logf ~level:`debug "introducing dimension %d for floor(%a)"
      free_dim pp_vector v;
    let lower_bound = V.sub v floored in
    let upper_bound =
      V.sub floored v |>
        V.add_term QQ.one Linear.const_dim in
    let (intcond_p, intcond_l) = int_cond free_dim in
    let lincond =
      {
        p_cond = [(`Nonneg, lower_bound); (`Pos, upper_bound)]
                 @ intcond_p
      ; l_cond = intcond_l
      ; t_cond = []
      }
    in
    ( floored
    , lincond
    , next_free_dim free_dim
    , add_term_of_dim free_dim (Syntax.mk_floor srk t) term_of_dim
    )

  type 'a expand_mod_floor =
    | NoExpansion
    | Expand_mod_floor_with of
        { free_dim: int
        ; new_dimensions: ('a Syntax.arith_term) IntMap.t
        ; linearize_mod: 'a Syntax.context -> free_dim:int -> ('a Syntax.arith_term) IntMap.t ->
                         V.t -> V.t -> ('a Syntax.arith_term) -> ('a Syntax.arith_term) ->
                         (V.t * lin_cond * int * ('a Syntax.arith_term) IntMap.t)
        ; linearize_floor: 'a Syntax.context -> free_dim:int -> ('a Syntax.arith_term) IntMap.t ->
                           V.t -> 'a Syntax.arith_term ->
                           (V.t * lin_cond * int * ('a Syntax.arith_term) IntMap.t)
        }

  type 'a expansion =
    {
      vec_of_symbol: Syntax.symbol -> V.t
    ; translate_int_atom: [`IsInt | `NotInt] -> (int -> QQ.t) -> V.t -> lin_cond
    (* TODO: one more way of translating an int_atom is to replace the term
       inside with a fresh dimension, i.e.,
       for `IsInt, add a new equation defining a new dimension and add the
       dimension to the lattice,
       and for `NotInt, add a new inequality b < t < b + 1 and dimension b to
       the lattice.
       So [translate_int_atom] should have a signature like [linearize_floor].
     *)
    ; expand_mod_floor: 'a expand_mod_floor
    }

  let expand_univ_translation univ_translation interp new_dimensions initial =
    let extend m new_dimensions dim =
      try
        begin
          let term = IntMap.find dim new_dimensions in
          Interpretation.evaluate_term interp term
        end
      with
      | Not_found -> m dim
    in
    let next = univ_translation initial in
    extend next new_dimensions

  let floor_int_frac m v =
    let (integer_part, fraction_from_integer_part, lconds) =
      V.fold
        (fun dim coeff (integer_part, fractional_part, lconds) ->
          if dim = Linear.const_dim then
            (integer_part, fractional_part, lconds)
          else if dim mod 2 = 1 then (integer_part, fractional_part, lconds)
          else
            let (p, q) = QQ.to_zzfrac coeff in
            let remainder =
              match QQ.to_zz (m dim) with
              | Some n -> ZZ.modulo (ZZ.mul p n) q
              | None ->
                 failwith
                   (Format.asprintf "dim %d should evaluate to an integer" dim)
            in
            let fraction = QQ.of_zzfrac remainder q in
            let integer_summand =
              V.of_term coeff dim
              |> V.add_term (QQ.negate fraction) Linear.const_dim in
            ( V.add integer_part integer_summand
            , QQ.add fractional_part fraction
            , integer_summand :: V.of_term QQ.one dim :: lconds
            )
        )
        v
        (V.zero, QQ.zero, [])
    in
    let within_unit_interval lower_bound term =
      [
        (`Nonneg, V.add_term (QQ.negate lower_bound) Linear.const_dim term)
      ; (`Pos, (Linear.const_linterm (QQ.add lower_bound QQ.one))
               |> V.add (V.negate term))
      ]
    in
    let (fraction_part, pconds) =
      let constant_within_floor =
        QQ.add fraction_from_integer_part (V.coeff Linear.const_dim v)
      in
      V.fold
        (fun dim coeff (sum, term, fractional_bounds) ->
          if dim = Linear.const_dim then (sum, term, fractional_bounds)
          else if dim mod 2 = 0 then (sum, term, fractional_bounds)
          else
            ( QQ.add (QQ.mul coeff (m dim)) sum
            , V.add_term coeff dim term
            , List.rev_append
                (within_unit_interval QQ.zero (V.of_term QQ.one dim))
                fractional_bounds
            )
        )
        v
        ( constant_within_floor
        , Linear.const_linterm constant_within_floor
        , []
        )
      |> (fun (sum, term, fractional_bounds) ->
        let lower_bound = QQ.floor sum |> QQ.of_zz in
        let pconds =
          List.rev_append
            (within_unit_interval lower_bound term)
            fractional_bounds
        in
        (lower_bound, pconds))
    in
    let result = V.add_term fraction_part Linear.const_dim integer_part in
    logf ~level:`debug
      "floor_int_frac: @[floor(%a) = %a@] is %b when @[%a@] and@\n @[%a@]@;"
      pp_vector v pp_vector result
      (QQ.equal (QQ.of_zz (QQ.floor (Linear.evaluate_affine m v))) (Linear.evaluate_affine m result))
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") pp_pconstr)
      pconds
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") pp_vector)
      lconds;
    test_point_in_polyhedron "floor_int_frac" m pconds;
    test_point_in_lattice `IsInt "floor_int_frac" m lconds;
    (result, pconds, lconds)

  let ceiling_int_frac m v =
    let (neg_v', pcond, lcond) = floor_int_frac m (V.negate v) in
    let v' = V.negate neg_v' in
    (v', pcond, lcond)

  let standard_vec_of_symbol dim_of_symbol s =
    V.of_term QQ.one (dim_of_symbol s)

  let int_frac_vec_of_symbol dim_of_symbol s =
    V.of_term QQ.one (dim_of_symbol s)
    |> V.add_term QQ.one (dim_of_symbol s + 1)

  let mk_expansion srk expand layout dim_of_symbol =
    let mk_standard lin =
      lin
        ~vec_of_free_dim:(V.of_term QQ.one)
        ~int_cond:(fun dim -> ([], [V.of_term QQ.one dim]))
        ~next_free_dim:(fun n -> n + 1)
        ~add_term_of_dim:IntMap.add
    in
    let mk_int_frac lin =
      lin
        ~vec_of_free_dim:(fun dim -> V.of_term QQ.one dim |> V.add_term QQ.one (dim + 1))
        ~int_cond:(fun dim -> ([(`Zero, V.of_term QQ.one (dim + 1))], []))
        ~next_free_dim:(fun n -> n + 2)
        ~add_term_of_dim:(fun free_dim term map ->
          IntMap.add free_dim term map |> IntMap.add (free_dim + 1) (Syntax.mk_real srk QQ.zero)
        )
    in
    let int_frac_translate integral m v =
      let (result, pconds, lconds) = floor_int_frac m v in
      match integral with
      | `IsInt ->
         { p_cond = (`Zero, V.sub v result) :: pconds
         ; l_cond = lconds
         ; t_cond = []
         }
      | `NotInt ->
         { p_cond = (`Pos, V.sub v result) :: pconds
         ; l_cond = lconds
         ; t_cond = []
         }
    in
    let standard_translate integral _m v =
      match integral with
      | `IsInt -> { p_cond = []; l_cond = [v]; t_cond = [] }
      | `NotInt -> { p_cond = []; l_cond = []; t_cond = [v] }
    in
    match layout with
    | `Standard ->
       begin match expand with
       | `Expand free_dim ->
          { vec_of_symbol = standard_vec_of_symbol dim_of_symbol
          ; translate_int_atom = standard_translate
          ; expand_mod_floor =
              Expand_mod_floor_with
                { free_dim
                ; new_dimensions = IntMap.empty
                ; linearize_mod = mk_standard lin_mod
                ; linearize_floor = mk_standard lin_floor
                }
          }
       | `NoExpand ->
          { vec_of_symbol = standard_vec_of_symbol dim_of_symbol
          ; translate_int_atom = standard_translate
          ; expand_mod_floor = NoExpansion
          }
       end
    | `IntFrac ->
       begin match expand with
       | `Expand free_dim ->
          { vec_of_symbol = int_frac_vec_of_symbol dim_of_symbol
          ; translate_int_atom = int_frac_translate
          ; expand_mod_floor =
              Expand_mod_floor_with
                { free_dim
                ; new_dimensions = IntMap.empty
                ; linearize_mod = mk_int_frac lin_mod
                ; linearize_floor = mk_int_frac lin_floor
                }
          }
       | `NoExpand ->
          { vec_of_symbol = int_frac_vec_of_symbol dim_of_symbol
          ; translate_int_atom = int_frac_translate
          ; expand_mod_floor = NoExpansion
          }
       end

  (*
  let mk_standard_expansion srk ~dim_of_symbol ~free_dim =
    mk_expansion srk (`Expand free_dim) `Standard dim_of_symbol
   *)

  (* Linear.linterm_of can only handle div and mod on constants, but
     [t div constant] and [t mod constant] can come from the input.
     Also, Interpretation.destruct_atom translates [IsInt t] into
     [t' mod constant] terms.
   *)
  let linearize_term srk expansion term =
    let vec_of_symbol = expansion.vec_of_symbol in
    let (curr_free_dim, curr_term_of_dim, lin_mod, lin_floor) =
      match expansion.expand_mod_floor with
      | Expand_mod_floor_with
        { free_dim
        ; new_dimensions
        ; linearize_mod = lin_mod
        ; linearize_floor = lin_floor
        } ->
         (ref free_dim, ref new_dimensions, lin_mod, lin_floor)
      | NoExpansion ->
         ( ref (-1)
         , ref IntMap.empty
         , (fun _srk ~free_dim _term_of_dim -> ignore free_dim; invalid_arg "mod term in formula")
         , (fun _srk ~free_dim _term_of_dim -> ignore free_dim; invalid_arg "floor term in formula")
         )
    in
    let old_term_of_dim = !curr_term_of_dim in
    let (linearized, cond, _term) =
      ArithTerm.eval srk (function
          | `Real r -> (Linear.const_linterm r, tru, mk_real srk r)
          | `App (x, []) -> (vec_of_symbol x, tru, mk_const srk x)
          | `App (_f, _xs) -> raise Linear.Nonlinear
          | `Var (_i, _typ) -> raise Linear.Nonlinear
          | `Add lincondterms ->
             let linconds =
               List.map (fun (lin, cond, _term) -> (lin, cond)) lincondterms
             in
             let (lin, cond) = List.fold_left (lift_binop V.add) (V.zero, tru)
                                 linconds
             in
             (lin, cond, Syntax.mk_add srk (List.map (fun (_, _, term) -> term) lincondterms))
          | `Mul lincondterms ->
             let linconds =
               List.map (fun (lin, cond, _term) -> (lin, cond)) lincondterms
             in
             let (lin, cond) =
               List.fold_left (lift_binop mul_vec) (Linear.const_linterm QQ.one, tru)
                 linconds
             in
             (lin, cond, Syntax.mk_mul srk (List.map (fun (_, _, term) -> term) lincondterms))
          | `Binop (`Div, lincondterm1, lincondterm2) ->
             begin
               let (lin1, cond1, term1) = lincondterm1 in
               let (lin2, cond2, term2) = lincondterm2 in
               let lincond1, lincond2 = (lin1, cond1), (lin2, cond2) in
               let divide v1 v2 =
                 let divisor = try real_of v2 with | Invalid_argument _ -> raise Linear.Nonlinear
                 in
                 if QQ.equal divisor QQ.zero then invalid_arg "Division by zero"
                 else
                   V.scalar_mul (QQ.inverse divisor) v1
               in
               let (div_v, lincond) = (lift_binop divide) lincond1 lincond2 in
               (div_v, lincond, Syntax.mk_div srk term1 term2)
             end
          | `Binop (`Mod, (v1, cond1, t1), (v2, cond2, t2)) ->
             let (mod_v, cond, next_free_dim, next_term_of_dim) =
               lin_mod srk ~free_dim:!curr_free_dim !curr_term_of_dim v1 v2 t1 t2
             in
             let lincond = (conjoin cond2 cond1)
                           |> conjoin cond
             in
             curr_free_dim := next_free_dim;
             curr_term_of_dim := next_term_of_dim;
             (mod_v, lincond, Syntax.mk_mod srk t1 t2)
          | `Unop (`Floor, (v, cond, term)) ->
             let (floor_v, floor_cond, next_free_dim, next_term_of_dim) =
               lin_floor srk ~free_dim:!curr_free_dim !curr_term_of_dim v term
             in
             let lincond_floor = conjoin floor_cond cond in
             curr_free_dim := next_free_dim;
             curr_term_of_dim := next_term_of_dim;
             (floor_v, lincond_floor, Syntax.mk_floor srk term)
          | `Unop (`Neg, (v, lincond, term)) ->
             (V.negate v, lincond, Syntax.mk_neg srk term)
          | `Ite _ -> assert false
          | `Select _ -> raise Linear.Nonlinear
        ) term
    in
    logf ~level:`trace "term_of_dim before linearization: @[%a@]"
      (pp_term_of_dim srk)
      old_term_of_dim;
    logf ~level:`trace "curr_term_of_dim: @[%a@]" (pp_term_of_dim srk)
      !curr_term_of_dim;
    let expand_mod_floor =
      match expansion.expand_mod_floor with
      | NoExpansion -> NoExpansion
      | Expand_mod_floor_with initial ->
         Expand_mod_floor_with
           { initial with
             free_dim = !curr_free_dim
           ; new_dimensions = !curr_term_of_dim
           }
    in
    (linearized, cond, {expansion with expand_mod_floor})

  (*
  let union_expansion expansion1 expansion2 =
    let exp1, exp2 = expansion1.expand_mod_floor, expansion2.expand_mod_floor
    in
    let expand_mod_floor =
      match exp1, exp2 with
      | Expand_mod_floor_with
        { free_dim = free_dim1
        ; new_dimensions = new_dims1
        ; linearize_mod
        ; linearize_floor
        },
        Expand_mod_floor_with
          { free_dim = free_dim2
          ; new_dimensions = new_dims2
          ; _
          } ->
         Expand_mod_floor_with
           { free_dim = Int.max free_dim1 free_dim2
           ; new_dimensions =
               IntMap.union (fun _dim _t1 t2 -> Some t2)
                 new_dims1 new_dims2
           ; linearize_mod
           ; linearize_floor
           }
      | _, _ -> failwith "Cannot combine incompatible expansions"
    in
    {expansion1 with expand_mod_floor}
   *)

  let plt_ineq srk expansion (sign: [`Lt | `Leq | `Eq]) t1 t2 =
    let (v2, lin2, expansion2) = linearize_term srk expansion t2 in
    let (v1, lin1, expansion1) = linearize_term srk expansion2 t1 in
    let v = V.sub v2 v1 in
    let kind = match sign with
      | `Lt -> `Pos
      | `Leq -> `Nonneg
      | `Eq -> `Zero
    in
    let constrnt = {
        p_cond = (kind, v) :: (lin1.p_cond @ lin2.p_cond)
      ; l_cond = lin1.l_cond @ lin2.l_cond
      ; t_cond = lin1.t_cond @ lin2.t_cond
      }
    in
    (constrnt, expansion1)

  let plt_int srk univ_translation expansion interp (sign: [`IsInt | `NotInt]) t =
    let (v, lincond_linearize, next_expansion) = linearize_term srk expansion t in
    let m =
      match next_expansion.expand_mod_floor with
      | NoExpansion -> univ_translation interp
      | Expand_mod_floor_with {new_dimensions; _} ->
         (expand_univ_translation univ_translation interp new_dimensions) interp
    in
    let lincond_int = next_expansion.translate_int_atom sign m v
    in
    (conjoin lincond_int lincond_linearize, next_expansion)

  let plt_constraint_of_atom srk univ_translation expansion interp atom =
    match Formula.destruct srk atom with
    | `Tru -> (tru, expansion)
    | `Fls -> (fls, expansion)
    | `Not psi ->
       begin
         match Formula.destruct srk psi with
         | `Tru -> (fls, expansion)
         | `Fls -> (tru, expansion)
         | `Atom (`Arith (`Eq, t1, t2)) ->
            if Interpretation.evaluate_formula interp (Syntax.mk_lt srk t1 t2)
            then
              plt_ineq srk expansion `Lt t1 t2
            else
              plt_ineq srk expansion `Lt t2 t1
         | `Atom (`Arith (`Leq, t1, t2)) ->
            plt_ineq srk expansion `Lt t2 t1
         | `Atom (`Arith (`Lt, t1, t2)) ->
            plt_ineq srk expansion `Leq t2 t1
         | `Atom (`ArrEq (_t1, _t2)) -> invalid_arg "linearize_atom"
         | `Atom (`IsInt t) ->
            plt_int srk univ_translation expansion interp `NotInt t
         | _ -> invalid_arg "linearize_atom"
       end
    | `Atom (`Arith (`Eq, t1, t2)) ->
       plt_ineq srk expansion `Eq t1 t2
    | `Atom (`Arith (`Leq, t1, t2)) ->
       plt_ineq srk expansion `Leq t1 t2
    | `Atom (`Arith (`Lt, t1, t2)) ->
       plt_ineq srk expansion `Lt t1 t2
    | `Atom (`ArrEq (_t1, _t2)) -> invalid_arg "linearize_atom"
    | `Atom (`IsInt t) ->
       plt_int srk univ_translation expansion interp `IsInt t
    | _ -> invalid_arg "linearize_atom"

  let plt_implicant_of_implicant srk univ_translation expansion m implicant =
    match implicant with
    | None -> assert false
    | Some atoms ->
       List.fold_left (fun (lincond, expansion) atom ->
           let (lincond_atom, next_expansion) =
             plt_constraint_of_atom srk univ_translation expansion m atom in
           (conjoin lincond_atom lincond, next_expansion)
         )
         (tru, expansion)
         atoms

  let formula_of_plt srk term_of_dim plt =
    let phis_p =
      BatEnum.map (formula_p srk term_of_dim) (P.enum_constraints plt.poly_part)
      |> BatList.of_enum
    in
    let phis_l =
      List.map (formula_l srk term_of_dim) (L.basis plt.lattice_part)
    in
    let phis_t =
      List.map (formula_t srk term_of_dim) (L.basis plt.tiling_part)
    in
    mk_and srk (phis_p @ phis_l @ phis_t)

  let abstract_to_plt
        expansion
        srk
        ?(term_of_new_dims_to_set = None)
        ?(universe_p=[])
        ?(universe_l=[])
        ?(universe_t=[])
        univ_translation =
    let abstract interp phi =
      logf ~level:`debug "abstract_to_plt...";
      let implicant = Interpretation.select_implicant interp phi in
      logf ~level:`debug "abstract_to_plt: abstracting @[%a@]"
        (Format.pp_print_list
           ~pp_sep: (fun fmt () -> Format.fprintf fmt ", ")
           (fun fmt atom -> Syntax.Formula.pp srk fmt atom)
        )
        (Option.get implicant);
      let (lincond, post_expansion) =
        plt_implicant_of_implicant srk univ_translation expansion interp implicant in
      log_plt_constraints ~level:`debug "abstract_to_plt: abstracted: "
        (lincond.p_cond, lincond.l_cond, lincond.t_cond);
      let imp_p =
        Polyhedron.of_constraints
          (BatEnum.append (BatList.enum universe_p) (BatList.enum lincond.p_cond))
      in
      let imp_l =
        L.hermitize (List.rev_append universe_l lincond.l_cond)
      in
      let imp_t =
        L.hermitize (List.rev_append universe_t lincond.t_cond)
      in
      let plt = { poly_part = imp_p
                ; lattice_part = imp_l
                ; tiling_part = imp_t
                }
      in
      let expanded_univ_translation =
        match post_expansion.expand_mod_floor with
        | NoExpansion -> univ_translation
        | Expand_mod_floor_with {new_dimensions ; _} ->
           logf ~level:`debug
             "abstract_to_plt: expanding universe with dimensions @[%a@]"
             (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
                Format.pp_print_int)
             (BatList.of_enum (IntMap.keys new_dimensions));
           let () =
             match term_of_new_dims_to_set with
             | None -> ()
             | Some term_of_dim ->
                logf ~level:`debug "Adding dimensions @[%a@]"
                  (pp_term_of_dim srk) new_dimensions;
                term_of_dim :=
                  IntMap.union
                    (fun dim _ _ ->
                      failwith
                        (Format.asprintf
                           "expansion overlaps with existing dimensions in dimension %d"
                           dim)
                    ) !term_of_dim new_dimensions
           in
           expand_univ_translation univ_translation interp new_dimensions
      in
      test_point_in_polyhedron "abstract_to_plt"
        (expanded_univ_translation interp)
        (BatList.of_enum (P.enum_constraints plt.poly_part));
      test_point_in_lattice `IsInt "abstract_to_plt"
        (expanded_univ_translation interp)
        (L.basis plt.lattice_part);
      test_point_in_lattice `NotInt "abstract_to_plt"
        (expanded_univ_translation interp)
        (L.basis plt.tiling_part);
      (plt, expanded_univ_translation)
    in
    LocalAbstraction.{ abstract }

  let int_frac_layout ~num_terms =
    let start_of_term_int_frac =
      if num_terms mod 2 = 0 then num_terms
      else num_terms + 1
    in
    let start_of_symbol_int_frac = start_of_term_int_frac + (2 * num_terms) in
    { start_of_term_int_frac
    ; start_of_symbol_int_frac
    }

  let mk_interp_dim layout terms interp dim =
    let num_terms = Array.length terms in
    match layout with
    | `Standard ->
       if dim >= num_terms then
         Interpretation.real interp (Syntax.symbol_of_int (dim - num_terms))
       else if dim >= 0 && dim < num_terms then
         Interpretation.evaluate_term interp terms.(dim)
       else
         begin
           logf "interp_dim: %d not defined" dim;
           assert false
         end
    | `IntFrac ->
       let {start_of_term_int_frac ; start_of_symbol_int_frac} =
         int_frac_layout ~num_terms in
       let int r = QQ.floor r |> QQ.of_zz in
       let frac r = QQ.modulo r QQ.one in
       let original_idx base int_frac_idx =
         let idx =
           if int_frac_idx mod 2 = 0 then (int_frac_idx - base) / 2
           else (int_frac_idx - 1 - base) / 2
         in
         assert (idx >= 0);
         idx
       in
       if dim >= start_of_symbol_int_frac then
         let idx = original_idx start_of_symbol_int_frac dim in
         let value = Interpretation.real interp (Syntax.symbol_of_int idx) in
         if dim mod 2 = 0 then int value else frac value
       else if dim >= start_of_term_int_frac && dim < start_of_symbol_int_frac
       then
         let idx = original_idx start_of_term_int_frac dim in
         assert (idx >= 0 && idx < num_terms);
         let value = Interpretation.evaluate_term interp terms.(idx) in
         if dim mod 2 = 0 then int value else frac value
       else if dim >= 0 && dim < num_terms then
         Interpretation.evaluate_term interp terms.(dim)
       else if dim >= num_terms && dim < start_of_term_int_frac then QQ.zero
       else
         begin
           logf "interp_dim: %d not defined" dim;
           assert false
         end

  let mk_term_definitions layout srk dim_of_symbol terms =
    let linearize_term =
      match layout with
      | `Standard ->
         linearize_term srk (mk_expansion srk `NoExpand `Standard dim_of_symbol)
      | `IntFrac ->
         linearize_term srk (mk_expansion srk `NoExpand `IntFrac dim_of_symbol)
    in
    let vector_of_term idx =
      match layout with
      | `Standard -> V.of_term QQ.one idx
      | `IntFrac ->
         let {start_of_term_int_frac; _} =
           int_frac_layout ~num_terms:(Array.length terms) in
         let int_dim_of_term i = start_of_term_int_frac + (2 * i) in
         V.of_term QQ.one (int_dim_of_term idx)
         |> V.add_term QQ.one (int_dim_of_term idx + 1)
    in
    let (p_conds, l_conds, t_conds) =
      (ref (BatEnum.empty ()), ref (BatEnum.empty ()), ref (BatEnum.empty ()))
    in
    Array.iteri
      (fun dim term ->
        let (v, lincond, _expansion) = linearize_term term in
        BatEnum.push !p_conds
          (`Zero, V.add v (V.negate (vector_of_term dim)));
        p_conds := BatEnum.append (BatList.enum lincond.p_cond) !p_conds;
        l_conds := BatEnum.append (BatList.enum lincond.l_cond) !l_conds;
        t_conds := BatEnum.append (BatList.enum lincond.t_cond) !t_conds
      )
      terms;
    ( BatList.of_enum !p_conds
    , BatList.of_enum !l_conds
    , BatList.of_enum !t_conds
    )

  let get_max_dim layout num_terms symbols =
    match layout with
    | `Standard ->
       begin match Symbol.Set.max_elt_opt symbols with
       | None -> num_terms - 1
       | Some dim -> Syntax.int_of_symbol dim + num_terms
       end
    | `IntFrac ->
       let {start_of_symbol_int_frac; _} = int_frac_layout ~num_terms in
       begin match Symbol.Set.max_elt_opt symbols with
       | None -> start_of_symbol_int_frac - 1
       | Some dim ->
          let num_symbols = Syntax.int_of_symbol dim + 1 in
          start_of_symbol_int_frac + (2 * num_symbols) - 1
       end

  let abstract_to_standard_plt
        has_mod_floor srk ?(term_of_new_dims_to_set = None) terms symbols =
    let num_terms = Array.length terms in
    let max_dim = get_max_dim `Standard num_terms symbols in
    logf ~level:`debug "initial plt abstraction: max_dim: %d, num_terms = %d@;"
      max_dim num_terms;
    let dim_of_symbol sym = Syntax.int_of_symbol sym + num_terms in
    let free_dim =
      match term_of_new_dims_to_set with
      | None -> max_dim + 1
      | Some term_of_new_dims ->
         begin match IntMap.max_binding_opt !term_of_new_dims with
         | None -> max_dim + 1
         | Some (dim, _) -> (Int.max max_dim dim) + 1
         end
    in
    let expansion =
      let expand = match has_mod_floor with
        | `NoExpandModFloor -> `NoExpand
        | `ExpandModFloor -> `Expand free_dim
      in
      mk_expansion srk expand `Standard dim_of_symbol
    in
    let (universe_p, universe_l, universe_t) =
      mk_term_definitions `Standard srk dim_of_symbol terms in
    logf ~level:`debug "abstract_to_standard_plt...";
    log_plt_constraints ~level:`debug "term definitions" (universe_p, universe_l, universe_t);
    let interp_dim = mk_interp_dim `Standard terms in
    abstract_to_plt expansion srk ~term_of_new_dims_to_set
      ~universe_p ~universe_l ~universe_t interp_dim

  (* LIRA PLT layout:
     0 ... len(terms) - 1 represent terms.
     Let n be the first even integer >= len(terms).
     Dimensions corresponding to integer-valued variables are even and
     those for fractional variables are odd.
     Then n + 2k, n + 2k + 1 are the integer and fractional dimensions for
     the (k-1)-th term, k = 1, ..., len(terms).
     Dimensions (n + 2 * (len(terms) + m), (n + (2 * len(terms) + m) + 1)
     are the integer and fractional dimensions for symbol m,
     m = 0, ..., max_elt symbols.
   *)
  let abstract_to_intfrac_plt has_mod_floor srk terms symbols =
    let num_terms = Array.length terms in
    let { start_of_symbol_int_frac ; start_of_term_int_frac} =
      int_frac_layout ~num_terms in
    let max_dim = get_max_dim `IntFrac num_terms symbols in
    logf ~level:`debug
      "initial int-frac plt abstraction: max_dim: %d, num_terms = %d,
       start_of_term_int_frac = %d, start_of_symbol_int_frac = %d@;"
      max_dim num_terms start_of_term_int_frac start_of_symbol_int_frac;
    let int_dim_of_symbol sym =
      start_of_symbol_int_frac + (2 * Syntax.int_of_symbol sym) in
    let expansion =
      let expand = match has_mod_floor with
        | `NoExpandModFloor -> `NoExpand
        | `ExpandModFloor -> `Expand (max_dim + 1)
      in
      mk_expansion srk expand `IntFrac int_dim_of_symbol
    in
    let (universe_p, universe_l, universe_t) =
      mk_term_definitions `IntFrac srk int_dim_of_symbol terms
    in
    logf ~level:`debug "abstract_to_intfrac_plt...";
    log_plt_constraints ~level:`debug "term definitions" (universe_p, universe_l, universe_t);
    let interp_dim = mk_interp_dim `IntFrac terms in
    abstract_to_plt expansion srk
      ~universe_p ~universe_l ~universe_t interp_dim

  let abstract_poly_part abstract_poly =
    let abstract m plt =
      let p = plt.poly_part in
      let (p', p_translate) = LocalAbstraction.apply2 abstract_poly m p in
      ({ plt with poly_part = p' }, p_translate)
    in
    LocalAbstraction.{abstract}

  (*
  let extrapolate ~integer_point ~direction plt =
    let lt = List.rev_append
               (L.basis (tiling_part plt))
               (L.basis (lattice_part plt)) in
    if V.equal V.zero direction then [integer_point]
    else
      begin
        logf ~level:`debug
          "extrapolate: integer point is @[%a@]@; direction is @[%a@]@;"
          pp_vector integer_point
          pp_vector direction;
        let u = List.map (V.dot direction) lt in
        let gcd = List.fold_left (fun a b -> QQ.gcd a b) QQ.zero u in
        let integral_direction = not (QQ.equal QQ.zero gcd) in
        let rescaled =
          if QQ.equal QQ.zero gcd then direction
          else V.scalar_mul (QQ.inverse gcd) direction
        in
        let min = function
          | `PlusInfinity, `PlusInfinity -> `PlusInfinity
          | `PlusInfinity, `Num n -> `Num n
          | `Num n, `PlusInfinity -> `Num n
          | `Num n1, `Num n2 -> `Num (QQ.min n1 n2)
        in
        let (coeff_neg_dirn, coeff_pos_dirn) =
          BatEnum.fold
            (fun (max_neg_dirn, max_pos_dirn) (kind, v) ->
              let eval_base = QQ.add (V.dot v integer_point) (V.coeff Linear.const_dim v) in
              let eval_rescaled_direction = V.dot v rescaled in
              let (curr_num_steps_neg_dirn, curr_num_steps_pos_dirn) =
                match kind with
                | `Zero ->
                   if QQ.equal QQ.zero eval_rescaled_direction then
                     (`PlusInfinity, `PlusInfinity)
                   else
                     (`Num QQ.zero, `Num QQ.zero)
                | `Nonneg
                  | `Pos ->
                   if QQ.equal QQ.zero eval_rescaled_direction then
                     (`PlusInfinity, `PlusInfinity)
                   else
                     let num_steps =
                       if integral_direction then
                         QQ.of_zz (QQ.idiv eval_base (QQ.abs eval_rescaled_direction))
                       else
                         QQ.div eval_base (QQ.abs eval_rescaled_direction)
                     in
                     let remainder =
                       if integral_direction then
                         QQ.modulo eval_base (QQ.abs eval_rescaled_direction)
                       else QQ.zero
                     in
                     match ( QQ.lt QQ.zero eval_rescaled_direction
                           , integral_direction )
                     with
                     | (true, true) ->
                        if QQ.equal QQ.zero remainder && kind = `Pos then
                          (`Num (QQ.sub num_steps QQ.one), `PlusInfinity)
                        else
                          (`Num num_steps, `PlusInfinity)
                     | (false, true) ->
                        if QQ.equal QQ.zero remainder && kind = `Pos then
                          (`PlusInfinity, `Num (QQ.sub num_steps QQ.one))
                        else
                          (`PlusInfinity, `Num num_steps)
                     | (true, false) ->
                        if QQ.equal QQ.zero remainder && kind = `Pos then
                          (`Num (QQ.div num_steps (QQ.of_int 2)), `PlusInfinity)
                        else
                          (`Num num_steps, `PlusInfinity)
                     | (false, false) ->
                        if QQ.equal QQ.zero remainder && kind = `Pos then
                          (`PlusInfinity, `Num (QQ.div num_steps (QQ.of_int 2)))
                        else
                          (`Num num_steps, `PlusInfinity)
              in
              ( min (max_neg_dirn, curr_num_steps_neg_dirn)
              , min (max_pos_dirn, curr_num_steps_pos_dirn)
              )
            )
            (`PlusInfinity, `PlusInfinity)
            (P.enum_constraints (poly_part plt))
        in
        let translate coeff =
          if QQ.equal QQ.zero coeff then
            None
          else
            Some (V.add integer_point (V.scalar_mul coeff rescaled))
        in
        match (coeff_neg_dirn, coeff_pos_dirn) with
        | (`Num n1), (`Num n2) ->
           BatList.filter_map translate [QQ.negate n1; n2]
        | (`Num n1, `PlusInfinity) ->
           BatList.filter_map translate [QQ.negate n1]
        | (`PlusInfinity, `Num n2) ->
           BatList.filter_map translate [n2]
        | (`PlusInfinity, `PlusInfinity) -> []
      end
   *)

  let polyhedron_of_far_lattice_points ~man ~max_dim m plt =
    (* Strengthen strict inequalities to strict ones *)
    let closed_subpolyhedron =
      P.enum_constraints (poly_part plt)
      |> BatEnum.map (fun (kind, v) ->
             match kind with
             | `Zero | `Nonneg  -> (kind, v)
             | `Pos ->
                let m_val = Linear.evaluate_affine m v in
                let epsilon =
                  if QQ.lt m_val _epsilon then
                    (* test point m does not satisfy t - epsilon >= 0 -- need to
                       choose a smaller value for epsilon than the default. *)
                    QQ.nudge_down ~accuracy:2 m_val
                  else
                    _epsilon
                in
                assert (QQ.lt QQ.zero epsilon);
                (* t > 0 --> t - epsilon >= 0 *)
                (`Nonneg, V.add_term (QQ.negate epsilon) Linear.const_dim v))
      |> P.of_constraints in
    let closed_subpolyhedron_dd = P.dd_of ~man (max_dim + 1) closed_subpolyhedron
    in
    let m_vec =
      let open BatPervasives in
      BatEnum.fold
        (fun v i -> V.add_term (m i) i v)
        V.zero
        (0 -- max_dim)
    in
    let fns =
      let covectors =
        (L.basis (lattice_part plt))
        @ (L.basis (tiling_part plt))
      in
      (* Taking the dot-product with the lattice / tiling constraints
         effectively homogenizes them, since the coefficient
         Linear.const_dim is zero for every point in the primal space. *)
      List.map (fun vec -> V.dot vec) covectors
    in
    let generators =
      BatEnum.map (fun (k, v) ->
          match k with
          | `Vertex ->
             let int_v =
               P.close_lattice_point
                 fns
                 closed_subpolyhedron
                 ~rational:v
                 ~integer:m_vec
                 (max_dim + 1)
             in
             (`Vertex, int_v)
          | `Ray -> (`Ray, v)
          | `Line -> (`Line, v)
        )
        (DD.enum_generators closed_subpolyhedron_dd)
    in
    (DD.of_generators ~man (max_dim + 1) generators)

end

module LocalGlobal: sig

  open Syntax

  val abstract_dd:
    'a context ->
    ?man:Polka.loose Polka.t Apron.Manager.t ->
    max_dim:int ->
    term_of_dim:(int -> 'a arith_term) ->
    ?bottom:DD.closed DD.t option ->
    model_translation:('a Interpretation.interpretation -> 'point1) ->
    local_abstraction:('point1 BatEnum.t -> 'concept1 -> DD.closed DD.t) ->
    [ `Solver of ('a formula -> 'concept1) * 'a Abstract.Solver.t
    | `Source of ('concept1 -> 'a formula) * 'concept1 ] ->
    DD.closed DD.t

end = struct

  open Syntax

  let dump_model_up_to srk term_of_dim max_dim_to_inspect interp =
    let rec evaluate n l =
      if n < 0 then l
      else
        let term = term_of_dim n in
        let l' = (term, Interpretation.evaluate_term interp term) :: l in
        evaluate (n - 1) l'
    in
    logf ~level:`debug "model: @[%a@]@;"
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
         (fun fmt (t, value) ->
           Format.fprintf fmt "(%a, %a)"
             (Syntax.ArithTerm.pp srk) t
             QQ.pp value)
      )
      (evaluate max_dim_to_inspect [])

  let abstract ?(show=(fun _m -> ()))
        (srk: 'a context)
        ~join ~top ~bottom
        ~formula_of_target
        ~model_translation
        ~local_abstraction input =
    let counter = ref 0 in
    let models = ref [] in
    let abstract_model src m =
      match m with
      | `LIRR _ -> assert false
      | `LIRA m ->
         let () = show m in
         models := m :: !models;
         counter := !counter + 1;
         logf ~level:`info "Abstraction loop iteration: %d" !counter;
         let points = BatEnum.map model_translation (BatList.enum !models) in
         let result = local_abstraction points src in
         logf ~level:`info "Abstraction loop iteration %d done" (!counter - 1);
         result
    in
    let (of_model, solver) =
      match input with
      | `Source (formula_of_source, src) ->
         ( abstract_model src
         , Abstract.Solver.make srk ~theory:`LIRA (formula_of_source src) )
      | `Solver (source_of_formula, solver) ->
         ( abstract_model (source_of_formula (Abstract.Solver.get_formula solver))
         , solver )
    in
    let domain =
      Abstract.
      { join
      ; of_model
      ; formula_of = formula_of_target
      ; top
      ; bottom
      }
    in
    Abstract.Solver.abstract solver domain

  let abstract_dd
        (srk: 'a context)
        ?(man = Polka.manager_alloc_loose ())
        ~max_dim
        ~term_of_dim
        ?(bottom = None)
        ~model_translation
        ~local_abstraction input =
    let formula_of_target dd =
      let fml = formula_of_dd srk term_of_dim dd in
      logf ~level:`debug "Blocking %a" (Syntax.Formula.pp srk) fml;
      fml
    in
    let top = P.dd_of ~man (max_dim + 1) P.top in
    let bottom = match bottom with
      | None -> P.dd_of ~man (max_dim + 1) P.bottom
      | Some bottom -> bottom
    in
    let show m = dump_model_up_to srk term_of_dim max_dim m
    in
    abstract ~show srk ~join:DD.join ~top ~bottom ~formula_of_target
      ~model_translation ~local_abstraction input

    (*

  let lift_plt_abstraction ?(solver=None) srk ~term_of_dim local_abs =
    let local_abs' =
      let abstract m phi =
        let ((plt: 'b Plt.t), univ_translation) =
          local_abs.LocalAbstraction.abstract m phi in
        ([plt], univ_translation)
      in
      LocalAbstraction.{abstract}
    in
    let join plts1 plts2 = plts1 @ plts2 in
    let formula_of_target plts =
      let to_block = mk_or srk (List.map (Plt.formula_of_plt srk term_of_dim) plts) in
      logf ~level:`debug "blocking: @[%a@]" (Syntax.Formula.pp srk) to_block;
      to_block
    in
    let top = [Plt.top] in
    let bottom = [] in
    lift_abstraction srk ~solver ~join
      ~formula_of_source:(fun phi -> phi) ~univ_translation:(fun interp -> interp)
      ~formula_of_target ~top ~bottom local_abs'
     *)

end

(*
module UnionPlt : sig

  type 'layout t

  val plt_and_points: 'layout t -> ('layout Plt.t * ) list

  val abstract_to_union_plt:
    'a context -> 'a Syntax.ArithTerm.t array ->
    (('a Syntax.Formula.t, 'a Interpretation.interpretation,
      'layout t, (int -> QQ.t)) Abstraction.t) *
      (int -> 'a Syntax.ArithTerm.t)

end = struct

  val lift_abstraction:
    ?show:('a interpretation -> unit) ->
    ?solver: 'a Abstract.Solver.t option ->
    'a context ->
    join:('concept2 -> 'concept2 -> 'concept2) ->
    formula_of_source:('concept1 -> 'a formula) ->
    univ_translation:('a Interpretation.interpretation -> 'point1) ->
    formula_of_target:('concept2 -> 'a formula) ->
    top:'concept2 ->
    bottom:'concept2 ->
    ('concept1, 'point1, 'concept2, 'point2) LocalAbstraction.t ->
    ('concept1, 'point1, 'concept2, 'point2) Abstraction.t

  type 'layout t = ('layout Plt.t * (int -> QQ.t) list) list

  let adjoin plt_points plts =
    let (plt1, points1) = plt_points in
    List.fold_left
      (fun (plt2, pts2) -> )
      []
      plts


  (* Best-effort join *)
  let join union1 union2 =
    List.fold_left
      (fun plt1 )
      []
      union1


  let abstract_to_union_plt srk terms symbols =
    let curr_term_of_dim = ref IntMap.empty in
    let num_terms = Array.length terms in
    let () =
      Array.iteri
        (fun dim term -> curr_term_of_dim := IntMap.add dim term !curr_term_of_dim)
        terms;
      Syntax.Symbol.Set.iter
        (fun sym ->
          curr_term_of_dim :=
            IntMap.add
              (Syntax.int_of_symbol sym + num_terms)
              (Syntax.mk_const srk sym)
              !curr_term_of_dim
        )
        symbols
    in
    let abstract_plt =
      Plt.abstract_to_standard_plt `ExpandModFloor srk
        ~term_of_new_dims_to_set:(Some curr_term_of_dim)
        terms
        symbols
    in
    let mk_univ_translation term_of_dim =
      fun interp dim ->
      try
        let term = IntMap.find dim term_of_dim in
        Interpretation.evaluate_term interp term
      with
      | Not_found ->
         failwith
           (Format.asprintf "abstract_to_union_plt: cannot evaluate dimension %d" dim)
    in
    let alpha interp phi =
      let plt = LocalAbstraction.apply abstract_plt interp phi in
      let univ_translation = mk_univ_translation !curr_term_of_dim in
      ((plt, univ_translation interp), univ_translation)
    in
    let term_of_dim dim =
      try IntMap.find dim !curr_term_of_dim
      with
      | Not_found ->
         failwith
           (Format.asprintf "abstract_to_union_plt: cannot find a term at dimension %d" dim)
    in
    let join plts1 plts2 = plts1 @ plts2 in
    let formula_of_target plts =
      let to_block =
        mk_or srk (List.map (Plt.formula_of_plt srk term_of_dim) plts) in
      logf ~level:`debug "blocking: @[%a@]" (Syntax.Formula.pp srk) to_block;
      to_block
    in
    let top = [Plt.top] in
    let bottom = [] in
    let abstract = LocalGlobal.lift_abstraction srk ~join
                     ~formula_of_source:(fun phi -> phi)
                     ~formula_of_target
                     ~top ~bottom
                     LocalAbstraction.{abstract=alpha}
    in
    (abstract, term_of_dim)

end
 *)

module Ddify: sig

  val abstract:
    man:DD.closed Apron.Manager.t ->
    max_dim_in_projected: int ->
    (P.t, int -> QQ.t, DD.closed DD.t, int -> QQ.t) LocalAbstraction.t

end = struct

  let abstract ~man ~max_dim_in_projected =
    let abstract _m p =
      logf ~level:`debug "DDifying @[%a@] in ambient dimension %d" (P.pp pp_dim) p
        (max_dim_in_projected + 1);
      let dd = P.dd_of ~man (max_dim_in_projected + 1) p in
      let () = logf ~level:`debug "DDified@;" in
      (dd, (fun m -> m))
    in
    LocalAbstraction.{ abstract }

end

module LoosWeispfenning: sig

  val abstract_lw:
    elim: (int -> bool) ->
    (P.t, int -> QQ.t, P.t, int -> QQ.t) LocalAbstraction.t

end = struct

  let abstract_lw ~elim =
    let abstract m p =
      let to_project =
        BatList.of_enum (P.enum_constraints p)
        |> collect_dimensions (fun (_, v) -> v) (fun _ -> true)
        |> IntSet.filter elim
        |> IntSet.to_list
      in
      logf ~level:`debug "abstract_lw: eliminating dimensions @[%a@] from @[%a@]"
        (Format.pp_print_list ~pp_sep:(fun fmt _ -> Format.fprintf fmt ", ")
           Format.pp_print_int)
        to_project
        (P.pp pp_dim) p;
      let abstracted = P.local_project m to_project p in
      logf ~level:`debug "abstract_lw: abstracted.@\n";
      test_point_in_polyhedron "abstract_lw" m
        (BatList.of_enum (P.enum_constraints abstracted));
      let restricted m dim =
        if elim dim then
          failwith
            (Format.asprintf
               "abstract_lw: Dimension %d has been eliminated" dim)
        else m dim
      in
      (abstracted, restricted)
    in
    LocalAbstraction.{ abstract }

end

module MixedCooper: sig

  (* Let PLT(x, Y) be a PLT in dimensions RR^{x \cup Y}.
     [round_up: QQ^{x \cup Y} -> Term(Y) -> Term(Y)] is a function such that
     for all terms [t], [t'] and [m] in PLT(x, Y),
     [round_up m t = t'] only if m(t(y)) <= m(t'(y)) <= m(x).

     If [round_up] has finite image for each [t], [abstract_cooper] is a
     local abstraction that has finite image.
   *)

  (* Dimensions to be eliminated must appear in an Int literal. *)
  val abstract_cooper:
    elim: (int -> bool) ->
    round_up: ((int -> QQ.t) -> V.t -> V.t) ->
    ('layout Plt.t, int -> QQ.t, 'layout Plt.t, int -> QQ.t) LocalAbstraction.t

end = struct

  let substitute_for_in v dim w =
    let (coeff, w') = V.pivot dim w in
    V.add (V.scalar_mul coeff v) w'

  let virtual_sub_p vt dim (kind, v) =
    let (coeff, _) = V.pivot dim v in
    let result =
      if QQ.equal coeff QQ.zero then
        Some (kind, v)
      else
        match (vt, QQ.lt QQ.zero coeff) with
        | (`PlusInfinity, true) ->
           begin match kind with
           | `Zero -> invalid_arg "abstract_cooper: invalid selection of +infty"
           | `Nonneg
             | `Pos -> None
           end
        | (`MinusInfinity, false) ->
           begin match kind with
           | `Zero -> invalid_arg "abstract_cooper: invalid selection of -infty"
           | `Nonneg
             | `Pos -> None
           end
        | (`PlusInfinity, false) ->
           invalid_arg "abstract_cooper: invalid selection of +infty"
        | (`MinusInfinity, true) ->
           invalid_arg "abstract_cooper: invalid selection of -infty"
        | (`Term t, _) ->
           Some (kind, substitute_for_in t dim v)
    in
    logf ~level:`trace "virtual substitution: substituting %a for %d in @[%a@]"
      (fun fmt vt -> match vt with
                     | `PlusInfinity -> Format.fprintf fmt "+infty"
                     | `MinusInfinity -> Format.fprintf fmt "-infty"
                     | `Term t -> pp_vector fmt t
      ) vt
      dim pp_pconstr (kind, v);
    logf ~level:`trace "virtual substitution: result is @[%a@]"
      (Format.pp_print_option
         ~none:(fun fmt _ -> Format.fprintf fmt "None") pp_pconstr)
      result;
    result

  (* TODO: Verify that there is only one possibility in the range
     [0, lcm of denom)
   *)
  let virtual_sub_l modulus m vt dim v =
    let (coeff, _) = V.pivot dim v in
    if QQ.equal coeff QQ.zero then Some v
    else
      match vt with
      | `PlusInfinity
        | `MinusInfinity ->
         let delta = QQ.modulo (m dim) modulus in
         Some (substitute_for_in (V.of_term delta Linear.const_dim) dim v)
      | `Term t ->
         Some (substitute_for_in t dim v)

  let virtual_sub substitution_fn vt dim constraints =
    let result = BatEnum.empty () in
    List.iter
      (fun constr ->
        begin match substitution_fn vt dim constr with
        | None -> ()
        | Some atom -> BatEnum.push result atom
        end
      )
      constraints;
    BatList.of_enum result |> List.rev

  let glb_for dim p m =
    let has_upper_bound = ref false in
    let argmax (kind1, lower_bound1, b1) (kind2, lower_bound2, b2) =
      if QQ.lt b1 b2 then (kind2, lower_bound2, b2)
      else if QQ.lt b2 b1 then (kind1, lower_bound1, b1)
      else
        begin
          match (kind1, kind2) with
          | (`Nonneg, `Pos)
            | (`Nonneg, `Zero)
            | (`Pos, `Zero) -> (kind2, lower_bound2, b2)
          | (_, _) -> (kind1, lower_bound1, b1)
        end
    in
    let glb = ref None in
    let set_glb lb =
      logf ~level:`debug "glb_for: setting lower bound @[%a@]"
        pp_vector (let (_, lower_bound, _) = lb in lower_bound);
      glb := Some lb
    in
    List.iter
      (fun (kind, v) ->
        logf ~level:`debug "glb_for: @[%a@]"
          pp_pconstr (kind, v);
        let (coeff, w) = V.pivot dim v in
        if QQ.equal QQ.zero coeff then
          ()
        else
          let lower_bound = V.scalar_mul (QQ.negate (QQ.inverse coeff)) w in
          let b = Linear.evaluate_affine m lower_bound in
          if QQ.lt QQ.zero coeff then
            begin
              let () =
                match kind with
                | `Zero -> has_upper_bound := true
                | _ -> ()
              in
              match !glb with
              | None ->
                 set_glb (kind, lower_bound, b)
              | Some (kind0, lower_bound0, b0) ->
                 set_glb (argmax (kind0, lower_bound0, b0) (kind, lower_bound, b))
            end
          else
            begin
              has_upper_bound := true;
              match kind with
              | `Zero ->
                 begin match !glb with
                 | None ->
                    set_glb (kind, lower_bound, b)
                 | Some (kind0, lower_bound0, b0) ->
                    set_glb (argmax (kind0, lower_bound0, b0) (kind, lower_bound, b))
                 end
              | _ -> ()
            end
      )
      p;
    (!glb, !has_upper_bound)

  let select_term elim_dim modulus round_up (kind, lower) m =
    let rounded = round_up m lower in
    let lower_point = Linear.evaluate_affine m lower in
    let rounded_point = Linear.evaluate_affine m rounded in
    let remainder = QQ.modulo (QQ.sub (m elim_dim) rounded_point) modulus in
    let delta = match (kind, QQ.equal QQ.zero remainder) with
      | (`Zero, _)
        | (`Nonneg, _)
        | (`Pos, false) -> remainder
      | (`Pos, true) ->
         assert (QQ.leq lower_point rounded_point);
         if QQ.lt lower_point rounded_point then QQ.zero
         else modulus
    in
    let term = V.add_term delta Linear.const_dim rounded in
    logf ~level:`debug
      "select_term: calculating term: value of elim dimension %d = %a,
       value of lower bound = %a, value of rounded = %a,
       modulus = %a, remainder = %a, chosen point = %a@;"
      elim_dim
      QQ.pp (m elim_dim)
      QQ.pp (Linear.evaluate_affine m lower)
      QQ.pp (Linear.evaluate_affine m rounded)
      QQ.pp modulus
      QQ.pp remainder
      QQ.pp (QQ.add rounded_point delta);
    logf ~level:`debug
      "select_term: lower bound term: @[%a@]@; rounded term: @[%a@]@; selected term: @[%a@]"
      pp_vector lower pp_vector rounded pp_vector term;
    term

  let cooper_one round_up elim_dim m (p, l, t) =
    logf ~level:`debug "cooper_one: eliminating %d" elim_dim;
    let gcd_coeffs =
      List.fold_left (fun gcd v -> QQ.gcd (V.coeff elim_dim v) gcd) QQ.zero
        (List.rev_append l t)
    in
    let modulus =
      (* Better than just lcm of denoms, e.g., smaller steps for coeffs 5/2, 5/3 *)
      assert (not (QQ.equal QQ.zero gcd_coeffs));
      QQ.inverse gcd_coeffs
    in
    let select_term = select_term elim_dim modulus round_up in
    let term_selected =
      match glb_for elim_dim p m with
      | (_, false) ->
         logf ~level:`debug "abstract_cooper: selecting +infty";
         `PlusInfinity
      | (None, _) ->
         logf ~level:`debug "abstract_cooper: selecting -infty";
         `MinusInfinity
      | (Some (kind, term, _value), true) ->
         logf ~level:`debug "abstract_cooper: selecting term based on @[%a@]"
           pp_pconstr (kind, V.add_term QQ.one elim_dim (V.negate term));
         `Term (select_term (kind, term) m)
    in
    let polyhedron = virtual_sub virtual_sub_p term_selected elim_dim p in
    let virtual_sub_lattice = virtual_sub (virtual_sub_l modulus m) in
    let lattice = virtual_sub_lattice term_selected elim_dim l in
    let tiling = virtual_sub_lattice term_selected elim_dim t in
    test_point_in_polyhedron "cooper_one" m polyhedron;
    test_point_in_lattice `IsInt "cooper_one" m lattice;
    test_point_in_lattice `NotInt "cooper_one" m tiling;
    (polyhedron, lattice, tiling)

  let abstract_cooper_ ~elim ~round_up m plt =
    let open Plt in
    let p = P.enum_constraints (Plt.poly_part plt) |> BatList.of_enum in
    let l = L.basis (Plt.lattice_part plt) in
    let t = L.basis (Plt.tiling_part plt) in
    let elim_dimensions =
      Plt.constrained_dimensions plt
      |> IntSet.filter elim
    in
    logf ~level:`debug "abstract_cooper: eliminating dimensions @[%a@] from@\n"
      IntSet.pp elim_dimensions;
    log_plt_constraints ~level:`debug "plt: " (p, l, t);
    let (projected_p, projected_l, projected_t) =
      IntSet.fold
        (fun elim_dim (p, l, t) ->
          cooper_one round_up elim_dim m (p, l, t)
        )
        elim_dimensions
        (p, l, t)
    in
    logf ~level:`debug "abstract_cooper: abstracted";
    mk_plt ~poly_part:(Polyhedron.of_constraints (BatList.enum projected_p))
      ~lattice_part:(L.hermitize projected_l)
      ~tiling_part:(L.hermitize projected_t)

  let abstract_cooper ~elim ~round_up =
    let restricted m dim =
      if elim dim then
        failwith
          (Format.asprintf
             "abstract_lw: Dimension %d has been eliminated" dim)
      else m dim
    in
    LocalAbstraction.
    {
      abstract =
        (fun m plt -> (abstract_cooper_ ~elim ~round_up m plt, restricted))
    }

end

module LwCooper: sig

  (** This abstraction does real projection for real-valued dimensions and
      Cooper projection for integer-valued dimensions.
   *)
  val abstract_lw_cooper:
    elim: (int -> bool) ->
    ('layout Plt.t, int -> QQ.t, 'layout Plt.t, int -> QQ.t) LocalAbstraction.t

end = struct

  let abstract_lw_cooper_ ~elim m plt =
    let p = P.enum_constraints (Plt.poly_part plt) |> BatList.of_enum in
    let l = L.basis (Plt.lattice_part plt) in
    let t = L.basis (Plt.tiling_part plt) in
    log_plt_constraints ~level:`debug "abstract_lw_cooper: abstracting" (p, l, t);
    let elim_dimensions =
      Plt.constrained_dimensions plt |> IntSet.filter elim in
    let integer_dimensions =
      IntSet.union
        (collect_dimensions (fun v -> v) (fun _ -> true) l)
        (collect_dimensions (fun v -> v) (fun _ -> true) t)
    in
    let (int_dims_to_elim, real_dims_to_elim) =
      IntSet.partition (fun dim -> IntSet.mem dim integer_dimensions)
        elim_dimensions
    in
    let abstract_lw =
      LoosWeispfenning.abstract_lw
        ~elim:(fun dim -> IntSet.mem dim real_dims_to_elim)
    in
    let abstract_cooper =
      MixedCooper.abstract_cooper
        ~elim:(fun dim -> IntSet.mem dim int_dims_to_elim)
        ~round_up:(fun _ v -> v)
    in
    let local_abstraction =
      Plt.abstract_poly_part abstract_lw
      |> LocalAbstraction.compose abstract_cooper
    in
    let (plt, univ_translation) =
      LocalAbstraction.apply2 local_abstraction m plt in
    let projected_p = Plt.poly_part plt in
    let projected_l = Plt.lattice_part plt in
    let projected_t = Plt.tiling_part plt in
    log_plt_constraints ~level:`debug "abstract_lw_cooper: abstracted"
      ( BatList.of_enum (P.enum_constraints projected_p)
      , L.basis projected_l
      , L.basis projected_t);
    (plt, univ_translation)

  let abstract_lw_cooper ~elim =
    LocalAbstraction.
    {
      abstract = abstract_lw_cooper_ ~elim
    }

end

module SubspaceCone : sig

  val abstract_sc:
    man:DD.closed Apron.Manager.t ->
    max_dim_in_projected: int ->
    diversify_in_dd: bool ->
    ('layout Plt.t, int -> QQ.t, DD.closed DD.t, int -> QQ.t) LocalAbstraction.t

end = struct

  module LW = LoosWeispfenning

  let close_constraints constrs =
    constrs
    |> BatEnum.map
         (fun (kind, v) ->
           match kind with
           | `Zero | `Nonneg -> (kind, v)
           | `Pos -> (`Nonneg, v)
         )

  let abstract_sc ~man ~max_dim_in_projected ~diversify_in_dd =
    let abstract m plt =
      logf ~level:`debug "abstract_sc...";
      let abstract_lw =
        let abstract =
          LW.abstract_lw ~elim:(fun dim -> dim > max_dim_in_projected)
          |> LocalAbstraction.compose
               (Ddify.abstract ~man ~max_dim_in_projected)
        in
        LocalAbstraction.apply abstract m
      in
      let closed_p = close_constraints (P.enum_constraints (Plt.poly_part plt))
                     |> P.of_constraints in
      let l_constraints = L.basis (Plt.lattice_part plt) in
      logf ~level:`debug "abstract_sc: lattice constraints: @[%a@]"
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
           pp_vector)
        l_constraints;
      let polyhedron_abstraction = abstract_lw closed_p in
      let subspace_constraints =
        List.map
          (fun v ->
            ( `Zero
            , V.add_term
                (QQ.negate (Linear.evaluate_affine m v))
                Linear.const_dim
                v
            )
          )
          l_constraints
      in
      let subspace_abstraction =
        match subspace_constraints with
        | [] -> polyhedron_abstraction
        | _ ->
           BatEnum.append (BatList.enum subspace_constraints)
             (P.enum_constraints closed_p)
           |> P.of_constraints
           |> abstract_lw
      in
      let subspace_abstraction =
        match diversify_in_dd with
        | false -> subspace_abstraction
        | true ->
           let underapprox_plt =
             LocalAbstraction.apply
               (LwCooper.abstract_lw_cooper
                  ~elim:(fun dim -> dim > max_dim_in_projected))
               m
               plt
           in
           let far_lattice_points_and_cone =
             Plt.polyhedron_of_far_lattice_points ~man
               ~max_dim:max_dim_in_projected
               m underapprox_plt
           in
           DD.join subspace_abstraction far_lattice_points_and_cone
      in
      logf ~level:`debug "abstract_sc: combining...";
      let recession_cone =
        DD.enum_generators polyhedron_abstraction
        |> BatEnum.filter (fun (kind, _) -> kind = `Ray || kind = `Line)
      in
      let dd = BatEnum.append (DD.enum_generators subspace_abstraction)
                 recession_cone
               |> DD.of_generators ~man (max_dim_in_projected + 1) in
      logf ~level:`debug "abstract_sc: combined dd = @[%a@]"
        (DD.pp pp_dim) dd;
      let restricted m dim =
        if dim > max_dim_in_projected
        then failwith "abstract_sc: Dimension has been eliminated"
        else m dim
      in
      (dd, restricted)
    in
    LocalAbstraction.{ abstract }

end

module IntFracProjection: sig

  val abstract_intfrac_plt:
    elim:(int -> bool) ->
    (Plt.intfrac Plt.t, int -> QQ.t, Plt.intfrac Plt.t, int -> QQ.t)
      LocalAbstraction.t

end = struct

  module LW = LoosWeispfenning

  let abstract_intfrac_plt ~elim =
    let abstract m plt =
      logf ~level:`debug "abstract_intfrac_plt...";
      let must_be_integral dim =
        (* If dim is supported in any positive integrality constraint,
           dim itself is.
         *)
        L.member (V.of_term QQ.one dim) (Plt.lattice_part plt) in
      let abstract_lw =
        LW.abstract_lw
          ~elim:(fun dim ->
            elim dim &&
              (* If an integrality assumption for an integer dimension is
                 not used, it is sound to treat it as real-valued.
               *)
              not (must_be_integral dim)) in
      let abstract_cooper =
        MixedCooper.abstract_cooper
          ~elim:(fun dim -> elim dim && must_be_integral dim)
          ~round_up:(fun m t -> let (t', _, _) = Plt.ceiling_int_frac m t in t')
      in
      LocalAbstraction.apply2
        (Plt.abstract_poly_part abstract_lw
         |> LocalAbstraction.compose abstract_cooper)
        m plt
    in
    LocalAbstraction.{abstract}
end


module AbstractTerm: sig

  val mk_sc_abstraction:
    man:DD.closed Apron.Manager.t ->
    diversify_in_dd:bool ->
    [ `ExpandModFloor | `NoExpandModFloor ] ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> Q.t)
      LocalAbstraction.t

  (*
  val mk_sc_abstraction_with_acceleration:
    [`DiversifyInOriginal of int | `DiversifyInDD | `DiversifyInBoth of int] ->
    man:DD.closed Apron.Manager.t ->
    [ `ExpandModFloor | `NoExpandModFloor ] ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> Q.t)
      LocalAbstraction.t
   *)

  val mk_lw_cooper_abstraction:
    [ `ExpandModFloor | `NoExpandModFloor ] ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, Plt.standard Plt.t, int -> Q.t)
      LocalAbstraction.t

  val mk_intfrac_abstraction:
    man:DD.closed Apron.Manager.t ->
    [ `ExpandModFloor | `NoExpandModFloor ] ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> Q.t)
      LocalAbstraction.t

  (*
  val mk_intfrac_abstraction_with_acceleration:
    man:DD.closed Apron.Manager.t -> ?window:int ->
    [ `ExpandModFloor | `NoExpandModFloor ] ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> Q.t)
      LocalAbstraction.t
   *)

end = struct

  (*
  let model_to_vector dimensions m =
    IntSet.fold (fun dim v ->
      if dim <> Linear.const_dim then V.add_term (m dim) dim v
      else v)
    dimensions
    V.zero

  let abstract_multiple_points local_abs plt points =
    match points with
    | [] -> invalid_arg "at least one point is needed"
    | [point] -> LocalAbstraction.apply2 local_abs point plt
    | point1 :: point2 :: _ ->
       let dimensions = Plt.constrained_dimensions plt in
       let integer_point = model_to_vector dimensions point1 in
       let rational_point = model_to_vector dimensions point2 in
       let points =
         let direction = V.sub rational_point integer_point in
         Plt.extrapolate ~integer_point ~direction plt
       in
       log_plt_constraints ~level:`debug "diversifying within"
         ( BatList.of_enum (P.enum_constraints (Plt.poly_part plt))
         , L.basis (Plt.lattice_part plt)
         , L.basis (Plt.tiling_part plt));
       logf ~level:`debug "diversified points: @[%a@]@\n@[%a@]@;"
         pp_vector integer_point
         (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
            pp_vector)
         points;
       let points = List.map (fun v dim -> V.coeff dim v) points in
       let (dd1, univ_translation) =
         LocalAbstraction.apply2 local_abs point1 plt in
       let dd = List.map (fun m -> LocalAbstraction.apply local_abs m plt)
                  points
                |> List.fold_left DD.join dd1
       in
       (dd, univ_translation)

  let abstract_multiple_models
        window abstract_to_plt abstract_to_dd models phi =
    let end_to_end = abstract_to_plt |> LocalAbstraction.compose abstract_to_dd in
    match models with
    | [] -> invalid_arg "at least one model is needed"
    | [interp] -> LocalAbstraction.apply2 end_to_end interp phi
    | interp1 :: interp2 ->
       let (plt1, univ_translation1) =
         LocalAbstraction.apply2 abstract_to_plt interp1 phi in
       let point = univ_translation1 interp1 in
       let (dd1, univ_translation2) =
         LocalAbstraction.apply2 abstract_to_dd point plt1 in
       let dimensions = Plt.constrained_dimensions plt1 in
       let integer_point = model_to_vector dimensions point in
       let history = BatList.take window interp2 in
       let rational_points =
         List.map (fun interp -> univ_translation1 interp
                                 |> model_to_vector dimensions)
           history
       in
       let new_points =
         List.fold_left
           (fun accumulated rational_point ->
             let direction = V.sub rational_point integer_point
             in
             List.rev_append (Plt.extrapolate ~integer_point ~direction plt1)
               accumulated)
           []
           rational_points
       in
       let unique_points =
         BatList.unique ~eq:V.equal (integer_point :: new_points)
       in
       log_plt_constraints ~level:`debug "diversifying within"
         ( BatList.of_enum (P.enum_constraints (Plt.poly_part plt1))
         , L.basis (Plt.lattice_part plt1)
         , L.basis (Plt.tiling_part plt1));
       logf ~level:`debug "diversified points: @[%a@]@\n@[%a@]@;"
         pp_vector integer_point
         (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
            pp_vector)
         unique_points;
       let points =
         List.map (fun v dim -> V.coeff dim v) unique_points
       in
       let dd = List.map (fun m -> LocalAbstraction.apply abstract_to_dd m plt1)
                  points
                |> List.fold_left DD.join dd1
       in
       (dd, fun interp -> univ_translation2 (univ_translation1 interp))
   *)

  let mk_sc_abstraction ~man ~diversify_in_dd
        expand_mod_floor srk terms symbols =
    let num_terms = Array.length terms in
    let plt_abstraction =
      Plt.abstract_to_standard_plt expand_mod_floor srk terms symbols
    in
    let sc_abstraction =
      SubspaceCone.abstract_sc ~man
        ~max_dim_in_projected:(num_terms - 1)
        ~diversify_in_dd
    in
    plt_abstraction |> LocalAbstraction.compose sc_abstraction

  (*
  let mk_standard_acceleration term_of_new_dims_to_set
        standard_plt_to_term_dd window
        expand_mod_floor srk terms symbols =
    let models = ref [] in
    let plt_abstraction =
      Plt.abstract_to_standard_plt ~term_of_new_dims_to_set
        expand_mod_floor srk terms symbols
    in
    let abstract interp phi =
      models := interp :: !models;
      BatList.iter
        (fun interp ->
          assert (Interpretation.evaluate_formula interp phi)
        ) !models;
      abstract_multiple_models window plt_abstraction standard_plt_to_term_dd !models phi
    in
    LocalAbstraction.{abstract}

  let mk_sc_abstraction_with_acceleration how ~man
        expand_mod_floor srk terms symbols =
    let diversify_in_dd =
      match how with
      | `DiversifyInOriginal _ -> false
      | `DiversifyInDD -> true
      | `DiversifyInBoth _ -> true
    in
    let window =
      match how with
      | `DiversifyInOriginal window -> window
      | `DiversifyInDD -> 1
      | `DiversifyInBoth window -> window
    in
    let sc_abstraction =
      SubspaceCone.abstract_sc ~man ~max_dim_in_projected:(Array.length terms - 1)
        ~diversify_in_dd
    in

    let term_of_dim = ref IntMap.empty in
    let () =
      let num_terms = Array.length terms in
      Array.iteri (fun dim term -> term_of_dim := IntMap.add dim term !term_of_dim)
        terms;
      Syntax.Symbol.Set.iter
        (fun sym ->
          term_of_dim := IntMap.add (Syntax.int_of_symbol sym + num_terms)
                           (Syntax.mk_const srk sym)
                           !term_of_dim)
        symbols
    in

    mk_standard_acceleration (Some term_of_dim)
      sc_abstraction
      window
      expand_mod_floor srk terms symbols

   *)

  let mk_lw_cooper_abstraction expand_mod_floor srk terms symbols =
    let num_terms = Array.length terms in
    let local_abs =
      let open LocalAbstraction in
      logf ~level:`debug "convex_hull_lw_cooper...";
      Plt.abstract_to_standard_plt expand_mod_floor srk terms symbols
      |> compose (LwCooper.abstract_lw_cooper ~elim:(fun dim -> dim >= num_terms))
    in
    local_abs

  let mk_map_intfrac_to_original_dimensions man terms =
    let num_terms = Array.length terms in
    let Plt.{start_of_term_int_frac; start_of_symbol_int_frac} =
      Plt.int_frac_layout ~num_terms
    in
    let defining_equations =
      let equations = BatEnum.empty () in
      let sum dim = V.of_term QQ.one dim |> V.add_term QQ.one (dim + 1)
      in
      let rec loop dim intfrac_dim =
        if dim < num_terms then
          begin
            BatEnum.push equations
              (`Zero, V.of_term (QQ.of_int (-1)) dim |> V.add (sum intfrac_dim));
            loop (dim + 1) (intfrac_dim + 2)
          end
        else
          ()
      in
      loop 0 start_of_term_int_frac;
      (BatList.of_enum equations)
    in
    let map_intfrac _m dd =
      let int_frac_term_dimensions =
        BatList.of_enum
          BatEnum.(num_terms --^ start_of_symbol_int_frac)
      in
      let mapped_dd = DD.meet_constraints dd defining_equations
                      |> DD.project int_frac_term_dimensions
                      |> DD.enum_constraints
                      |> DD.of_constraints_closed ~man num_terms
      in
      logf ~level:`debug "DD in original dimensions: @[%a@]@;"
        (DD.pp pp_dim) mapped_dd;
      ( mapped_dd
      , fun m dim ->
        if dim >= 0 && dim < num_terms then m dim
        else
          failwith
            (Format.asprintf
               "convex_hull_intfrac: dimension %d has been eliminated" dim)
      )
    in
    map_intfrac

  let mk_intfrac_abstraction ~man
        expand_mod_floor srk terms symbols =
    let map_intfrac = mk_map_intfrac_to_original_dimensions man terms in
    let Plt.{start_of_symbol_int_frac; _} =
      Plt.int_frac_layout ~num_terms:(Array.length terms)
    in
    let max_dim_in_projected = start_of_symbol_int_frac - 1 in
    let convexify m plt =
      ( Plt.polyhedron_of_far_lattice_points
          ~man ~max_dim:max_dim_in_projected m plt
      , fun m -> m)
    in
    let local_abs =
      let open LocalAbstraction in
      Plt.abstract_to_intfrac_plt expand_mod_floor srk terms symbols
      |> compose
           (IntFracProjection.abstract_intfrac_plt
              ~elim:(fun dim -> dim > max_dim_in_projected))
      (*
      |> compose
           (SubspaceCone.abstract_sc ~man ~max_dim_in_projected
              ~diversify_in_dd:false)
       *)
      |> compose { abstract = convexify }
      |> compose { abstract = map_intfrac }
    in
    local_abs

  (*
  let mk_intfrac_abstraction_with_acceleration ~man
        ?(window=1) expand_mod_floor srk terms symbols =
    let map_intfrac = mk_map_intfrac_to_original_dimensions man terms in
    let Plt.{start_of_symbol_int_frac; _} =
      Plt.int_frac_layout ~num_terms:(Array.length terms)
    in
    let max_dim_in_projected = start_of_symbol_int_frac - 1 in
    let open LocalAbstraction in
    let abstract_to_plt =
      Plt.abstract_to_intfrac_plt expand_mod_floor srk terms symbols
    in
    let abstract_to_dd =
      IntFracProjection.abstract_intfrac_plt
        ~elim:(fun dim -> dim > max_dim_in_projected)
      |> compose
           (SubspaceCone.abstract_sc ~man ~max_dim_in_projected
              ~diversify_in_dd:false)
      |> compose { abstract = map_intfrac }
    in
    let models = ref [] in
    let abstract interp phi =
      models := interp :: !models;
      BatList.iter
        (fun interp ->
          assert (Interpretation.evaluate_formula interp phi)
        ) !models;
      abstract_multiple_models window abstract_to_plt abstract_to_dd !models phi
    in
    LocalAbstraction.{abstract}
   *)

end

type standard = Plt.standard
type intfrac = Plt.intfrac
type 'a plt = 'a Plt.t

let formula_of_plt = Plt.formula_of_plt

let mk_term_of_dim terms dim =
  let num_terms = Array.length terms in
  if dim >= 0 && dim < num_terms then terms.(dim)
  else failwith (Format.asprintf "term_of_dim: %d" dim)

type abstraction_algorithm =
  | SubspaceCone of [`Standard | `WithHKMMZCone]
  | IntFrac of [`Standard ]
  | LwCooperHKMMZCone
  | ProjectImplicant of
      [ `AssumeReal of [`FullProject | `Lw]
      | `AssumeInt of [ `HullThenProject of [`GomoryChvatal | `Normaliz]
                      | `ProjectThenHull of [`GomoryChvatal | `Normaliz]
                      ]
      ]

let sharpen_strict_inequalities_assuming_integrality p =
  let cnstrnts = BatEnum.empty () in
  BatEnum.iter (fun (kind, v) ->
      match kind with
      | `Pos ->
         let sharpened =
           V.scalar_mul (QQ.of_zz (V.common_denominator v)) v
           |> V.add_term (QQ.of_int (-1)) Linear.const_dim
         in
         BatEnum.push cnstrnts (`Nonneg, sharpened)
      | _ -> BatEnum.push cnstrnts (kind, v)
    )
    (P.enum_constraints p);
  cnstrnts

let integer_hull_plt_assuming_integrality ~man hull_alg plt =
  let lattice_basis =
    IntLattice.basis (Plt.lattice_part plt) in
  let () =
    if (IntLattice.basis (Plt.tiling_part plt) = []) then ()
    else failwith "Negative IsInt not handled; use [Syntax.eliminate_floor_mod_div_int]."
  in
  let max_dim =
    let dimensions =
      collect_dimensions (fun v -> v) (fun _ -> true) lattice_basis
    in
    match IntSet.max_elt_opt dimensions with
    | Some dim -> dim
    | None -> Linear.const_dim
  in
  let (cnstrnts, substitutions) =
    let cnstrnts =
      P.enum_constraints (Plt.poly_part plt) in
    let substitution = ref IntMap.empty in
    let free_dim = ref (max_dim + 1) in
    List.iter
      (fun v ->
        BatEnum.push cnstrnts (`Zero, V.add_term (QQ.of_int (-1)) !free_dim v);
        substitution := IntMap.add !free_dim v !substitution;
        free_dim := !free_dim + 1
      )
      lattice_basis;
    (cnstrnts, !substitution)
  in
  let hull =
    let image =
      P.project_dd (BatEnum.(0 -- max_dim) |> BatList.of_enum)
        (P.of_constraints cnstrnts)
    in
    match hull_alg with
    | `GomoryChvatal ->
       P.integer_hull `GomoryChvatal image
    | `Normaliz ->
       P.integer_hull `Normaliz image
  in
  let substitute substitutions w =
    V.fold (fun dim coeff v ->
        if dim = Linear.const_dim then
          V.add_term coeff dim v
        else
          match IntMap.find_opt dim substitutions with
          | Some v1 -> V.add v (V.scalar_mul coeff v1)
          | None -> failwith "cannot find dimension when applying inverse"
      )
      w
      V.zero
  in
  let hull =
    BatEnum.map
      (fun (kind, w) ->
        (kind, substitute substitutions w)
      )
      (P.enum_constraints hull)
    |> P.of_constraints
  in
  logf ~level:`debug
    "integer_hull_plt_assuming_integrality: max_dim: %d@;" max_dim;
  logf ~level:`debug
    "integer_hull_plt_assuming_integrality: hull: @[%a@]" (P.pp pp_dim) hull;
  P.dd_of ~man (max_dim + 1) hull

let local_abstraction_of_lira_model how ~man srk terms symbols =
  let local_abs =
    match how with
    | SubspaceCone `Standard ->
       AbstractTerm.mk_sc_abstraction ~man ~diversify_in_dd:false
         `ExpandModFloor srk terms symbols
    | SubspaceCone `WithHKMMZCone ->
       AbstractTerm.mk_sc_abstraction ~man ~diversify_in_dd:true
         `ExpandModFloor srk terms symbols
    | IntFrac `Standard ->
       AbstractTerm.mk_intfrac_abstraction ~man `ExpandModFloor srk terms
         symbols
    | LwCooperHKMMZCone ->
       let abs = AbstractTerm.mk_lw_cooper_abstraction `ExpandModFloor
                   srk terms symbols in
       let expand m plt =
         ( Plt.polyhedron_of_far_lattice_points
             ~man ~max_dim:(Array.length terms - 1) m plt
         , fun m -> m )
       in
       abs
       |> LocalAbstraction.compose { abstract = expand }
    | ProjectImplicant type_assumption ->
       let univ_translation m dim =
         if dim < 0 || dim >= Array.length terms then
           invalid_arg (Format.asprintf "dimension %d cannot be interpreted" dim)
         else m dim
       in
       let adjoin_translation f = (fun m phi -> (f m phi, univ_translation)) in
       let project_plt m plt =
         let p = Plt.poly_part plt in
         let max_dim_in_p = P.max_constrained_dim p in
         begin match type_assumption with
         | `AssumeReal `FullProject ->
            let dimensions_to_eliminate =
              BatEnum.(Array.length terms -- max_dim_in_p) |> BatList.of_enum
            in
            P.project_dd dimensions_to_eliminate p
            |> P.dd_of ~man (Array.length terms)
         | `AssumeReal `Lw ->
            logf ~level:`debug "convex_hull_lw...";
            LocalAbstraction.apply
              (LoosWeispfenning.abstract_lw ~elim:(fun dim -> dim >= Array.length terms))
              m p
            |> P.dd_of ~man (Array.length terms)
         | `AssumeInt how ->
            let dimensions_to_eliminate =
              BatEnum.(Array.length terms -- max_dim_in_p) |> BatList.of_enum
            in
            begin match how with
            | `HullThenProject hull_alg ->
               begin match hull_alg with
               | `GomoryChvatal ->
                  let cnstrnts =
                    sharpen_strict_inequalities_assuming_integrality p in
                  P.of_constraints cnstrnts
                  |> P.dd_of ~man (max_dim_in_p + 1)
                  |> DD.integer_hull
                  |> DD.project dimensions_to_eliminate
                  |> DD.enum_constraints
                  |> DD.of_constraints_closed ~man (Array.length terms)
               | `Normaliz ->
                  P.integer_hull `Normaliz p
                  |> P.dd_of ~man (max_dim_in_p + 1)
                  |> DD.project dimensions_to_eliminate
                  |> DD.enum_constraints
                  |> DD.of_constraints_closed ~man (Array.length terms)
               end
            | `ProjectThenHull hull_alg ->
               let elim dim = dim >= Array.length terms in
               let round_up _m v = v in
               let sharpened_plt =
                 Plt.abstract_poly_part
                   {abstract =
                      (fun _m p ->
                        ( sharpen_strict_inequalities_assuming_integrality p
                          |> P.of_constraints
                        , fun m -> m))
                   }
                 |> (fun abs -> LocalAbstraction.apply abs m plt)
               in
               let local_projection =
                 LocalAbstraction.apply
                   (MixedCooper.abstract_cooper ~elim ~round_up) m sharpened_plt in
               let p = P.enum_constraints (Plt.poly_part local_projection) |> BatList.of_enum in
               let l = L.basis (Plt.lattice_part local_projection) in
               let t = L.basis (Plt.tiling_part local_projection) in
               log_plt_constraints ~level:`debug "project_then_hull, projected"
                 (p, l, t);
               integer_hull_plt_assuming_integrality ~man hull_alg local_projection
            end
         end
       in
       let project_implicant =
         let open LocalAbstraction in
         Plt.abstract_to_standard_plt `ExpandModFloor srk terms symbols
         |> compose { abstract = adjoin_translation project_plt }
       in
       project_implicant
  in
  local_abs

let convex_hull_of_lira_model how ?(man=Polka.manager_alloc_loose ()) solver terms model =
  let srk = Abstract.Solver.get_context solver in
  let phi = Abstract.Solver.get_formula solver
  in
  let m = match model with
    | `LIRA m -> m
    | `LIRR _ -> invalid_arg "Unsupported"
  in
  let local_abs =
    local_abstraction_of_lira_model how ~man srk terms (Syntax.symbols phi) in
  let result = LocalAbstraction.apply local_abs m phi in
  test_hull solver terms result;
  result

let abstract how ?(man=Polka.manager_alloc_loose ()) ?(bottom=None)
      solver terms =
  let srk = Abstract.Solver.get_context solver in
  let num_terms = Array.length terms in
  let local_abs models phi =
    let m = match BatEnum.get models with
      | Some m -> m
      | None -> failwith "no model to abstract"
    in
    let symbols = Syntax.symbols (Abstract.Solver.get_formula solver) in
    LocalAbstraction.apply
      (local_abstraction_of_lira_model how ~man srk terms symbols)
      m phi
  in
  let result =
    LocalGlobal.abstract_dd
      srk ~man ~max_dim:(num_terms - 1)
      ~term_of_dim:(mk_term_of_dim terms)
      ~bottom
      ~model_translation:(fun m -> m)
      ~local_abstraction:local_abs (`Solver ((fun phi -> phi), solver))
  in
  test_hull solver terms result;
  result

let convex_hull how ?(man=(Polka.manager_alloc_loose ())) srk phi terms =
  let ints = Syntax.explicit_ints srk phi in
  let solver = Abstract.Solver.make srk (Syntax.mk_and srk (phi :: ints))
  in
  abstract how solver ~man terms

let convex_hull_of_real_relaxation how ?(man=(Polka.manager_alloc_loose ()))
      srk phi terms =
  let expanded_phi = Syntax.eliminate_floor_mod_div_int srk phi in
  let (retyped_expanded, map) = Syntax.retype srk `IntToReal expanded_phi in
  let subst sym = match Symbol.Map.find_opt sym map with
    | Some sym' -> Syntax.mk_const srk sym'
    | None -> Syntax.mk_const srk sym
  in
  let remapped_terms =
    Array.map
      (fun term -> Syntax.substitute_const srk subst term)
      terms in
  let solver = Abstract.Solver.make srk retyped_expanded in
  logf ~level:`debug "convex_hull_of_real_relaxation: @[%a@] relaxed to @[%a@]@;"
    (Syntax.Formula.pp srk) phi (Syntax.Formula.pp srk) retyped_expanded;
  abstract (ProjectImplicant (`AssumeReal how)) solver ~man remapped_terms

(*
let disjunctive_normal_form srk ~base_dim phi =
  let symbols = Syntax.symbols phi in
  let dim_of_symbol sym = Syntax.int_of_symbol sym + base_dim in
  let initial_term_of_dim =
    Symbol.Set.fold
      (fun sym map ->
        IntMap.add (dim_of_symbol sym) (Syntax.mk_const srk sym) map)
      symbols IntMap.empty
  in
  let curr_term_of_dim = ref initial_term_of_dim in
  let curr_free_dim =
    ref
      (match Symbol.Set.max_elt_opt symbols with
       | Some symbol -> dim_of_symbol symbol + 1
       | None -> base_dim
      )
  in
  let local_abs =
    let abstract m psi =
      let expansion =
        Plt.mk_standard_expansion srk
          ~free_dim:!curr_free_dim ~dim_of_symbol
      in
      let result =
        LocalAbstraction.apply2
          (Plt.abstract_to_plt
             expansion
             ~term_of_new_dims_to_set:(Some curr_term_of_dim)
             srk
             (fun interp dim ->
               try
                 let term = IntMap.find dim !curr_term_of_dim in
                 Interpretation.evaluate_term interp term
               with
               | Not_found ->
                  failwith
                    (Format.asprintf "disjunctive normal form: cannot evaluate dimension %d" dim)
             )
          )
          m psi
      in
      curr_free_dim :=
        (match IntMap.max_binding_opt !curr_term_of_dim with
         | Some (dim, _) -> dim + 1
         | None -> 0);
      result
    in
    LocalAbstraction.{abstract}
  in
  let term_of_dim dim =
    try IntMap.find dim !curr_term_of_dim
    with
    | Not_found ->
       failwith
         (Format.asprintf "disjunctive normal form: cannot find a term at dimension %d" dim)
  in
  let abstract =
    LocalGlobal.lift_plt_abstraction srk ~term_of_dim local_abs
  in
  (Abstraction.apply abstract phi, !curr_term_of_dim)
 *)
