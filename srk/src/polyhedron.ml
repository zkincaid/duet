open Syntax
open BatPervasives

module V = Linear.QQVector
module CS = CoordinateSystem
module IntSet = SrkUtil.Int.Set
module IntMap = SrkUtil.Int.Map

type constraint_kind = [`Zero | `Nonneg | `Pos] [@@deriving ord]
type generator_kind = [`Vertex | `Ray | `Line]

include Log.Make(struct let name = "srk.polyhedron" end)

(* Replace x with replacement in term. *)
let replace_term x replacement term =
  let (a, t) = V.pivot x term in
  V.add (V.scalar_mul a replacement) t

module P = struct
  include BatSet.Make(struct
      type t = (constraint_kind * V.t) [@@deriving ord]
    end)

  let bottom =
    singleton (`Zero, Linear.const_linterm (QQ.of_int 1))

  let is_bottom = mem (`Zero, Linear.const_linterm (QQ.of_int 1))

  let top = empty

  let add (p, v) set =
    match Linear.const_of_linterm v with
    | Some value ->
      begin match p with
        | `Zero when QQ.equal QQ.zero value -> set
        | `Nonneg when QQ.leq QQ.zero value -> set
        | `Pos when QQ.lt QQ.zero value -> set
        | _ -> bottom
      end
    | None -> add (p, v) set

  let replace x replacement set =
    BatEnum.fold (fun set (p, t) ->
        add (p, replace_term x replacement t) set)
      empty
      (enum set)
end

type t = P.t

let enum_constraints polyhedron = P.enum polyhedron

let pp_constraint pp_dim formatter = function
  | (`Zero, t) -> Format.fprintf formatter "%a = 0" (V.pp_term pp_dim) t
  | (`Nonneg, t) -> Format.fprintf formatter "%a >= 0" (V.pp_term pp_dim) t
  | (`Pos, t) -> Format.fprintf formatter "%a > 0" (V.pp_term pp_dim) t

let pp pp_dim formatter polyhedron =
  let pp_sep formatter () = Format.fprintf formatter "@;" in
  Format.fprintf formatter "@[<v 0>%a@]"
    (SrkUtil.pp_print_enum_nobox ~pp_sep (pp_constraint pp_dim)) (P.enum polyhedron)

let of_dd polyhedron =
  BatEnum.fold (fun p cnstr -> P.add cnstr p) P.top (DD.enum_constraints polyhedron)

let dd_of ?(man=Polka.manager_alloc_loose ()) dim polyhedron =
  DD.of_constraints_closed ~man dim (P.enum polyhedron)

let nnc_dd_of ?(man=Polka.manager_alloc_strict ()) dim polyhedron =
  DD.of_constraints ~man dim (P.enum polyhedron)

let top = P.top
let bottom = P.bottom

let meet x y =
  if P.is_bottom x || P.is_bottom y then
    bottom
  else
    P.union x y

let of_formula ?(admit=false) cs phi =
  let linearize = CS.vec_of_term ~admit cs in
  let alg = function
    | `Tru -> top
    | `Fls -> bottom
    | `And xs -> List.fold_left meet top xs
    | `Atom (`Arith (`Eq, x, y)) ->
      P.singleton (`Zero, V.sub (linearize y) (linearize x))
    | `Atom (`Arith (`Leq, x, y)) ->
      P.singleton (`Nonneg, V.sub (linearize y) (linearize x))
    | `Atom (`Arith (`Lt, x, y)) ->
      P.singleton (`Pos, V.sub (linearize y) (linearize x))
    | `Or _ | `Not _ | `Quantify (_, _, _, _) | `Proposition _
    | `Ite (_, _, _) | `Atom (`ArrEq _)
    | `Atom (`IsInt _) -> invalid_arg "Polyhedron.of_formula"
  in
  Formula.eval (CS.get_context cs) alg phi

let formula_of_constraint srk f (kind, vec) =
  let open Syntax in
  let f' dim =
    if dim = Linear.const_dim then mk_one srk
    else f dim
  in
  let zero = mk_zero srk in
  let term = Linear.term_of_vec srk f' vec in
  match kind with
  | `Zero -> mk_eq srk term zero
  | `Nonneg -> mk_leq srk zero term
  | `Pos -> mk_lt srk zero term

let implicant_of srk f polyhedron =
  P.fold (fun cnstr constraints ->
      (formula_of_constraint srk f cnstr)::constraints)
    polyhedron
    []

let cube_of srk polyhedron =
  let zero = mk_real srk QQ.zero in
  let term = Linear.of_linterm srk in
  P.fold (fun (p, t) constraints ->
      let new_constraint =
        match p with
        | `Zero -> mk_eq srk (term t) zero
        | `Nonneg -> mk_leq srk zero (term t)
        | `Pos -> mk_lt srk zero (term t)
      in
      new_constraint::constraints)
    polyhedron
    []

let to_formula srk f polyhedron =
  implicant_of srk f polyhedron
  |> mk_and srk

(* Check whether a given point belongs to a polyhedron *)
let mem m polyhedron =
  P.for_all (function
      | (`Zero, t) -> QQ.equal (Linear.evaluate_affine m t) QQ.zero
      | (`Nonneg, t) -> QQ.leq QQ.zero (Linear.evaluate_affine m t)
      | (`Pos, t) -> QQ.lt QQ.zero (Linear.evaluate_affine m t))
    polyhedron

let of_implicant ?(admit=false) cs conjuncts =
  let srk = CS.get_context cs in
  let linearize atom = match Interpretation.destruct_atom srk atom with
    | `ArithComparison (p, x, y) ->
      let t =
        V.sub (CS.vec_of_term ~admit cs y) (CS.vec_of_term ~admit cs x)
      in
      let p = match p with `Eq -> `Zero | `Leq -> `Nonneg | `Lt -> `Pos in
      P.singleton (p, t)
    | _ -> top
  in
  List.fold_left meet top (List.map linearize conjuncts)

let of_cube srk cube =
  let add polyhedron atom =
    match Interpretation.destruct_atom srk atom with
    | `ArithComparison (p, x, y) ->
      let t =
        V.sub (Linear.linterm_of srk y) (Linear.linterm_of srk x)
      in
      let p = match p with `Eq -> `Zero | `Leq -> `Nonneg | `Lt -> `Pos in
      P.add (p, t) polyhedron
    | _ ->
      Log.logf ~level:`warn "Discarded constraint in Polyhedron.of_cube";
      polyhedron
  in
  List.fold_left add top cube

(* Given a coordinate x and a polyhedron p, find a term t such that p |= x=t
   and x does not appear in t, should one exist. *)
let select_equal_term x polyhedron =
  let enum = P.enum polyhedron in
  let rec go () = match BatEnum.get enum with
    | None -> None
    | Some (`Zero, t) ->
      let (a, t) = V.pivot x t in
      if QQ.equal a QQ.zero then
        go ()
      else
        Some (V.scalar_mul (QQ.inverse (QQ.negate a)) t)
    | Some (_, _) -> go ()
  in
  go ()

(* Project a single variable, as long as the number of added constraints does
   not exceed max_add. If max_add is negative, the variable is projected no
   matter how many constraints it adds. *)
let project_one max_add polyhedron x =
  match select_equal_term x polyhedron with
  | Some t -> P.replace x t polyhedron
  | None ->
    (* If no equations involve x, find a least upper bound or greatest lower
       bound for x *)
    let (lower, upper, rest) =
      P.fold (fun (p, t) (lower, upper, rest) ->
          let (a, t) = V.pivot x t in
          if QQ.equal a QQ.zero then
            (lower, upper, P.add (p,t) rest)
          else
            let bound =
              (p = `Pos, V.scalar_mul (QQ.inverse (QQ.negate a)) t)
            in
            (* constraint is a*x + t >= 0, which is either x <= bound or bound
               <= x, depending on the sign of a *)
            if QQ.lt QQ.zero a then
              (bound::lower, upper, rest)
            else
              (lower, bound::upper, rest))
        polyhedron
        ([], [], top)
    in
    let nb_lower = List.length lower in
    let nb_upper = List.length upper in
    if max_add < 0 || max_add > (nb_lower*nb_upper-nb_lower-nb_upper) then
      List.fold_left (fun polyhedron (strict, lo) ->
          List.fold_left (fun polyhedron (strict', hi) ->
              if strict || strict' then
                P.add (`Pos, V.sub hi lo) polyhedron
              else
                P.add (`Nonneg, V.sub hi lo) polyhedron)
            polyhedron
            upper)
        rest
        lower
    else
      polyhedron

let project xs polyhedron =
  Log.time "Fourier-Motzkin" (List.fold_left (project_one (-1)) polyhedron) xs

let try_fourier_motzkin cs p polyhedron =
  let projected_linear =
    BatEnum.fold (fun remove i ->
        match CS.destruct_coordinate cs i with
        | `App (sym, []) -> if p sym then remove else IntSet.add i remove
        | _ ->
          IntSet.diff remove (CS.direct_subcoordinates cs i))
      IntSet.empty
      (0 -- (CS.dim cs - 1))
    |> IntSet.elements
  in
  Log.time "Fourier-Motzkin"
    (List.fold_left (project_one 10) polyhedron) projected_linear

(* All dimensions involved in a constraint. *)
let _constrained_dimensions polyhedron =
  BatEnum.fold (fun dims (_, v) ->
      BatEnum.fold (fun dims (_, dim) ->
          if dim == Linear.const_dim then
            dims
          else
            IntSet.add dim dims)
        dims
        (V.enum (snd (V.pivot Linear.const_dim v))))
    IntSet.empty
    (enum_constraints polyhedron)

let max_constrained_dim polyhedron =
  BatEnum.fold (fun dims (_, v) ->
      BatEnum.fold (fun max_dim (_, dim) -> max max_dim dim) dims (V.enum v))
    0
    (enum_constraints polyhedron)

let project_dd xs polyhedron =
  let dim = 1 + max_constrained_dim polyhedron in
  let polyhedron =
    List.fold_left (project_one 10) polyhedron xs
  in
  of_dd (DD.project xs (dd_of dim polyhedron))

let dual_cone dim polyhedron =
  (* Given polyhedron Ax >= b, form the constraint system
     lambda * A = y /\ lambda * b >= 0.
     Then project out the lambda dimensions.
  *)
  (* map [0 .. nb_constraints] to [dim .. dim + nb_constraints] *)
  assert (dim >= max_constrained_dim polyhedron);
  let lambda i = dim + i in
  let lambda_nonnegative =
    BatEnum.foldi
      (fun i (cmp, _) constraints ->
         match cmp with
         | `Zero -> constraints
         | `Nonneg | `Pos ->
           P.add (`Nonneg, V.of_term QQ.one (lambda i)) constraints)
      P.top
      (P.enum polyhedron)
  in
  let farkas_constraints =
    let zero =
      BatEnum.fold
        (fun map dim -> IntMap.add dim (V.of_term (QQ.of_int (-1)) dim) map)
        IntMap.empty
        (0 -- (dim - 1))
    in
    let (lambdaA, lambdab) =
      BatEnum.foldi
        (fun i (_, t) (lambdaA, lambdab) ->
           BatEnum.fold
             (fun (lambdaA, lambdab) (scalar, dim) ->
                if dim == Linear.const_dim then
                  (lambdaA, V.add_term (QQ.negate scalar) (lambda i) lambdab)
                else
                  (IntMap.modify dim (V.add_term scalar (lambda i)) lambdaA, lambdab))
             (lambdaA, lambdab)
             (V.enum t))
        (zero, V.zero)
        (P.enum polyhedron)
    in
    IntMap.fold (fun _ t constraints ->
        P.add (`Zero, t) constraints)
      lambdaA
      (P.add (`Nonneg, lambdab) lambda_nonnegative)
  in
  project
    (BatList.of_enum (dim -- (P.cardinal polyhedron + dim - 1)))
    farkas_constraints

let of_constraints constraints =
  BatEnum.fold (fun p constr -> P.add constr p) P.top constraints

(** Given a matrix [M] and a polyhedron [p], find a polyhedron [q]
    such that [p] contains a point [x] iff [q] contains [Mx].  Such a
    polyhedron exists iff [p] can be written as [Ax >= b], with the
    rowspace of [A] contained in the rowspace of [M]. *)
let invertible_image mM polyhedron =
  let mMt = Linear.QQMatrix.transpose mM in
  let densify_vec vec =
    let (a, vec) = V.pivot Linear.const_dim vec in
    match Linear.solve mMt vec with
    | Some v -> V.add_term a Linear.const_dim v
    | None -> invalid_arg "Densify: polyhedron is unrepresentible in the chosen basis"
  in
  P.fold (fun (kind, vec) dense ->
      P.add (kind, densify_vec vec) dense)
    polyhedron
    P.top

let conical_hull polyhedron =
  let dim = (max_constrained_dim polyhedron + 1) in
  dual_cone dim polyhedron
  |> dd_of dim
  |> DD.enum_generators
  |> BatEnum.filter_map (function
      | `Vertex, vec ->
        assert (V.equal V.zero vec);
        None
      | `Ray, vec ->
        Some (`Nonneg, vec)
      | `Line, vec ->
        Some (`Zero, vec))
  |> of_constraints

let constraint_space polyhedron =
  enum_constraints polyhedron
  /@ (fun (_, v) -> snd (V.pivot Linear.const_dim v))
  |> BatList.of_enum
  |> Linear.QQVectorSpace.basis

let equal p q =
  let man = Polka.manager_alloc_strict () in
  let cs = constraint_space p in
  let dim = List.length cs in
  let csM = Linear.QQVectorSpace.matrix_of cs in
  if Linear.QQVectorSpace.equal cs (constraint_space q) then
    let p0 = nnc_dd_of ~man dim (invertible_image csM p) in
    let q0 = nnc_dd_of ~man dim (invertible_image csM q) in
    DD.equal p0 q0
  else
    false

let valid_cone polyhedron =
  let dim = max_constrained_dim polyhedron in
  let (lines, rays) =
    P.fold (fun (p, v) (lines, rays) ->
        match p with
        | `Zero -> (v::lines, rays)
        | `Nonneg | `Pos -> (lines, v::rays))
      polyhedron
      ([], [V.of_term QQ.one Linear.const_dim])
  in
  Cone.make ~lines ~rays dim

let implies polyhedron (p, v) =
  let c = valid_cone polyhedron in
  match p with
  | `Zero -> Cone.mem v c && Cone.mem (V.negate v) c
  | `Nonneg -> Cone.mem v c
  | `Pos -> invalid_arg "Polyhedron.implies does not currently support strict \
                         inequalities"

module IntegerHull = struct

  open Normalizffi

  (* Rescale vector such that the selected coefficients are integral and
     relatively prime *)
  let normalize v =
    Linear.QQVector.scalar_mul (QQ.inverse (Linear.QQVector.gcd_entries v)) v

  module D = Linear.MakeDenseConversion(SrkUtil.Int)(V)

  let densify ctx v =
    let array = Array.make (D.dim ctx) (ZZ.mpz_of ZZ.zero) in
    BatEnum.iter
      (fun (a, i) ->
         array.(D.int_of_dim ctx i) <- ZZ.mpz_of (Option.get (QQ.to_zz a)))
      (V.enum v);
    Array.to_list array

  let sparsify ctx v =
    BatList.fold_lefti (fun vec i a ->
        V.set (D.dim_of_int ctx i) (QQ.of_zz (ZZ.of_mpz a)) vec)
      V.zero
      v

  let normaliz_cone_by_constraints polyhedron =
    let normalized_constraints =
      enum_constraints polyhedron
      /@ (fun (p, v) -> (p, normalize v))
      |> (* Add 1 >= 0 to ensure the constant dimension x0 is present,
            so that the cone may be dehomogenized at x0 = 1 if needed
            to get a polyhedron.
         *)
      (fun enum ->
         BatEnum.push enum (`Nonneg, Linear.const_linterm (QQ.of_int 1)); enum)
      |> BatList.of_enum
    in
    let ctx =
      BatList.enum normalized_constraints
      /@ snd
      |> D.min_context
    in
    (* The constant dimension must be present and be the first coordinate *)
    assert (D.int_of_dim ctx Linear.const_dim = 0);
    let (equalities, inequalities) =
      List.fold_left
        (fun (equalities, inequalities) (kind, v) ->
           match kind with
           | `Zero -> (densify ctx v :: equalities, inequalities)
           | `Nonneg -> (equalities, densify ctx v :: inequalities)
           | `Pos -> invalid_arg "normaliz_cone_of: open faces not supported yet")
        ([], [])
        normalized_constraints in
    try
      let cone = Normaliz.empty_cone
                 |> Normaliz.add_equalities equalities |> Result.get_ok
                 |> Normaliz.add_inequalities inequalities |> Result.get_ok
                 |> Normaliz.new_cone
      in
      (cone, ctx)
    with Invalid_argument s -> logf "normaliz_cone_by_constraints"; invalid_arg s

  let polyhedron_of (equalities, inequalities, ctx) =
    let to_constraint kind v = (kind, sparsify ctx v) in
    let equalities = List.map (to_constraint `Zero) equalities in
    let inequalities = List.map (to_constraint `Nonneg) inequalities in
    BatList.enum (List.append equalities inequalities)
    |> of_constraints

  let hull_by_normaliz polyhedron =
    let (cone, bijection) = normaliz_cone_by_constraints polyhedron in

    logf ~level:`trace "polyhedron: integer_hull: computed Normaliz cone for polyhedron:@[%a@]@;"
      (pp (Polynomial.pp_numeric_dim "x")) polyhedron;

    let dehomogenized = Normaliz.dehomogenize cone in
    logf ~level:`trace "polyhedron: integer_hull: dehomogenized cone, computing integer hull...@;";
    Normaliz.hull dehomogenized;
    if !my_verbosity_level = `trace then
      logf ~level:`trace "polyhedron: integer_hull: computed integer hull: @[%a@]@;"
        Normaliz.pp_hull dehomogenized
    else ();

    let cut_ineqs = Normaliz.get_int_hull_inequalities dehomogenized in
    let cut_eqns = Normaliz.get_int_hull_equations dehomogenized
    in
    polyhedron_of (cut_eqns, cut_ineqs, bijection)

  let hull_by_gomory_chvatal polyhedron =
    let dim = 1 + max_constrained_dim polyhedron in
    let man = Polka.manager_alloc_loose () in
    of_dd (DD.integer_hull (dd_of ~man dim polyhedron))

end

let integer_hull = function
  | `GomoryChvatal -> IntegerHull.hull_by_gomory_chvatal
  | `Normaliz -> IntegerHull.hull_by_normaliz

module IntDS = DisjointSet.Make(struct
    include Int
    let hash = Hashtbl.hash
    let equal = (=)
  end)

let factor polyhedron =
  let ds = IntDS.create 991 in
  enum_constraints polyhedron |> BatEnum.iter
    (fun (_, v) ->
       let ((i, _), v') = V.pop (snd (V.pivot Linear.const_dim v)) in
       let rep = IntDS.find ds i in
       V.enum v' |> BatEnum.iter (fun (_, j) ->
           ignore (IntDS.union (IntDS.find ds j) rep)));
  let rev_map =
    IntDS.reverse_map ds IntSet.empty IntSet.add
  in
  let find_rep i = IntSet.choose (rev_map i) in
  let map =
    BatEnum.fold (fun map (kind, vec) ->
        let equiv_class =
          find_rep (fst (fst (V.pop (snd (V.pivot Linear.const_dim vec)))))
        in
        IntMap.modify_def P.top equiv_class (P.add (kind, vec)) map)
      IntMap.empty
      (enum_constraints polyhedron)
  in
  BatList.of_enum (IntMap.values map)

let integer_hull ?(decompose=true) how =
  Log.time "Integer hull" (fun p ->
      if decompose then
        List.fold_left
          (fun rest factor -> meet rest (integer_hull how factor))
          top
          (factor p)
      else
        integer_hull how p)

(* Given target vector v, and a set of halfspaces containing v, compute
   generators for a cone that contains v and is contained within each
   halfspace.  The cone is generated by at most dim "short" integer vectors,
   where dim is the dimension of the ambient space. *)
let _dual_relative_subcone dim halfspaces v =
  (* Initialization: create a cone that contains v (but is not
     necessarily contained inside the given halfspaces) *)
  let cardinal_rays =
    V.fold (fun i coeff rays ->
        let i_ray =
          if QQ.lt QQ.zero coeff then
            V.of_term QQ.one i
          else
            V.of_term (QQ.of_int (-1)) i
        in
        i_ray::rays)
      v
      []
  in
  (* For each halfspace, intersect the current cone with the halfspace.  Write
     v as a nonnegative combination of rays, and then take the subcone
     generated by all of rays with non-zero coefficients.  This cone satisfies
     the invariant that it contain v and is contained within the intersection
     of all halfspaces seen so far. *)
  List.fold_left (fun cone halfspace ->
      let cone' = Cone.intersect_halfspaces cone [halfspace] in
      if List.length (Cone.generators cone') > dim then
        let rays' = Array.of_list (Cone.generators cone') in
        match Cone.simplex rays' v with
        | None -> assert false (* Impossible *)
        | Some soln ->
          let relevant_rays =
            V.fold (fun i _ relevant_rays -> rays'.(i)::relevant_rays) soln []
          in
          Cone.make ~rays:relevant_rays ~lines:[] dim
      else
        cone')
    (Cone.make ~rays:cardinal_rays ~lines:[] dim)
    halfspaces


let _close_point scale polyhedron ~rational ~integer n =
  (* Call the rational point r and the inger point z.
     Write P as { x : A_1 x >= b_1 /\ A_2 x >= b_2 }, where
     A_1 z >= A_1 r and A_2 z < A_2 r.  Define C to be the cone
     { x : A_1 x >= 0 /\ A_2 x <= 0 } -- find a subcone of C
     that contains (z-r).  *)
  let c =
    let rays =
      P.fold (fun (kind, v) rays ->
          let v = snd (V.pivot Linear.const_dim v) in (* Homogenize *)
          match kind with
          | `Zero -> (V.negate v)::v::rays
          | `Nonneg | `Pos ->
            let rat_val = Linear.QQVector.dot v rational in
            let int_val = Linear.QQVector.dot v integer in
            if QQ.leq rat_val int_val then
              v::rays
            else
              (V.negate v)::rays)
        polyhedron
        []
    in
      _dual_relative_subcone n rays (V.sub integer rational)
  in
  (* By construction of the cone C, it must contain (z-r).  Write (z-r) as a
     lambda_0 v_0 + ... + lambda_n v_n where v_0,...,v_n is a set of integer
     vectors generating C, and each lambda_i >= 0. *)
  let rays = Array.of_list (Cone.generators c) in
  BatArray.modify scale rays;
  match Cone.simplex rays (V.sub integer rational) with
  | None -> assert false (* Impossible *)
  | Some soln ->
    (* z = r + (z-r) = r + lambda_0*v_0 + ... + lambda_n*v_n.
       It follows that
       r + (lambda_0 - floor lambda_0)*v_0 + ... + (lambda_n - floor lambda_n)*v_n
       is an integer point in P that is close to r *)
    V.fold (fun i lambda z' ->
        V.add z' (V.scalar_mul (QQ.sub lambda (QQ.of_zz (QQ.floor lambda))) rays.(i)))
      soln
      rational

let close_integral_point =
  _close_point (fun v -> V.scalar_mul (QQ.of_zz (V.common_denominator v)) v)

let close_lattice_point = function
  | [] -> (fun _ ~rational ~integer:_ _ -> rational)
  | fns ->
    _close_point (fun v ->
        let gcd = List.fold_left (fun z f -> QQ.gcd (f v) z) QQ.zero fns in
        if QQ.equal gcd QQ.zero then
          (* v is orthogonal to all functions constrained to be integral -- no
             need to scale. *)
          v
        else V.scalar_mul (QQ.inverse gcd) v)

