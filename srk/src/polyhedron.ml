open Syntax
open BatPervasives

module V = Linear.QQVector
module CS = CoordinateSystem
module IntSet = SrkUtil.Int.Set
module IntMap = SrkUtil.Int.Map

type compare = Eq | Geq | Gt [@@deriving ord]


(* Replace x with replacement in term. *)
let replace_term x replacement term =
  let (a, t) = V.pivot x term in
  V.add (V.scalar_mul a replacement) t

module P = struct
  include BatSet.Make(struct
      type t = (compare * V.t) [@@deriving ord]
    end)

  let bottom =
    singleton (Eq, Linear.const_linterm (QQ.of_int 1))

  let is_bottom = mem (Eq, Linear.const_linterm (QQ.of_int 1))

  let top = empty

  let add (p, v) set =
    match Linear.const_of_linterm v with
    | Some value ->
      begin match p with
        | Eq when QQ.equal QQ.zero value -> set
        | Geq when QQ.leq QQ.zero value -> set
        | Gt when QQ.lt QQ.zero value -> set
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

let enum polyhedron =
  (P.enum polyhedron)
  /@ (function
      | (Eq, t) -> `EqZero t
      | (Geq, t) -> `LeqZero (V.negate t)
      | (Gt, t) -> `LtZero (V.negate t))

let pp cs formatter polyhedron =
  let pp_elt formatter = function
    | (Eq, t) -> Format.fprintf formatter "%a = 0" (CS.pp_vector cs) t
    | (Geq, t) -> Format.fprintf formatter "%a >= 0" (CS.pp_vector cs) t
    | (Gt, t) -> Format.fprintf formatter "%a > 0" (CS.pp_vector cs) t
  in
  let pp_sep formatter () = Format.fprintf formatter "@;" in
  Format.fprintf formatter "@[<v 0>%a@]"
    (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt) (P.enum polyhedron)

let top = P.top
let bottom = P.bottom

let conjoin x y =
  if P.is_bottom x || P.is_bottom y then
    bottom
  else
    P.union x y

let of_formula ?(admit=false) cs phi =
  let linearize = CS.vec_of_term ~admit cs in
  let alg = function
    | `Tru -> top
    | `Fls -> bottom
    | `And xs -> List.fold_left conjoin top xs
    | `Atom (`Eq, x, y) ->
      P.singleton (Eq, V.sub (linearize y) (linearize x))
    | `Atom (`Leq, x, y) ->
      P.singleton (Geq, V.sub (linearize y) (linearize x))
    | `Atom (`Lt, x, y) ->
      P.singleton (Gt, V.sub (linearize y) (linearize x))
    | `Or _ | `Not _ | `Quantify (_, _, _, _) | `Proposition _
    | `Ite (_, _, _) ->
      invalid_arg "Polyhedron.of_formula"
  in
  Formula.eval (CS.get_context cs) alg phi

let implicant_of cs polyhedron =
  let srk = CS.get_context cs in
  let zero = mk_real srk QQ.zero in
  let term = CS.term_of_vec cs in
  P.fold (fun (p, t) constraints ->
      let new_constraint =
        match p with
        | Eq -> mk_eq srk (term t) zero
        | Geq -> mk_leq srk zero (term t)
        | Gt -> mk_lt srk zero (term t)
      in
      new_constraint::constraints)
    polyhedron
    []

let to_formula cs polyhedron =
  implicant_of cs polyhedron
  |> mk_and (CS.get_context cs)

(* Check whether a given point belongs to a polyhedron *)
let mem m polyhedron =
  P.for_all (function
      | (Eq, t) -> QQ.equal (Linear.evaluate_affine m t) QQ.zero
      | (Geq, t) -> QQ.leq QQ.zero (Linear.evaluate_affine m t)
      | (Gt, t) -> QQ.lt QQ.zero (Linear.evaluate_affine m t))
    polyhedron

let nonzero_coeff x vec = not (QQ.equal (V.coeff x vec) QQ.zero)

let of_implicant ?(admit=false) cs conjuncts =
  let srk = CS.get_context cs in
  let linearize atom = match Interpretation.destruct_atom srk atom with
    | `Comparison (p, x, y) ->
      let t =
        V.sub (CS.vec_of_term ~admit cs y) (CS.vec_of_term ~admit cs x)
      in
      let p = match p with `Eq -> Eq | `Leq -> Geq | `Lt -> Gt in
      P.singleton (p, t)
    | `Literal (_, _) -> top
  in
  List.fold_left conjoin top (List.map linearize conjuncts)

(* Given a coordinate x and a polyhedron p, find a term t such that p |= x=t
   and x does not appear in t, should one exist. *)
let select_equal_term x polyhedron =
  let enum = P.enum polyhedron in
  let rec go () = match BatEnum.get enum with
    | None -> None
    | Some (Eq, t) ->
      let (a, t) = V.pivot x t in
      if QQ.equal a QQ.zero then
        go ()
      else
        Some (V.scalar_mul (QQ.inverse (QQ.negate a)) t)
    | Some (_, _) -> go ()
  in
  go ()

(* Loos-Weispfenning virtual term *)
type lw_vt =
  | MinusInfinity
  | PlusEpsilon of V.t
  | Term of V.t

(* Model-based selection of a Loos-Weispfenning virtual term *)
let select_lw m x polyhedron =
  (* Internally to this function, it's conveniento represent a virtual term as
     a triple consisting of a term, its value in the model, and a flag
     indicating whether an epsilon is required (-oo is represented by
     None). *)
  let merge_vt_internal x y =
    match x, y with
    | None, x | x, None -> x
    | Some (_, value, _), Some (_, value', _) when QQ.lt value value' -> y
    | Some (_, value, _), Some (_, value', _) when QQ.lt value' value -> x
    | Some (_, _, _), Some (_, _, true) -> y
    | _, _ -> x
  in
  let vt_internal =
    P.fold (fun (p, t) vt ->
        let (a, t) = V.pivot x t in
        if QQ.leq a QQ.zero then
          vt
        else
          (* ax + t >= 0 /\ a > 0 |= x >= t/a *)
          let toa = V.scalar_mul (QQ.inverse (QQ.negate a)) t in
          let strict = (p = Gt) in
          let value = Linear.evaluate_affine m toa in
          merge_vt_internal vt (Some (toa, value, strict)))
      polyhedron
      None
  in
  match vt_internal with
  | None -> MinusInfinity
  | Some (t, _, true) -> PlusEpsilon t
  | Some (t, _, false) -> Term t

let substitute_lw_vt x vt polyhedron =
  match vt with
  | Term t -> P.replace x t polyhedron
  | MinusInfinity ->
    P.fold (fun (p, term) polyhedron ->
        let a = V.coeff x term in
        if QQ.equal QQ.zero a then
          P.add (p, term) polyhedron
        else if QQ.lt QQ.zero a || p = Eq then
          bottom
        else
          polyhedron)
      polyhedron
      top
  | PlusEpsilon t ->
    P.fold (fun (p, term) polyhedron ->
        let (a, term') = V.pivot x term in
        if QQ.equal QQ.zero a then
          P.add (p, term) polyhedron
        else
          let term' = V.add (V.scalar_mul a t) term' in
          if p = Eq then
            bottom
          else if QQ.lt QQ.zero a then
            P.add (Geq, term') polyhedron
          else
            P.add (Gt, term') polyhedron)
      polyhedron
      top

(* Model-guided projection of a polyhedron.  Given a point m within a
   polyhedron p and a set of dimension xs, compute a polyhedron q such that
   m|_xs is within q, and q is a subset of p|_xs (using |_xs to denote
   projection of dimensions xs) *)
let local_project m xs polyhedron =
  (* Project a single variable *)
  let project_one polyhedron x =
    let vt = select_lw m x polyhedron in
    substitute_lw_vt x vt polyhedron
  in
  List.fold_left project_one polyhedron xs

let project xs polyhedron =
  (* Project a single variable *)
  let project_one polyhedron x =
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
                (p = Gt, V.scalar_mul (QQ.inverse (QQ.negate a)) t)
              in
              (* constraint is a*x + t >= 0, which is either x <= bound or
                 bound <= x, depending on the sign of a *)
              if QQ.lt QQ.zero a then
                (bound::lower, upper, rest)
              else
                (lower, bound::upper, rest))
          polyhedron
          ([], [], top)
      in
      List.fold_left (fun polyhedron (strict, lo) ->
          List.fold_left (fun polyhedron (strict', hi) ->
              if strict || strict' then
                P.add (Gt, V.sub hi lo) polyhedron
              else
                P.add (Geq, V.sub hi lo) polyhedron)
            polyhedron
            upper)
        polyhedron
        lower
  in
  Log.time "Fourier-Motzkin" (List.fold_left project_one polyhedron) xs

let to_apron cs env man polyhedron =
  let open SrkApron in
  let symvec v =
    V.enum v
    /@ (fun (coeff, coord) ->
        if coord == Linear.const_dim then
          (coeff, coord)
        else
          match CS.destruct_coordinate cs coord with
          | `App (sym, []) -> (coeff, int_of_symbol sym)
          | _ -> invalid_arg "Polyhedron.to_apron")
    |> V.of_enum
  in
  let constraints =
    P.fold (fun (p, t) cs ->
        let c =
          match p with
          | Eq -> lcons_eqz (lexpr_of_vec env (symvec t))
          | Geq -> lcons_geqz (lexpr_of_vec env (symvec t))
          | Gt -> lcons_gtz (lexpr_of_vec env (symvec t))
        in
        c::cs)
      polyhedron
      []
  in
  meet_lcons (top man env) constraints

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
  project projected_linear polyhedron
