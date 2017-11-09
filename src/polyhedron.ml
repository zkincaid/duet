open Syntax
open BatPervasives

module V = Linear.QQVector
module CS = CoordinateSystem

type t = { eq : V.t list;
           leq : V.t list }

let enum polyhedron =
  BatEnum.append
    (BatList.enum polyhedron.eq /@ (fun t -> `EqZero t))
    (BatList.enum polyhedron.leq /@ (fun t -> `LeqZero t))

let pp cs formatter polyhedron =
  let pp_elt formatter = function
    | `EqZero t -> Format.fprintf formatter "%a = 0" (CS.pp_vector cs) t
    | `LeqZero t -> Format.fprintf formatter "%a <= 0" (CS.pp_vector cs) t
  in
  let pp_sep formatter () = Format.fprintf formatter "@;" in
  Format.fprintf formatter "@[<v 0>%a@]"
    (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt) (enum polyhedron)

let conjoin x y =
  { eq = List.rev_append x.eq y.eq;
    leq = List.rev_append x.leq y.leq }

let nonzero_coeff x vec = not (QQ.equal (V.coeff x vec) QQ.zero)

let top = { eq = []; leq = [] }

let of_formula ?(admit=false) cs phi =
  let linearize = CS.vec_of_term ~admit cs in
  let alg = function
    | `Tru -> top
    | `Fls -> assert false (* to do *)
    | `And xs -> List.fold_left conjoin top xs
    | `Atom (`Eq, x, y) ->
      { eq = [V.add (linearize x) (V.negate (linearize y))]; leq = [] }
    | `Atom (`Leq, x, y) | `Atom (`Lt, x, y) ->
      { eq = []; leq = [V.add (linearize x) (V.negate (linearize y))] }
    | `Or _ | `Not _ | `Quantify (_, _, _, _) | `Proposition _
    | `Ite (_, _, _) ->
      invalid_arg "Polyhedron.of_formula"
  in
  Formula.eval (CS.get_context cs) alg phi

let to_formula cs polyhedron =
  let srk = CS.get_context cs in
  let zero = mk_real srk QQ.zero in
  let term = CS.term_of_vec cs in
  List.rev_append
    (List.map (fun t -> mk_eq srk (term t) zero) polyhedron.eq)
    (List.map (fun t -> mk_leq srk (term t) zero) polyhedron.leq)
  |> mk_and srk

(* Check whether a given point belongs to a polyhedron *)
let mem m polyhedron =
  List.for_all
    (fun t -> QQ.equal (Linear.evaluate_affine m t) QQ.zero)
    polyhedron.eq
  && List.for_all
    (fun t -> QQ.leq (Linear.evaluate_affine m t) QQ.zero)
    polyhedron.leq

let polyhedron_of_implicant ?(admit=false) cs conjuncts =
  let srk = CS.get_context cs in
  let linearize atom = match Interpretation.destruct_atom srk atom with
    | `Comparison (`Eq, x, y) ->
      { eq = [V.add
                (CS.vec_of_term ~admit cs x)
                (V.negate (CS.vec_of_term ~admit cs y))];
        leq = [] }
    | `Comparison (`Lt, x, y) | `Comparison (`Leq, x, y) ->
      { eq = [];
        leq = [V.add
                 (CS.vec_of_term ~admit cs x)
                 (V.negate (CS.vec_of_term ~admit cs y))] }
    | `Literal (_, _) -> top
  in
  List.fold_left conjoin top (List.map linearize conjuncts)

(* Model-guided projection of a polyhedron.  Given a point m within a
   polyhedron p and a set of dimension xs, compute a polyhedron q such that
   m|_xs is within q, and q is a subset of p|_xs (using |_xs to denote
   projection of dimensions xs) *)
let local_project m xs polyhedron =
  (* Replace x with replacement in term representing an (in)equality
     constraint.  Return None if the resulting (in)equality is trivial. *)
  let replace_term x replacement term =
    let (a, t) = V.pivot x term in
    let replaced = V.add (V.scalar_mul a replacement) t in
    match Linear.const_of_linterm replaced with
    | Some k ->
      assert (QQ.leq k QQ.zero);
      None
    | None -> Some replaced
  in
  (* Project a single variable *)
  let project_one polyhedron x =
    (* occ is the set of equations involving x, nonocc is the set of
       equations that don't *)
    let (occ, nonocc) = List.partition (nonzero_coeff x) polyhedron.eq in
    match occ with
    | (term::rest) ->
      (* If x is involved in an equation a*x + t = 0, replace x with -t/a
         everywhere *)
      let (a, t) = V.pivot x term in
      let toa = V.scalar_mul (QQ.inverse (QQ.negate a)) t in
      { eq =
          List.fold_left (fun eqs eq ->
              match replace_term x toa eq with
              | Some eq -> eq::eqs
              | None -> eqs)
            nonocc
            rest;
        leq = BatList.filter_map (replace_term x toa) polyhedron.leq }
    | [] ->
      (* If no equations involve x, find a least upper bound or greatest
         lower bound for x *)
      let (occ, nonocc) = List.partition (nonzero_coeff x) polyhedron.leq in
      let (lower, upper) =
        List.fold_left (fun (lower, upper) t ->
            let (a, t) = V.pivot x t in
            let bound = V.scalar_mul (QQ.inverse (QQ.negate a)) t in
            (* constraint is a*x + t <= 0, which is either x <= bound or
               bound <= x, depending on the sign of a *)
            if QQ.lt QQ.zero a then
              (lower, bound::upper)
            else
              (bound::lower, upper))
          ([], [])
          occ
      in
      match lower, upper with
      | [], _ | _, [] ->
        (* no lower bound or no upper bounds -> just remove all
           constraints involving x *)
        { eq = polyhedron.eq; leq = nonocc }
      | (lt::lower), (ut::upper) ->
        let term_val = Linear.evaluate_affine m in
        if List.length lower < List.length upper then
          let glb =
            List.fold_left (fun glb t ->
                if QQ.lt (term_val glb) (term_val t) then t else glb)
              lt
              lower
          in
          { eq = polyhedron.eq;
            leq = (BatList.filter_map (replace_term x glb) occ)@nonocc }
        else
          let lub =
            List.fold_left (fun lub t ->
                if QQ.lt (term_val t) (term_val lub) then t else lub)
              ut
              upper
          in
          { eq = polyhedron.eq;
            leq = (BatList.filter_map (replace_term x lub) occ)@nonocc }
  in
  List.fold_left project_one polyhedron xs

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
  let apron_leq t = lcons_geqz (lexpr_of_vec env (symvec (V.negate t))) in
  let apron_eq t = lcons_eqz (lexpr_of_vec env (symvec t)) in
  (List.map apron_leq polyhedron.leq)@(List.map apron_eq polyhedron.eq)
  |> meet_lcons (top man env)
