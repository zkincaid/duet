open Syntax
open BatPervasives
module Vec = Linear.QQVector
module TF = TransitionFormula
module CS = CoordinateSystem

include Log.Make(struct let name = "TerminationLLRF" end)

let mem_cs cs x =
  try (ignore (CS.cs_term_id cs (`App (x,[]))); true)
  with Not_found -> false

let cs_of_symbols srk symbols =
  let cs = CS.mk_empty srk in
  List.iter (fun x -> CoordinateSystem.admit_cs_term cs (`App (x,[]))) symbols;
  cs

(* Given a formula F, find the weakest formula G such that G |= F and
   every quasi-ranking function of G is invariant.  Return None if G =
   false (i.e., F has a linear-lexicographic ranking function).  *)
let llrf_residual srk tf =
  let polka = Polka.manager_alloc_loose () in
  let tf = TF.linearize srk tf in
  let x_xp =
    Symbol.Set.fold
      (fun s xs -> (s,s)::xs)
      (TF.symbolic_constants tf)
      (TF.symbols tf)
  in
  (* For each variable x, create a symbol d_x representing x - x' *)
  let dx =
    List.map (fun (x,_) ->
        let name = String.concat "" ["d_"; show_symbol srk x] in
        mk_symbol srk ~name (typ_symbol srk x))
      x_xp
  in
  let formula = (* tf /\_x d_x = x' - x, in negation-normal form *)
    let nnf =
      rewrite srk ~down:(pos_rewriter srk) (TF.formula tf)
    in
    let diff =
      List.map2 (fun (x,x') dx ->
          mk_eq srk (mk_const srk dx) (mk_sub srk (mk_const srk x) (mk_const srk x')))
        x_xp
        dx
    in
    mk_and srk (nnf::diff)
  in
  let dim = List.length x_xp in
  let x_cs = cs_of_symbols srk (List.map fst x_xp) in
  let dx_cs = cs_of_symbols srk dx in
  let rec go formula =
    let pre_guard =
      Abstract.abstract ~exists:(mem_cs x_cs) srk polka formula
    in
    if SrkApron.is_bottom pre_guard then
      None (* Residual is inconsistent *)
    else
      (* Find the cone of quasi-ranking functions and strengthen F to
         constrain the generators of the cone to be invariant *)
      let non_inc_cone =
        Abstract.abstract ~exists:(mem_cs dx_cs) srk polka formula
        |> SrkApron.formula_of_property
        |> Polyhedron.of_formula dx_cs
        |> Polyhedron.dual_cone dim
        |> Polyhedron.dd_of ~man:polka dim
      in
      let lb_cone =
        let lb_cone_generators =
          SrkApron.formula_of_property pre_guard
          |> Polyhedron.of_formula x_cs
          |> Polyhedron.enum_constraints
          |> BatEnum.map (fun (constraint_kind, v) ->
                 match constraint_kind with
                 | `Nonneg | `Pos -> let _, w = Vec.pivot (-1) v in (`Ray, w)
                 | `Zero -> let _, w = Vec.pivot (-1) v in (`Line, w))
        in
        (* Origin must belong to the lower-bounded terms cone *)
        BatEnum.push lb_cone_generators (`Vertex, Vec.zero);
        DD.of_generators dim lb_cone_generators
      in
      let qrf_cone = DD.meet non_inc_cone lb_cone in
      let qrf_invariant =
        DD.enum_generators qrf_cone
        |> BatEnum.filter_map (fun (typ, vec) ->
               if typ = `Ray then
                 let unprimed_exp =
                   Linear.term_of_vec srk
                     (fun d -> mk_const srk (fst (BatList.nth x_xp d)))
                     vec
                 in
                 let primed_exp =
                   Linear.term_of_vec srk
                     (fun d -> mk_const srk (snd (BatList.nth x_xp d)))
                     vec
                 in
                 Some (mk_eq srk unprimed_exp primed_exp)
               else (* Only vertex is zero; lines are already invariant *)
                 None)
        |> BatList.of_enum
      in
      if qrf_invariant = [] then Some formula (* All QRFs are invariant *)
      else match Smt.entails srk formula (mk_and srk qrf_invariant) with
           | `Yes | `Unknown -> Some formula (* All QRFs are invariant *)
           | `No -> go (mk_and srk (formula::qrf_invariant))
  in
  go formula

let has_llrf srk tf = (llrf_residual srk tf = None)

let mp srk tf = if has_llrf srk tf then mk_true srk else mk_false srk
