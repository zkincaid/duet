(*pp camlp4find deriving.syntax *)

open Core
open CfgIr
open Apak
open EqLogic

module DG = Afg.G
module Pack = Afg.Pack

(* Two point lock sets *)
module LockPred = struct
  module LP = LockLogic.LockPred
  include LockLogic.CombinePred(Var)(LP)(LP)
  let implies sub x y =
    let sub' ap = Some (sub ap) in
      equal x (subst sub' y)
  let clear_fst (x, y) = (LP.unit, y)
  let clear_snd (x, y) = (x, LP.unit)
  let make_acq x = 
    let ls = { LP.acq = x;
               LP.rel = AP.Set.empty }
    in
      (ls, ls)
  let make_rel x = 
    let ls = { LP.acq = AP.Set.empty; 
               LP.rel = x }
    in
      (ls, ls)
  let fst_acq (ls, _) = ls.LP.acq
  let snd_acq (_, ls) = ls.LP.acq
  let fst_rel (ls, _) = ls.LP.rel
  let snd_rel (_, ls) = ls.LP.rel
end

module Make(MakeEQ :
	      functor (P : Hashed.Predicate with type var = Var.t) ->
		Hashed.ConjFormula with type var = Var.t
				   and type pred = P.t) = struct
  module SeqDep = AliasLogic.Make(MakeEQ)

  module MakeFormula (Minterm : Hashed.ConjFormula with type var = Var.t) = struct
    module Formula = EqLogic.MakeFormula(Minterm)
    module TR = struct 
      include Formula.Transition

      let sub_index i j x = if Var.get_subscript x = i then Var.subscript x j else x
      let sub0 = sub_index 0 3
      let sub1 = sub_index 1 3
      let pred_unit = Minterm.get_pred Minterm.unit

      let subst sub x =
        let frame = get_frame x in
        let f m   = add (of_minterm frame (Minterm.subst sub m)) in
          fold_minterms f x zero

      let apply_pred f x =
        let frame = get_frame x in
        let g m   =
          let m' = Minterm.make (Minterm.get_eqs m) (f (Minterm.get_pred m)) in
            add (of_minterm frame m')
        in
          fold_minterms g x zero
    end
    module State = Formula.State
  end

  module KillPred = struct
    include SeqDep.KillPred
    let subst sub_var set =
      let add iap set = match (iap, AP.psubst_var sub_var iap) with
        | (Variable v, _) -> AP.Set.add iap set
	| (_, Some z) -> AP.Set.add z set
	| (_, None)   -> set
      in
      AP.Set.fold add set AP.Set.empty
    let pred_weight def = 
      let assign_weight ap = AP.Set.singleton (AP.subscript 0 ap) in
      let assume_weight be =
        AP.Set.map (AP.subscript 0) (Bexpr.get_uses be)
      in
        match def.dkind with
          | Store (lhs, rhs) -> assign_weight lhs
          | Assign (lhs, rhs) -> assign_weight (Variable lhs)
          | Assume be | Assert (be, _) -> assume_weight be
          | AssertMemSafe (e, _) -> assume_weight (Bexpr.of_expr e)
          | Builtin (Alloc (lhs, _, _)) -> assign_weight (Variable lhs)
          | _ -> AP.Set.empty
  end
  module LKPred  = LockLogic.CombinePred(Var)(LockPred)(KillPred)
  module LKMinterm = MakeEQ(LKPred)
  module LK = MakeFormula(LKMinterm)

  module RDPred = struct
    include SeqDep.RDPred
    let subst subst_var x =
      let current = match x.SeqDep.current_name with
        | Some (Variable v) -> Some (Variable v)
	| Some name -> AP.psubst_var subst_var name
	| None -> None
      in
      { SeqDep.current_name = current;
	SeqDep.killed = KillPred.subst subst_var x.SeqDep.killed }
    let pred_weight def = unit
  end

  module LRDPred = LockLogic.CombinePred(Var)(LockPred)(RDPred)
  module LRDMinterm = MakeEQ(LRDPred)
  module LRD = MakeFormula(LRDMinterm)

  module CoLRDPred = LockLogic.CombinePred(Var)(LRDPred)(LRDPred)
  module CoLRDMinterm = MakeEQ(CoLRDPred)
  module CoLRD = MakeFormula(CoLRDMinterm)

  module DefAP = struct
    type t = Def.t * AP.t
                       deriving (Show, Compare)
    let format = Show_t.format
    let show = Show_t.show
    let compare = Compare_t.compare
    let hash (def, ap) = Hashtbl.hash (Def.hash def, AP.hash ap)
    let equal x y = compare x y = 0
  end
  module RDMap =
    Monoid.FunctionSpace.Total.Ordered.Make
      (DefAP)
      (Ka.Ordered.AdditiveMonoid(LRD.TR))
  module EUMap = RDMap

  module DefAPPair = struct
    type t = DefAP.t * DefAP.t deriving (Show, Compare)
    let format = Show_t.format
    let show = Show_t.show
    let compare = Compare_t.compare
    let hash (x, y) = Hashtbl.hash (DefAP.hash x, DefAP.hash y)
    let equal x y = compare x y = 0
  end
  module PartialFlowMap =
    Monoid.FunctionSpace.Total.Ordered.Make
      (DefAP)
      (Ka.Ordered.AdditiveMonoid(CoLRD.TR))
  module FlowMap =
    Monoid.FunctionSpace.Total.Ordered.Make
      (DefAPPair)
      (Ka.Ordered.AdditiveMonoid(CoLRD.TR))

  (* Path types. *)
  type abspath = LK.TR.t deriving(Show,Compare)
  type rd = RDMap.t deriving(Show,Compare)
  type eu = EUMap.t deriving(Show,Compare)
  type du = FlowMap.t deriving(Show,Compare)

  (* Lifting functions. f is a function from lk to lrd/colrd predicates *)

  (* Lift an LKTransition to an LRDTransition *)
  let lift_lk f tr =
    let frame = LK.TR.get_frame tr in
    let f minterm rest =
      let eqs = LKMinterm.get_eqs minterm in
      let pred = f (LKMinterm.get_pred minterm) in
      let new_minterm = LRDMinterm.make eqs pred in
      let new_tr = LRD.TR.of_minterm frame new_minterm in
        LRD.TR.add new_tr rest
    in
      LK.TR.fold_minterms f tr LRD.TR.zero

  (* Lift an LKTransition to a CoLRDTransition
   * the "concurrent" branch of the transition gets unit predicate *)
  let lift_colk f tr =
    let frame = LK.TR.get_frame tr in
    let f minterm rest =
      let eqs = LKMinterm.get_eqs minterm in
      let pred = f (LKMinterm.get_pred minterm) in
      let new_minterm = CoLRDMinterm.make eqs (pred, LRDPred.unit) in
      let new_tr = CoLRD.TR.of_minterm frame new_minterm in
        CoLRD.TR.add new_tr rest
    in
      LK.TR.fold_minterms f tr CoLRD.TR.zero

  (* Lift an LRDTransition to a co LRDTransition.
   * the predicate is unchanged and the "concurrent" branch gets unit *)
  let lift_colrd tr =
    let frame = LRD.TR.get_frame tr in
    let f minterm rest =
      let eqs = LRDMinterm.get_eqs minterm in
      let (ls, k) = LRDMinterm.get_pred minterm in
      let new_minterm = CoLRDMinterm.make eqs ((LockPred.clear_fst ls, k),
                                               LRDPred.unit)
      in
      let new_tr = CoLRD.TR.of_minterm frame new_minterm in
        CoLRD.TR.add new_tr rest
    in
      LRD.TR.fold_minterms f tr CoLRD.TR.zero

  (* predicate transformations. id is obvious, left lifts to a path left of the
   * midpoint, right lifts to a path to the right of the midpoint. conc lifts to
   * a pure equality path, e.g. to the left of a fork *)
  let left (lk, _) = (lk, RDPred.unit)
  let id (lk, kl) = (lk, { SeqDep.current_name = None; SeqDep.killed = kl })
  let right (lk, kl) = (LockPred.clear_fst lk, 
                        { SeqDep.current_name = None; SeqDep.killed = kl })
  let conc (_, _) = (LockPred.unit, RDPred.unit)

  (* Remove dead definitions (definitions of memory locations which are
   overwritten later in the path) *)
  let filter_rd rd_tr =
    let frame = LRD.TR.get_frame rd_tr in
    let f minterm rest =
      let (locks, pred) = LRDMinterm.get_pred minterm in
      let add = match pred.SeqDep.current_name with
        | Some name -> not (AP.Set.mem name pred.SeqDep.killed)
        | None -> true
      in
        if add
        then LRD.TR.add (LRD.TR.of_minterm frame minterm) rest
        else rest
    in
      LRD.TR.fold_minterms f rd_tr LRD.TR.zero

  (* Remove "trees" that can't be interleaved (beginning or ending locksets have
   * non-empty intersection) or have dead definitions/uses (definitions/uses of
   * locations overwritten in either branch *)
  let filter_flow du_tr =
    let frame = CoLRD.TR.get_frame du_tr in
    let f minterm rest =
      let subst = CoLRDMinterm.get_subst minterm in
      let ((ls1, k1), (ls2, k2)) = CoLRDMinterm.get_pred minterm in
      let kills = AP.Set.union k1.SeqDep.killed k2.SeqDep.killed in
      let killed name = match name with
        | Some ap -> AP.Set.mem (AP.subst_var subst ap) kills
        | None -> false
      in
        if (AP.Set.is_empty (AP.Set.inter (fst ls1).LockPred.LP.acq
                                          (fst ls2).LockPred.LP.acq))
        && (AP.Set.is_empty (AP.Set.inter (snd ls1).LockPred.LP.acq
                                          (snd ls2).LockPred.LP.acq))
        && not (killed k1.SeqDep.current_name)
        && not (killed k2.SeqDep.current_name)
        then CoLRD.TR.add (CoLRD.TR.of_minterm frame minterm) rest
        else rest
    in
      CoLRD.TR.fold_minterms f du_tr CoLRD.TR.zero

  (* Filtering when the ending point of the sequential path is not known -- we
   * can filter out paths with a non-zero intersection for the initial locksets
   * and with the access paths killed *)
  let filter_partial_flow du_tr =
    let frame = CoLRD.TR.get_frame du_tr in
    let f minterm rest =
      let subst = CoLRDMinterm.get_subst minterm in
      let ((ls1, k1), (ls2, k2)) = CoLRDMinterm.get_pred minterm in
      let kills = AP.Set.union k1.SeqDep.killed k2.SeqDep.killed in
      let killed name = match name with
        | Some ap -> AP.Set.mem (AP.subst_var subst ap) kills
        | None -> false
      in
        if (AP.Set.is_empty (AP.Set.inter (fst ls1).LockPred.LP.acq
                                          (fst ls2).LockPred.LP.acq))
        && not (killed k1.SeqDep.current_name)
        && not (killed k2.SeqDep.current_name)
        then CoLRD.TR.add (CoLRD.TR.of_minterm frame minterm) rest
        else rest
    in
      CoLRD.TR.fold_minterms f du_tr CoLRD.TR.zero

  (* Multiply RDMap by an LRD transition *)
  let mul_right x y = 
    let update_rd tr = filter_rd (LRD.TR.mul tr y) in
      RDMap.map update_rd x

  let mul_left x y = 
    let update_rd tr = filter_rd (LRD.TR.mul y tr) in
      RDMap.map update_rd x

  (* Multiply FlowMap by a CoLRD transition *)
  let mul_coright f x y =
    let update_du tr = f (CoLRD.TR.mul tr y) in
      FlowMap.map update_du x

  let mul_coleft f x y =
    let update_du tr = f (CoLRD.TR.mul y tr) in
      FlowMap.map update_du x

  (* Multiply FlowMap by a CoLRD transition *)
  let mul_flow_uses f ud eu =
    let h acc (((d, d_ap), (_, _)), d_tr) ((u, u_ap), u_tr) =
      let tr = f (CoLRD.TR.mul d_tr (lift_colrd u_tr)) in
        if Pa.may_alias d_ap u_ap
        then FlowMap.update ((d, d_ap), (u, u_ap)) tr acc
        else acc
    in
    let g acc flow = BatEnum.fold (fun acc -> h acc flow) acc (EUMap.enum eu) in 
      BatEnum.fold g FlowMap.unit (FlowMap.enum ud)

  let interleave tr con_tr =
    let frame =
      Var.Set.union (LRD.TR.get_frame tr) (LRD.TR.get_frame con_tr)
    in
    let sub = LRDMinterm.subst (fun x -> if Var.get_subscript x = 1
                                         then Var.subscript x 3
                                         else x)
    in
    let g x y acc =
      let y' = sub y in
      let p1 = LRDMinterm.get_pred x in 
      let p2 = LRDMinterm.get_pred y' in 
      let eqs = LRDMinterm.get_eqs (LRDMinterm.mul x y') in
      let z = CoLRDMinterm.make eqs (p1, p2) in
        CoLRD.TR.add (CoLRD.TR.of_minterm frame z) acc
    in
    let f x acc = LRD.TR.fold_minterms (fun y -> g x y) con_tr acc in
      LRD.TR.fold_minterms f tr CoLRD.TR.zero

  (* Try all interleavings of paths in rd and eu, remove the impossible ones or
   * ones that kill the memory locations. con_use specifies whether the uses or
   * the definitions are concurrent *)
  let dflow f rd eu =
    let g acc ((d, d_ap), d_tr) ((u, u_ap), u_tr) =
      if Pa.may_alias d_ap u_ap
      then
        let du = f d_tr u_tr in
          FlowMap.mul acc (FlowMap.update ((d, d_ap), (u, u_ap)) du FlowMap.unit)
      else acc
    in
    let f acc def = BatEnum.fold (fun acc -> g acc def) acc (EUMap.enum eu) in
      if (not (rd = RDMap.unit)) && (not (eu = EUMap.unit))
      then begin
        let tmp = BatEnum.fold f FlowMap.unit (RDMap.enum rd) in
          Log.logf
            "dflow: **DEF** %a **USE** %a -> %a"
            RDMap.format rd
            EUMap.format eu
            FlowMap.format tmp;
          tmp
      end
      else FlowMap.unit

  let partial_flow_parent_child = dflow interleave
  let partial_flow_child_parent rd abs_p =
    let f acc ((d, d_ap), d_tr) =
      let du = interleave (lift_lk id abs_p) d_tr in
        FlowMap.mul acc (FlowMap.update ((d, d_ap), (d, d_ap)) du FlowMap.unit)
    in
      BatEnum.fold f FlowMap.unit (RDMap.enum rd)
  let flow_parent_child = dflow (fun d u -> filter_flow (interleave d u))
  let flow_child_parent = dflow (fun d u -> filter_flow (interleave u d))
  let flow_child_child = dflow (fun d u -> filter_flow (interleave d u))

                           (* Path types *)
  (* abspath   : --------- ls1, ls2, kills ------------- *)
  (* abspath_t : --------- ls2, kills ------------------| *)
  (* abspath_p : ---- ls1, ls2 ----|---- ls2, kills ---- *)
  (* rd        : ---- ls1, ls2 --(def)-- ls2, kills ---- *)
  (* rd_t      : ---- ls1, ls2 --(def)-- ls2, kills ----| *)
  (* rd_c      : ----(fork)----        ...         -----| *)
  (* eu        : --------- ls2, kills ----------------(use) *)
  (* eu_p      : ---- ls1, ls2 ----|---- ls2, kills --(use) *)
  (* rd_c      : ----(fork)----        ...         ---(use) *)
  (* du        : ---- ls1, ls2 --(fork)-- ls1, ls2 --(def)-- ls2, kills ----
   *             ----------------(fork)-- ls1, ls2 ----|---- ls2, kills --(use) *) 
  (* ud        : ---- ls1, ls2 --(fork)-- ls1, ls2 ----|---- ls2, kills ---- 
   *             ----------------(fork)-- ls1, ls2 --(def)-- ls2, kills ----| *) 
  (* du_t      : ---- ls1, ls2 --(fork)-- ls1, ls2 --(def)-- ls2, kills ----|
   *             ----------------(fork)-- ls1, ls2 ----|---- ls2, kills --(use)
   *           : ---- ls1, ls2 --(fork)-- ls1, ls2 ----|---- ls2, kills --(use)
   *             ----------------(fork)-- ls1, ls2 --(def)-- ls2, kills ----| *) 
  (* du_c      : ----(fork)----        ...         ---- *)
  module ConcReachingDefs = struct
    type var = Var.t
    type t = { abspath   : abspath;
               abspath_t : abspath;
               abspath_p : abspath;
               rd : rd;
               rd_t : rd;
               rd_c : rd;
               eu : eu;
               eu_p : eu;
               eu_c : eu;
               du   : du;  (* parent-->child flow, non-terminated *)
               ud   : du;  (* child-->parent flow, no use *)
               du_t : du;  (* child-->parent and parent-->child flow *)
               du_c : du   (* child-->child flow *) }
               deriving(Show,Compare)

    let compare = Compare_t.compare
    let format = Show_t.format
    let show = Show_t.show

    let equal a b = compare a b = 0

    let clear_fst =
      LK.TR.apply_pred (fun (ls, k) -> (LockPred.clear_fst ls, k))
    let clear_kill =
      LK.TR.apply_pred (fun (ls, k) -> (ls, AP.Set.empty))

    let zero = { abspath = LK.TR.zero;
                 abspath_t = LK.TR.zero;
                 abspath_p = LK.TR.zero;
                 rd = RDMap.unit;
                 rd_t = RDMap.unit;
                 rd_c = RDMap.unit;
                 eu = EUMap.unit;
                 eu_p = EUMap.unit;
                 eu_c = EUMap.unit;
                 du   = FlowMap.unit;
                 ud   = FlowMap.unit;
                 du_t = FlowMap.unit;
                 du_c = FlowMap.unit }
    let one = { abspath = LK.TR.one;
                abspath_t = LK.TR.one;
                abspath_p = LK.TR.one;
                rd = RDMap.unit;
                rd_t = RDMap.unit;
                rd_c = RDMap.unit;
                eu = EUMap.unit;
                eu_p = EUMap.unit;
                eu_c = EUMap.unit;
                du   = FlowMap.unit;
                ud   = FlowMap.unit;
                du_t = FlowMap.unit;
                du_c = FlowMap.unit }

    let mul a b =
      let brd   = mul_left b.rd   (lift_lk left a.abspath) in
      let brd_t = mul_left b.rd_t (lift_lk left a.abspath) in
      let brd_c = mul_left b.rd_c (lift_lk conc a.abspath) in
      let beu   = mul_left b.eu   (lift_lk right a.abspath) in
      let beu_p = mul_left b.eu_p (lift_lk left a.abspath) in
      let beu_c = mul_left b.eu_c (lift_lk conc a.abspath) in
        { abspath   = LK.TR.mul a.abspath b.abspath;
          abspath_t = LK.TR.add 
                        a.abspath_t 
                        (LK.TR.mul (clear_fst a.abspath) b.abspath_t);
          abspath_p = LK.TR.add 
                        (LK.TR.mul a.abspath_p (clear_fst b.abspath)) 
                        (LK.TR.mul (clear_kill a.abspath) b.abspath_p);
          rd   = RDMap.mul brd (mul_right a.rd (lift_lk right b.abspath));
          rd_t = RDMap.mul 
                   (RDMap.mul a.rd_t brd_t)
                   (mul_right a.rd (lift_lk id b.abspath_t));
          rd_c = RDMap.mul a.rd_c brd_c;
          eu   = EUMap.mul a.eu beu;
          eu_p = EUMap.mul 
                   (EUMap.mul a.eu_p beu_p)
                   (mul_left b.eu (lift_lk id a.abspath_p));
          eu_c = EUMap.mul a.eu_c beu_c;
          du   = FlowMap.mul
                   (mul_coleft filter_partial_flow b.du (lift_colk left a.abspath))
                   (FlowMap.mul
                      (mul_coright filter_partial_flow a.du (lift_colk right b.abspath))
                      (partial_flow_parent_child brd a.eu_c));
          ud   = FlowMap.mul
                   (mul_coleft filter_partial_flow b.ud (lift_colk left a.abspath))
                   (FlowMap.mul
                      (mul_coright filter_partial_flow a.ud (lift_colk right b.abspath))
                      (partial_flow_child_parent a.rd_c b.abspath_p));
          du_t = FlowMap.mul
                   (FlowMap.mul 
                      (mul_coright filter_flow a.du (lift_colk right a.abspath_t))
                      (mul_coleft filter_flow b.du_t (lift_colk left a.abspath)))
                   (FlowMap.mul
                      (FlowMap.mul
                         a.du_t 
                         (mul_flow_uses filter_flow a.ud b.eu))
                      (FlowMap.mul 
                         (flow_parent_child brd_t a.eu_c)
                         (flow_child_parent a.rd_c beu_p)));
          du_c = FlowMap.mul 
                   (FlowMap.mul
                      a.du_c 
                      (mul_coleft filter_flow b.du_c (lift_colk conc a.abspath)))
                   (FlowMap.mul 
                      (flow_child_child brd_c a.eu_c)
                      (flow_child_child a.rd_c beu_c)) }
 
    let add a b = { abspath = LK.TR.add a.abspath b.abspath;
                    abspath_t = LK.TR.add a.abspath_t b.abspath_t;
                    abspath_p = LK.TR.add a.abspath_p b.abspath_p;
                    rd = RDMap.mul a.rd b.rd;
                    rd_t = RDMap.mul a.rd_t b.rd_t;
                    rd_c = RDMap.mul a.rd_c b.rd_c;
                    eu = EUMap.mul a.eu b.eu;
                    eu_p = EUMap.mul a.eu_p b.eu_p;
                    eu_c = EUMap.mul a.eu_c b.eu_c;
                    du   = FlowMap.mul a.du b.du;
                    ud   = FlowMap.mul a.ud b.ud;
                    du_t = FlowMap.mul a.du_t b.du_t;
                    du_c = FlowMap.mul a.du_c b.du_c }
   
    let star a = 
      let abspath = LK.TR.star a.abspath in
      let abspath_t = LK.TR.mul (clear_fst abspath) a.abspath_t in
      let abspath_p = LK.TR.mul 
                        (LK.TR.mul (clear_kill abspath) a.abspath_p)
                        (clear_fst abspath)
      in
      let rd = mul_left 
                 (mul_right a.rd (lift_lk right abspath))
                 (lift_lk left abspath)
      in
      let rd_t = mul_right rd (lift_lk id a.abspath_t) in
      let rd_c = mul_left a.rd_c (lift_lk conc abspath) in
      let eu   = mul_left a.eu (lift_lk right abspath) in
      let eu_p = mul_left a.eu (lift_lk id abspath_p) in
      let eu_c = mul_left a.eu_c (lift_lk conc abspath) in
        { abspath = abspath;
          abspath_t = abspath_t;
          abspath_p = abspath_p;
          rd   = rd;
          rd_t = rd_t;
          rd_c = rd_c;
          eu   = eu;
          eu_p = eu_p;
          eu_c = eu_c;
          du   = partial_flow_parent_child rd eu_c;
          ud   = partial_flow_child_parent rd_c abspath_p;
          du_t = FlowMap.mul
                   (flow_parent_child rd_t eu_c)
                   (flow_child_parent rd_c eu_p);
          du_c = flow_child_child rd_c eu_c }

    let exists f a =
      let g ((def, ap), rd) = match ap with
        | Variable v when not (f v) -> LRD.TR.zero
        | _ -> LRD.TR.exists f rd
      in
      let remove_locals rd =
        let h acc (da, rd) = RDMap.update da (g (da, rd)) acc in
          BatEnum.fold h RDMap.unit (RDMap.enum rd)
      in
      let remove_locals_flow du =
        let h acc (x, du) =
          FlowMap.update x (CoLRD.TR.exists f du) acc
        in
          BatEnum.fold h FlowMap.unit (FlowMap.enum du)
      in
        { abspath = LK.TR.exists f a.abspath;
          abspath_t = LK.TR.exists f a.abspath_t;
          abspath_p = LK.TR.exists f a.abspath_p;
          rd = remove_locals a.rd;
          rd_t = remove_locals a.rd_t;
          rd_c = remove_locals a.rd_c;
          eu = remove_locals a.eu;
          eu_p = remove_locals a.eu_p;
          eu_c = remove_locals a.eu_c;
          du   = remove_locals_flow a.du;
          ud   = remove_locals_flow a.ud;
          du_t = remove_locals_flow a.du_t;
          du_c = remove_locals_flow a.du_c }

    let widen = add
    let fork a = { one with rd_c = RDMap.mul a.rd_t a.rd_c;
                            eu_c = EUMap.mul a.eu_p a.eu_c;
                            du_c = FlowMap.mul a.du_t a.du_c }
  end

  module ConcRDAnalysis = struct
    module Analysis = Interproc.MakeParPathExpr(ConcReachingDefs)
    open ConcReachingDefs

    let lk_weight def =
      let get_deref e = match e with 
        | AddrOf  ap -> AP.Set.singleton ap
        | _          -> AP.Set.singleton (Deref e)
      in
      let assign_weight lhs rhs =
        let ls   = LockPred.unit in
        let kill = AP.Set.singleton (AP.subscript 0 lhs) in
          LK.TR.assign lhs rhs (ls, kill)
      in
      let assume_weight be =
        let ls   = LockPred.unit in
        let kill = AP.Set.map (AP.subscript 0) (Bexpr.get_uses be) in
          LK.TR.assume be (Bexpr.free_vars be) (ls, kill)
      in
      let acq_weight e =
        let ls   = LockPred.make_acq (get_deref e) in
        let kill = AP.Set.empty in
          LK.TR.assume Bexpr.ktrue (Expr.free_vars e) (ls, kill)
      in
      let rel_weight e =
        let ls   = LockPred.make_rel (get_deref e) in
        let kill = AP.Set.empty in
          LK.TR.assume Bexpr.ktrue (Expr.free_vars e) (ls, kill)
      in
        match def.dkind with
          | Assign (lhs, rhs) -> assign_weight (Variable lhs) rhs
          | Store  (lhs, rhs) -> assign_weight lhs rhs
          | Assume be | Assert (be, _) -> assume_weight be
          | AssertMemSafe (e, s) -> assume_weight (Bexpr.of_expr e)
          | Builtin (Alloc (lhs, _, _)) -> assign_weight (Variable lhs) (Havoc (Var.get_type lhs))
          | Builtin Exit -> LK.TR.zero
          | Builtin (Acquire e) -> acq_weight e
          | Builtin (Release e) -> rel_weight e
          | Call   (vo, e, elst) -> failwith "Conc dep: Call encountered"
          | Return eo            -> failwith "Conc dep: Return encountered"
          | _ -> LK.TR.one

    let rd_weight def =
      let assign_weight lhs rhs = 
        let pred = (LockPred.pred_weight def, 
                    { SeqDep.current_name = Some (AP.subscript 0 lhs);
                      SeqDep.killed = AP.Set.empty })
        in
          RDMap.update (def, lhs) (LRD.TR.assign lhs rhs pred) RDMap.unit
      in
      let assume_weight bexpr =
        let uses = Bexpr.get_uses bexpr in
        let f ap acc = 
          let pred = (LockPred.pred_weight def, 
                      { SeqDep.current_name = Some (AP.subscript 0 ap);
                        SeqDep.killed = AP.Set.empty })
          in
          let tr = LRD.TR.assume bexpr (AP.free_vars ap) pred in
            RDMap.update (def, ap) tr acc
        in
          AP.Set.fold f uses RDMap.unit
      in
        match def.dkind with
          | Store (lhs, rhs) -> assign_weight lhs rhs
          | Assign (lhs, rhs) -> assign_weight (Variable lhs) rhs
          | Assume be | Assert (be, _) -> assume_weight be
          | AssertMemSafe (e, _) -> assume_weight (Bexpr.of_expr e)
          (* Doesn't handle offsets at the moment *)
          | Builtin (Alloc (lhs, _, _)) -> assign_weight (Variable lhs) (Havoc (Var.get_type lhs))
          | _ -> RDMap.unit

    module Stab = LockLogic.Stabilizer(LKMinterm)

    let weight def =
      let abspath = (Stab.stabilise lk_weight) def in
      let rd = rd_weight def in
      let eu = 
        let f ap acc = 
          let pred = (LockPred.pred_weight def, 
                      { SeqDep.current_name = Some (AP.subscript 0 ap);
                        SeqDep.killed = AP.Set.empty })
          in
          let tr   = LRD.TR.assume Bexpr.ktrue (AP.free_vars ap) pred in
            EUMap.update (def, ap) tr acc
        in
          AP.Set.fold f (Def.get_uses def) EUMap.unit
      in
        { abspath = abspath;
          abspath_t = clear_fst abspath;
          abspath_p = abspath;
          rd = rd;
          rd_t = rd;
          rd_c = RDMap.unit;
          eu = eu;
          eu_p = eu;
          eu_c = EUMap.unit;
          du   = FlowMap.unit;
          ud   = FlowMap.unit;
          du_t = FlowMap.unit;
          du_c = FlowMap.unit }


    let analyze file =
      let root = match file.entry_points with
        | [main] -> main
        | _      -> assert false
      in
      let rg = Interproc.make_recgraph file in
        Analysis.mk_query rg weight Interproc.local root

    let add_conc_edges rg root dg =
      let query = Analysis.mk_query rg weight Interproc.local root in
      let summary = Analysis.get_summary query root in
      let g (((def1, ap1), (def2, ap2)), tmp) =
        if (filter_flow tmp) != CoLRD.TR.zero then
          DG.add_edge_e dg (DG.E.create def1 (Pack.PairSet.singleton (Pack.mk_pair ap1 ap2)) def2)
      in
        BatEnum.iter g (FlowMap.enum summary.du_t);
        BatEnum.iter g (FlowMap.enum summary.du_c)
          (*
    let add_conc_edges rg root dg =
      let query = Analysis.mk_query rg weight Interproc.local root in
      let summary = Analysis.get_summary query root in
      let g (((def1, ap1), (def2, ap2)), _) =
        DG.add_edge_e dg (DG.E.create def1 (Pack.PairSet.singleton (Pack.mk_pair ap1 ap2)) def2)
      in
        BatEnum.iter g (FlowMap.enum (flow_parent_child summary.rd_t summary.eu_c));
        BatEnum.iter g (FlowMap.enum (flow_child_parent summary.rd_c summary.eu_p));
        BatEnum.iter g (FlowMap.enum (flow_child_child summary.rd_c summary.eu_c))
           *)

  end
end

module ConcDep = Make(EqLogic.Hashed.MakeEQ(Var))
module ConcTrivDep = Make(EqLogic.Hashed.MakeTrivEQ(Var))

let construct_conc_dg file =
  let root = match file.entry_points with
    | [main] -> main
    | _ -> assert false
  in
  let rg = Interproc.make_recgraph file in
  let dg =
    ignore(LockLogic.find_races rg root);
    if !AliasLogic.must_alias then 
      ConcDep.SeqDep.construct_dg ~solver:(ConcDep.SeqDep.RDAnalysisConc.solve rg root) file
    else 
      ConcTrivDep.SeqDep.construct_dg ~solver:(ConcTrivDep.SeqDep.RDAnalysisConc.solve rg root) file
  in
    ConcDep.ConcRDAnalysis.add_conc_edges rg root dg;
    if !CmdLine.display_graphs then DG.display_labelled dg;
    dg

let chdfg_stats file =
  let dg = Log.phase "Construct hDFG" construct_conc_dg file in
    print_endline ("Vertices: " ^ (string_of_int (DG.nb_vertex dg)));
    print_endline ("Edges: " ^ (string_of_int (DG.nb_edges dg)))

let _ =
  CmdLine.register_pass 
    ("-chdfg-stats", chdfg_stats, " Concurrent heap data flow graph statistics")

module InvGen = Solve.MakeAfgSolver(Ai.ApronInterpretation)
let invariant_generation file =
  let dg = Log.phase "Construct hDFG" construct_conc_dg file in
  let state = InvGen.mk_state dg in
  let map = InvGen.do_analysis state dg in
  InvGen.check_assertions dg map

let _ =
  CmdLine.register_pass
    ("-chdfg",
     invariant_generation,
     " Invariant generation with concurrent heap data flow graph")
