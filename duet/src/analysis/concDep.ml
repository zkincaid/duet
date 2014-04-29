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

      let pred_unit = Minterm.get_pred Minterm.unit
      let sub_index i j x = if Var.get_subscript x = i then Var.subscript x j else x

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

      let mul_pointed x y =
        let frame_x = get_frame x in
        let frame_y = get_frame y in
        let x_minus_y = Var.Set.diff frame_x frame_y in
        let y_minus_x = Var.Set.diff frame_y frame_x in
        let x_eqs =
          subst (sub_index 1 3) (assume Bexpr.ktrue y_minus_x pred_unit)
        in
        let y_eqs =
          subst (sub_index 0 3) (assume Bexpr.ktrue x_minus_y pred_unit)
        in
          mul (mul x x_eqs) (mul y y_eqs)

      let make_pointed x y =
        let frame_x = get_frame x in
        let frame_y = get_frame y in
        let x_minus_y = Var.Set.diff frame_x frame_y in
        let y_minus_x = Var.Set.diff frame_y frame_x in
        let x' = mul x (assume Bexpr.ktrue y_minus_x pred_unit) in
        let y' = mul y (assume Bexpr.ktrue x_minus_y pred_unit) in
          mul (subst (sub_index 1 3) x') (subst (sub_index 0 3) y')
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

  module TreePred = LockLogic.CombinePred(Var)(LRDPred)(LRDPred)
  module TreeMinterm = MakeEQ(TreePred)
  module Tree = MakeFormula(TreeMinterm)

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
  module PartialTreeMap =
    Monoid.FunctionSpace.Total.Ordered.Make
      (DefAP)
      (Ka.Ordered.AdditiveMonoid(Tree.TR))
  module TreeMap =
    Monoid.FunctionSpace.Total.Ordered.Make
      (DefAPPair)
      (Ka.Ordered.AdditiveMonoid(Tree.TR))

  (* Lifting functions. f is a function from lk to lrd/colrd predicates *)

  (* Lift an LK Transition to an LRD Transition
   * The "current name" is always None *)
  let lift_lk_lrd f tr =
    let frame = LK.TR.get_frame tr in
    let f minterm rest =
      let eqs = LKMinterm.get_eqs minterm in
      let pred = f (LKMinterm.get_pred minterm) in
      let new_minterm = LRDMinterm.make eqs pred in
      let new_tr = LRD.TR.of_minterm frame new_minterm in
        LRD.TR.add new_tr rest
    in
      LK.TR.fold_minterms f tr LRD.TR.zero

  (* Lift an LK Transition to the left-hand branch of a Tree Transition *)
  let lift_lk_tree f tr =
    let frame = LK.TR.get_frame tr in
    let f minterm rest =
      let eqs = LKMinterm.get_eqs minterm in
      let pred = f (LKMinterm.get_pred minterm) in
      let new_minterm = TreeMinterm.make eqs (pred, LRDPred.unit) in
      let new_tr = Tree.TR.of_minterm frame new_minterm in
        Tree.TR.add new_tr rest
    in
      LK.TR.fold_minterms f tr Tree.TR.zero

  (* Lift an LRD Transition to the left-hand branch of a Tree Transition *)
  let lift_lrd_tree tr =
    let frame = LRD.TR.get_frame tr in
    let f minterm rest =
      let eqs = LRDMinterm.get_eqs minterm in
      let pred = LRDMinterm.get_pred minterm in
      let new_minterm = TreeMinterm.make eqs (pred, LRDPred.unit) in
      let new_tr = Tree.TR.of_minterm frame new_minterm in
        Tree.TR.add new_tr rest
    in
      LRD.TR.fold_minterms f tr Tree.TR.zero

  (* Lift an LRD Transition to the right-hand branch of a Tree Transition *)
  let lift_lrd_tree_right tr =
    let frame = LRD.TR.get_frame tr in
    let f minterm rest =
      let eqs = LRDMinterm.get_eqs minterm in
      let pred = LRDMinterm.get_pred minterm in
      let new_minterm = TreeMinterm.make eqs (LRDPred.unit, pred) in
      let new_tr = Tree.TR.of_minterm frame new_minterm in
        Tree.TR.add new_tr rest
    in
      LRD.TR.fold_minterms f tr Tree.TR.zero

  (* predicate transformations. id is obvious, left lifts to a path left of the
   * midpoint, right lifts to a path to the right of the midpoint. conc lifts to
   * a pure equality path, e.g. to the left of a fork *)
  let locks (lk, _) = (lk, RDPred.unit)
  let all (lk, kl) = (lk, { SeqDep.current_name = None; SeqDep.killed = kl })
  let lock_kill (lk, kl) = (LockPred.clear_fst lk, 
                        { SeqDep.current_name = None; SeqDep.killed = kl })
  let none (_, _) = (LockPred.unit, RDPred.unit)

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
  let filter_tree g tr =
    let frame = Tree.TR.get_frame tr in
    let f minterm rest =
      let subst = TreeMinterm.get_subst minterm in
      let ((ls1, k1), (ls2, k2)) = TreeMinterm.get_pred minterm in
      let kills = AP.Set.union k1.SeqDep.killed k2.SeqDep.killed in
      let killed name = match name with
        | Some ap -> AP.Set.mem (AP.subst_var subst ap) kills
        | None -> false
      in
        if (g ls1 ls2)
           && not (killed k1.SeqDep.current_name)
           && not (killed k2.SeqDep.current_name)
        then Tree.TR.add (Tree.TR.of_minterm frame minterm) rest
        else rest
    in
      Tree.TR.fold_minterms f tr Tree.TR.zero

  let f_none x = x
  let f_part =
    let g ls1 ls2 =
      (AP.Set.is_empty (AP.Set.inter (fst ls1).LockPred.LP.acq
                                   (fst ls2).LockPred.LP.acq))
    in
      filter_tree g
  let f_all =
    let g ls1 ls2 =
      (AP.Set.is_empty (AP.Set.inter (fst ls1).LockPred.LP.acq
                                     (fst ls2).LockPred.LP.acq))
      && (AP.Set.is_empty (AP.Set.inter (snd ls1).LockPred.LP.acq
                                        (snd ls2).LockPred.LP.acq))
    in
      filter_tree g

  (* Multiply RDMap by an LRD transition *)
  let mul_right x y = 
    let update_rd tr = filter_rd (LRD.TR.mul tr y) in
      RDMap.map update_rd x

  let mul_left x y = 
    let update_rd tr = filter_rd (LRD.TR.mul y tr) in
      RDMap.map update_rd x

  (* Multiply PartialTreeMap by a Tree transition *)
  let mul_pt_right f x y =
    let update tr = f (Tree.TR.mul_pointed tr y) in
      PartialTreeMap.map update x

  let mul_pt_left f x y =
    let update tr = f (Tree.TR.mul_pointed y tr) in
      PartialTreeMap.map update x

  (* Multiply TreeMap by a Tree transition *)
  let mul_t_right f x y =
    let update tr = f (Tree.TR.mul_pointed tr y) in
      TreeMap.map update x

  let mul_t_left f x y =
    let update tr = f (Tree.TR.mul_pointed y tr) in
      TreeMap.map update x

  (* Multiply a partial tree map by an eu map *)
  let add_uses f x y =
    let g acc ((d, d_ap), d_tr) ((u, u_ap), u_tr) =
      if Pa.may_alias d_ap u_ap
      then begin
        let tr = f (Tree.TR.mul_pointed d_tr (lift_lrd_tree u_tr)) in
          if tr != Tree.TR.zero
          then TreeMap.update ((d, d_ap), (u, u_ap)) tr acc
          else acc
      end
      else acc
    in
    let f acc t = BatEnum.fold (fun acc -> g acc t) acc (EUMap.enum y) in
      BatEnum.fold f TreeMap.unit (PartialTreeMap.enum x)

  (* Multiply a partial tree map by an rd map *)
  let add_defs f x y =
    let g acc ((u, u_ap), u_tr) ((d, d_ap), d_tr) =
      if Pa.may_alias d_ap u_ap
      then begin
        let tr = f (Tree.TR.mul_pointed u_tr (lift_lrd_tree d_tr)) in
          if tr != Tree.TR.zero
          then TreeMap.update ((d, d_ap), (u, u_ap)) tr acc
          else acc
      end
      else acc
    in
    let f acc t = BatEnum.fold (fun acc -> g acc t) acc (RDMap.enum y) in
      BatEnum.fold f TreeMap.unit (PartialTreeMap.enum x)

  (* Quantify out the midpoint of the path, then change indices 4 to 1 *)
  let pivot_branch x =
    let frame = Tree.TR.get_frame x in
    let f m acc = 
      let tmp = 
        TreeMinterm.subst (Tree.TR.sub_index 4 1) 
          (TreeMinterm.exists (fun x -> Var.get_subscript x != 3) m)
      in
      let eqs = TreeMinterm.get_eqs tmp in
      let (_, pred) = TreeMinterm.get_pred tmp in
      let m' = TreeMinterm.make eqs (pred, LRDPred.unit) in
        Tree.TR.add (Tree.TR.of_minterm frame m') acc
    in
      Tree.TR.fold_minterms f x Tree.TR.zero

  let clear_left = Tree.TR.apply_pred (fun (_, p) -> (LRDPred.unit, p))

  (* Multiply a partial rd map by a partial eu map *)
  let mul_rd_eu x y =
    let g acc ((d, d_ap), d_tr) ((u, u_ap), u_tr) =
      if Pa.may_alias d_ap u_ap
      then begin
        let tr = f_all (Tree.TR.mul_pointed (clear_left d_tr) (pivot_branch u_tr)) in
          if tr != Tree.TR.zero
          then TreeMap.update ((d, d_ap), (u, u_ap)) tr acc
          else acc
      end
      else acc
    in
    let f acc t = BatEnum.fold (fun acc -> g acc t) acc (PartialTreeMap.enum y) in
      BatEnum.fold f TreeMap.unit (PartialTreeMap.enum x)

  (* Multiply a partial eu map by a partial rd map
   * quantify out the "fork point" of the def path, then change indices 4 to 1 *)
  let mul_eu_rd x y =
    let g acc ((u, u_ap), u_tr) ((d, d_ap), d_tr) =
      if Pa.may_alias d_ap u_ap
      then begin
        let tr = f_all (Tree.TR.mul_pointed (clear_left u_tr) (pivot_branch d_tr)) in
          if tr != Tree.TR.zero
          then TreeMap.update ((d, d_ap), (u, u_ap)) tr acc
          else acc
      end
      else acc
    in
    let f acc t = BatEnum.fold (fun acc -> g acc t) acc (PartialTreeMap.enum y) in
      BatEnum.fold f TreeMap.unit (PartialTreeMap.enum x)

  (* Make an rd or eu map a partial tree map *)
  let make_partial_tree x =
    let f acc (defap, tr) =

      let tr' =
        Tree.TR.subst (Tree.TR.sub_index 1 4) 
          (Tree.TR.make_pointed Tree.TR.one (lift_lrd_tree_right tr))
      in
        PartialTreeMap.update defap tr' acc
    in
      BatEnum.fold f PartialTreeMap.unit (RDMap.enum x)

                           (* Path types *)
  (* abspath   : --------- ls1, ls2, kills ------------- *)
  (* abspath_t : --------- ls2, kills ------------------| *)
  (* abspath_p : ---- ls1, ls2 ----|---- ls2, kills ---- *)
  (* rd        : ---- ls1, ls2 --(def)-- ls2, kills ---- *)
  (* rd_t      : ---- ls1, ls2 --(def)-- ls2, kills ----| *)
  (* eu        : --------- ls2, kills ----------------(use) *)
  (* eu_p      : ---- ls1, ls2 ----|---- ls2, kills --(use) *)
  (* rd_tree   : ---- ls1, ls2 ---frk--- ls1, ls2 -------------------------
   *                                 --- ls3, ls4 --(def)-- ls4, kills ----| *)
  (* rd_tree_p : ---- ls1, ls2 ---frk--- ls1, ls2 ----|---- ls2, kills ----
   *                                 --- ls3, ls4 --(def)-- ls4, kills ----| *)
  (* rd_tree_eu: ---- ls1, ls2 ---frk--- ls1, ls2 ----|---- ls2, kills --(use)
   *                                 --- ls3, ls4 --(def)-- ls4, kills ----| *)
  (* eu_tree   : ---- ls1, ls2 ---frk--- ls1, ls2 -------------------------
   *                                 --- ls3, ls4 ----|---- ls4, kills --(use) *)
  (* eu_tree   : ---- ls1, ls2 ---frk--- ls1, ls2 --(def)-- ls2, kills ----
   *                                 --- ls3, ls4 ----|---- ls4, kills --(use) *)
  (* eu_tree   : ---- ls1, ls2 ---frk--- ls1, ls2 --(def)-- ls2, kills ----|
   *                                 --- ls3, ls4 ----|---- ls4, kills --(use) *)
  (* tree_c    : -------frk-------frk
   *                                 --- ls1, ls2 ----|---- ls2, kills ----|
   *                       ------------- ls3, ls4 ----|---- ls4, kills ----| *)
  module ConcReachingDefs = struct
    type var = Var.t
    type t = { abspath   : LK.TR.t;
               abspath_t : LK.TR.t;
               abspath_p : LK.TR.t;
               rd   : RDMap.t;
               rd_t : RDMap.t;
               eu   : EUMap.t;
               eu_p : EUMap.t;
               rd_tree    : PartialTreeMap.t;
               rd_tree_p  : PartialTreeMap.t;
               rd_tree_eu : TreeMap.t;
               eu_tree    : PartialTreeMap.t;
               eu_tree_rd : TreeMap.t;
               eu_tree_t  : TreeMap.t;
               tree_c     : TreeMap.t }
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
                 eu = EUMap.unit;
                 eu_p = EUMap.unit;
                 rd_tree = PartialTreeMap.unit;
                 rd_tree_p = PartialTreeMap.unit;
                 rd_tree_eu = TreeMap.unit;
                 eu_tree = PartialTreeMap.unit;
                 eu_tree_rd = TreeMap.unit;
                 eu_tree_t = TreeMap.unit;
                 tree_c = TreeMap.unit }
    let one = { abspath = LK.TR.one;
                abspath_t = LK.TR.one;
                abspath_p = LK.TR.one;
                rd = RDMap.unit;
                rd_t = RDMap.unit;
                eu = EUMap.unit;
                eu_p = EUMap.unit;
                rd_tree = PartialTreeMap.unit;
                rd_tree_p = PartialTreeMap.unit;
                rd_tree_eu = TreeMap.unit;
                eu_tree = PartialTreeMap.unit;
                eu_tree_rd = TreeMap.unit;
                eu_tree_t = TreeMap.unit;
                tree_c = TreeMap.unit }

    let mul a b =
        { abspath   = LK.TR.mul a.abspath b.abspath;
          abspath_t = LK.TR.add 
                        a.abspath_t 
                        (LK.TR.mul (clear_fst a.abspath) b.abspath_t);
          abspath_p = LK.TR.add 
                        (LK.TR.mul a.abspath_p (clear_fst b.abspath)) 
                        (LK.TR.mul (clear_kill a.abspath) b.abspath_p);
          rd   = RDMap.mul 
                   (mul_right a.rd (lift_lk_lrd lock_kill b.abspath))
                   (mul_left b.rd (lift_lk_lrd locks a.abspath));
          rd_t = RDMap.mul 
                   (mul_right a.rd (lift_lk_lrd all b.abspath_t))
                   (RDMap.mul
                      a.rd_t
                      (mul_left b.rd_t (lift_lk_lrd locks a.abspath)));
          eu   = EUMap.mul
                   a.eu
                   (mul_left b.eu (lift_lk_lrd lock_kill a.abspath));
          eu_p = EUMap.mul
                   (mul_left b.eu (lift_lk_lrd all a.abspath_p)) 
                   (EUMap.mul
                      a.eu_p 
                      (mul_left b.eu_p (lift_lk_lrd locks a.abspath)));
          rd_tree = PartialTreeMap.mul
                      (mul_pt_right f_none a.rd_tree (lift_lk_tree locks b.abspath))
                      (mul_pt_left f_none b.rd_tree (lift_lk_tree locks a.abspath));
          rd_tree_p = PartialTreeMap.mul
                        (mul_pt_right f_part a.rd_tree (lift_lk_tree all b.abspath_p))
                        (PartialTreeMap.mul
                           (mul_pt_right f_part a.rd_tree_p (lift_lk_tree lock_kill b.abspath))
                           (mul_pt_left f_part b.rd_tree_p (lift_lk_tree locks a.abspath)));
          rd_tree_eu = TreeMap.mul 
                         (TreeMap.mul
                            (add_uses f_all a.rd_tree_p b.eu)
                            (add_uses f_all a.rd_tree b.eu_p))
                         (TreeMap.mul
                            a.rd_tree_eu
                            (mul_t_left f_all b.rd_tree_eu (lift_lk_tree locks a.abspath)));
          eu_tree = PartialTreeMap.mul
                      (mul_pt_right f_none a.eu_tree (lift_lk_tree locks b.abspath))
                      (mul_pt_left f_none b.eu_tree (lift_lk_tree locks a.abspath));
          eu_tree_rd = TreeMap.mul
                         (add_defs f_part a.eu_tree b.rd)
                         (TreeMap.mul
                            (mul_t_right f_part a.eu_tree_rd (lift_lk_tree lock_kill b.abspath))
                            (mul_t_left f_part b.eu_tree_rd (lift_lk_tree locks a.abspath)));
          eu_tree_t = TreeMap.mul
                        (TreeMap.mul
                           (mul_t_right f_all a.eu_tree_rd (lift_lk_tree all b.abspath_t))
                           (add_defs f_all a.eu_tree b.rd_t))
                        (TreeMap.mul
                           a.eu_tree_t
                           (mul_t_left f_all b.eu_tree_t (lift_lk_tree locks a.abspath)));
          tree_c = TreeMap.mul
                     (TreeMap.mul
                        (mul_rd_eu a.rd_tree b.eu_tree)
                        (mul_eu_rd a.eu_tree b.rd_tree))
                     (TreeMap.mul
                        a.tree_c
                        (mul_t_left f_all b.tree_c (lift_lk_tree none a.abspath))) }
 
    let add a b = { abspath = LK.TR.add a.abspath b.abspath;
                    abspath_t = LK.TR.add a.abspath_t b.abspath_t;
                    abspath_p = LK.TR.add a.abspath_p b.abspath_p;
                    rd = RDMap.mul a.rd b.rd;
                    rd_t = RDMap.mul a.rd_t b.rd_t;
                    eu = EUMap.mul a.eu b.eu;
                    eu_p = EUMap.mul a.eu_p b.eu_p;
                    rd_tree = PartialTreeMap.mul a.rd_tree b.rd_tree;
                    rd_tree_p = PartialTreeMap.mul a.rd_tree_p b.rd_tree_p;
                    rd_tree_eu = TreeMap.mul a.rd_tree_eu b.rd_tree_eu;
                    eu_tree = PartialTreeMap.mul a.eu_tree b.eu_tree;
                    eu_tree_rd = TreeMap.mul a.eu_tree_rd b.eu_tree_rd;
                    eu_tree_t = TreeMap.mul a.eu_tree_t b.eu_tree_t;
                    tree_c = TreeMap.mul a.tree_c b.tree_c }
   
    let star a = 
      let abspath = LK.TR.star a.abspath in
      let abspath_t = LK.TR.mul (clear_fst abspath) a.abspath_t in
      let abspath_p = LK.TR.mul 
                        (LK.TR.mul (clear_kill abspath) a.abspath_p)
                        (clear_fst abspath)
      in
      let rd =
        mul_left (mul_right a.rd (lift_lk_lrd lock_kill abspath))
                 (lift_lk_lrd locks abspath)
      in
      let rd_t = mul_right rd (lift_lk_lrd all a.abspath_t) in
      let eu   = mul_left a.eu (lift_lk_lrd lock_kill abspath) in
      let eu_p = mul_left a.eu (lift_lk_lrd all abspath_p) in
      let rd_tree =
        mul_pt_left f_none 
          (mul_pt_right f_none a.rd_tree (lift_lk_tree locks abspath))
          (lift_lk_tree locks abspath)
      in
      let rd_tree_p = mul_pt_right f_part rd_tree (lift_lk_tree all abspath_p) in
      let rd_tree_eu = add_uses f_all rd_tree_p a.eu in
      let eu_tree =
        mul_pt_left f_none 
          (mul_pt_right f_none a.eu_tree (lift_lk_tree locks abspath))
          (lift_lk_tree locks abspath)
      in
      let eu_tree_rd = add_defs f_part eu_tree rd in
      let eu_tree_t = mul_t_right f_all eu_tree_rd (lift_lk_tree all a.abspath_t) in
      let tree_c =
        TreeMap.mul (mul_rd_eu rd_tree eu_tree) (mul_eu_rd eu_tree rd_tree) 
      in
        { abspath = abspath;
          abspath_t = abspath_t;
          abspath_p = abspath_p;
          rd   = rd;
          rd_t = rd_t;
          eu   = eu;
          eu_p = eu_p;
          rd_tree = rd_tree;
          rd_tree_p = rd_tree_p;
          rd_tree_eu = rd_tree_eu;
          eu_tree = eu_tree;
          eu_tree_rd = eu_tree_rd;
          eu_tree_t = eu_tree_t;
          tree_c = tree_c }

    let exists f a =
      let g ((def, ap), rd) = match ap with
        | Variable v when not (f v) -> LRD.TR.zero
        | _ -> LRD.TR.exists f rd
      in
      let remove_locals rd =
        let h acc (da, rd) = RDMap.update da (g (da, rd)) acc in
          BatEnum.fold h RDMap.unit (RDMap.enum rd)
      in
      let remove_locals_pt du =
        let h acc (x, du) =
          PartialTreeMap.update x (Tree.TR.exists f du) acc
        in
          BatEnum.fold h PartialTreeMap.unit (PartialTreeMap.enum du)
      in
      let remove_locals_t du =
        let h acc (x, du) =
          TreeMap.update x (Tree.TR.exists f du) acc
        in
          BatEnum.fold h TreeMap.unit (TreeMap.enum du)
      in
        { abspath = LK.TR.exists f a.abspath;
          abspath_t = LK.TR.exists f a.abspath_t;
          abspath_p = LK.TR.exists f a.abspath_p;
          rd = remove_locals a.rd;
          rd_t = remove_locals a.rd_t;
          eu = remove_locals a.eu;
          eu_p = remove_locals a.eu_p;
          rd_tree = remove_locals_pt a.rd_tree;
          rd_tree_p = remove_locals_pt a.rd_tree_p;
          rd_tree_eu = remove_locals_t a.rd_tree_eu;
          eu_tree = remove_locals_pt a.eu_tree;
          eu_tree_rd = remove_locals_t a.eu_tree_rd;
          eu_tree_t = remove_locals_t a.eu_tree_t;
          tree_c = remove_locals_t a.tree_c }

    let widen = add
    let fork a = 
      { one with
            rd_tree = make_partial_tree a.rd_t;
            eu_tree = make_partial_tree a.eu_p;
            tree_c = TreeMap.mul (TreeMap.mul a.rd_tree_eu a.eu_tree_t) a.tree_c }
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
          eu = eu;
          eu_p = eu;
          rd_tree = PartialTreeMap.unit;
          rd_tree_p = PartialTreeMap.unit;
          rd_tree_eu = TreeMap.unit;
          eu_tree = PartialTreeMap.unit;
          eu_tree_rd = TreeMap.unit;
          eu_tree_t = TreeMap.unit;
          tree_c = TreeMap.unit }


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
       (* if (filter_flow tmp) != Tree.TR.zero then*)
          DG.add_edge_e dg (DG.E.create def1 (Pack.PairSet.singleton (Pack.mk_pair ap1 ap2)) def2)
      in
        BatEnum.iter g (TreeMap.enum summary.rd_tree_eu);
        BatEnum.iter g (TreeMap.enum summary.eu_tree_t);
        BatEnum.iter g (TreeMap.enum summary.tree_c)
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
