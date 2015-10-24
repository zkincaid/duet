open Core
open CfgIr
open Apak
open EqLogic

module DG = Afg.G
module Pack = Afg.Pack

let conc_edges = ref true

let _ =
  CmdLine.register_config
    ("-no-conc-edges", Arg.Clear conc_edges, " Disable concurrent data flow edges") 

(* True if the variable may be used concurrently *)
let may_use_conc v = Var.is_shared v || Varinfo.addr_taken (fst v)

(* Two point lock sets *)
module LockPred = struct
  module LP = LockLogic.LockPred
  include LockLogic.CombinePred(Var)(LP)(LP)
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

      let make_tree x =
        let frame = get_frame x in
        let eqs =
          Var.Set.fold
            (fun v -> fun acc -> (Var.subscript v 0, Var.subscript v 3) ::
                                 (Var.subscript v 3, Var.subscript v 1) :: acc)
            frame
            []
        in
        let f m =
          let m' = Minterm.subst (sub_index 1 4) m in
          add (of_minterm frame (Minterm.make (eqs @ (Minterm.get_eqs m'))
                                   (Minterm.get_pred m')))
        in
        fold_minterms f x zero

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

    let filter x =
      let kills = match x.SeqDep.current_name with
        (* | Some (Variable v) -> AP.Set.filter (imprecise v) x.SeqDep.killed*)
        | Some ap ->
          AP.Set.filter (PointerAnalysis.may_alias ap) x.SeqDep.killed
        | _ -> x.SeqDep.killed
      in
      { x with SeqDep.killed = kills }

    let mul x y =
      filter (SeqDep.RDPred.mul x y)

    let pred_weight def = unit
  end

  module LRDPred = LockLogic.CombinePred(Var)(LockPred)(RDPred)
  module LRDMinterm = MakeEQ(LRDPred)
  module LRD = MakeFormula(LRDMinterm)

  module TreePred = LockLogic.CombinePred(Var)(LRDPred)(LRDPred)
  module TreeMinterm = MakeEQ(TreePred)
  module Tree = MakeFormula(TreeMinterm)

  module DefAP = struct
    type t = Def.t * AP.t [@@deriving show,ord]
    let hash (def, ap) = Hashtbl.hash (Def.hash def, AP.hash ap)
    let equal x y = compare x y = 0
  end
  module RDMap =
    Monoid.FunctionSpace.Total.Ordered.Make
      (DefAP)
      (Ka.Ordered.AdditiveMonoid(LRD.TR))
  module EUMap = RDMap

  module DefAPPair = struct
    type t = DefAP.t * DefAP.t [@@deriving show,ord]
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

  (* Find a variable equality for two aliased access paths *)
  let unify a b =
    let unify e e' =
      let vs = Var.Set.filter
          (fun v -> is_pointer_type (Var.get_type v)) (Expr.free_vars e)
      in
      let vs' = Var.Set.filter
          (fun v -> is_pointer_type (Var.get_type v)) (Expr.free_vars e')
      in
      let v  = Var.Set.choose vs  in
      let v' = Var.Set.choose vs' in
      if e = (Expr.subst_var (fun v'' -> if v' = v'' then v else v'') e')
      then [(v, v')]
      else []
    in
    match (a, b) with
    | (Some (Variable v), Some (Variable u)) -> [(v, u)]
    | (Some (Deref e), Some (Deref e')) -> begin try unify e e'
        with Not_found -> []
      end
    | _ -> []

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
    let update tr = f (Tree.TR.mul tr y) in
    PartialTreeMap.map update x

  let mul_pt_left f x y =
    let update tr = f (Tree.TR.mul y tr) in
    PartialTreeMap.map update x

  (* Multiply TreeMap by a Tree transition *)
  let mul_t_right f x y =
    let update tr = f (Tree.TR.mul tr y) in
    TreeMap.map update x

  let mul_t_left f x y =
    let update tr = f (Tree.TR.mul y tr) in
    TreeMap.map update x

  let mul_eq tr tr' =
    let tr'' = Tree.TR.mul tr tr' in
    let frame = Tree.TR.get_frame tr'' in
    let f m acc =
      let ((ls1, k1), (ls2, k2)) = TreeMinterm.get_pred m in
      Tree.TR.add (Tree.TR.of_minterm frame
                     (TreeMinterm.make
                        ((unify k1.SeqDep.current_name k2.SeqDep.current_name)
                         @ TreeMinterm.get_eqs m)
                        ((ls1, k1), (ls2, k2))))
        acc
    in
    Tree.TR.fold_minterms f tr'' Tree.TR.zero

  (* Multiply a partial tree map by an eu map *)
  let add_uses f x y =
    let g acc ((d, d_ap), d_tr) ((u, u_ap), u_tr) =
      if PointerAnalysis.may_alias d_ap u_ap
      then begin
        let tr = f (mul_eq d_tr (lift_lrd_tree u_tr)) in
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
      if PointerAnalysis.may_alias d_ap u_ap
      then begin
        let tr = f (mul_eq u_tr (lift_lrd_tree d_tr)) in
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
        let f x =
          let sub = Var.get_subscript x in
          sub != 3 && sub != 1
        in
        TreeMinterm.subst (Tree.TR.sub_index 4 1) (TreeMinterm.exists f m)
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
      if PointerAnalysis.may_alias d_ap u_ap
      then begin
        let tr = f_all (mul_eq (clear_left d_tr) (pivot_branch u_tr)) in
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
      if PointerAnalysis.may_alias d_ap u_ap
      then begin
        let tr = f_all (mul_eq (clear_left u_tr) (pivot_branch d_tr)) in
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
      let tr' = Tree.TR.make_tree (lift_lrd_tree_right tr) in
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
        [@@deriving show,ord]

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
      let a_lk_lrd = lift_lk_lrd lock_kill a.abspath in
      let a_locks_lrd = lift_lk_lrd locks a.abspath in
      let b_lk_lrd = lift_lk_lrd lock_kill b.abspath in
      let a_locks_tree = lift_lk_tree locks a.abspath in
      let b_lk_tree = lift_lk_tree lock_kill b.abspath in
      let b_locks_tree = lift_lk_tree locks b.abspath in
      { abspath   = LK.TR.mul a.abspath b.abspath;
        abspath_t = LK.TR.add
            a.abspath_t
            (LK.TR.mul (clear_fst a.abspath) b.abspath_t);
        abspath_p = LK.TR.add
            (LK.TR.mul a.abspath_p (clear_fst b.abspath))
            (LK.TR.mul (clear_kill a.abspath) b.abspath_p);
        rd   = RDMap.mul (mul_right a.rd b_lk_lrd) (mul_left b.rd a_locks_lrd);
        rd_t = RDMap.mul
            (mul_right a.rd (lift_lk_lrd all b.abspath_t))
            (RDMap.mul a.rd_t (mul_left b.rd_t a_locks_lrd));
        eu   = EUMap.mul a.eu (mul_left b.eu a_lk_lrd);
        eu_p = EUMap.mul
            (mul_left b.eu (lift_lk_lrd all a.abspath_p))
            (EUMap.mul a.eu_p (mul_left b.eu_p a_locks_lrd));
        rd_tree = PartialTreeMap.mul
            (mul_pt_right f_none a.rd_tree b_locks_tree)
            (mul_pt_left f_none b.rd_tree a_locks_tree);
        rd_tree_p = PartialTreeMap.mul
            (mul_pt_right f_part a.rd_tree (lift_lk_tree all b.abspath_p))
            (PartialTreeMap.mul
               (mul_pt_right f_part a.rd_tree_p b_lk_tree)
               (mul_pt_left f_part b.rd_tree_p a_locks_tree));
        rd_tree_eu = TreeMap.mul
            (TreeMap.mul
               (add_uses f_all a.rd_tree_p b.eu)
               (add_uses f_all a.rd_tree b.eu_p))
            (TreeMap.mul
               a.rd_tree_eu
               (mul_t_left f_all b.rd_tree_eu a_locks_tree));
        eu_tree = PartialTreeMap.mul
            (mul_pt_right f_none a.eu_tree b_locks_tree)
            (mul_pt_left f_none b.eu_tree a_locks_tree);
        eu_tree_rd = TreeMap.mul
            (add_defs f_part a.eu_tree b.rd)
            (TreeMap.mul
               (mul_t_right f_part a.eu_tree_rd b_lk_tree)
               (mul_t_left f_part b.eu_tree_rd a_locks_tree));
        eu_tree_t = TreeMap.mul
            (TreeMap.mul
               (mul_t_right f_all a.eu_tree_rd (lift_lk_tree all b.abspath_t))
               (add_defs f_all a.eu_tree b.rd_t))
            (TreeMap.mul
               a.eu_tree_t
               (mul_t_left f_all b.eu_tree_t a_locks_tree));
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
      let abspath_p = LK.TR.mul (LK.TR.mul (clear_kill abspath) a.abspath_p) (clear_fst abspath) in
      let lrd_lk = lift_lk_lrd lock_kill abspath in
      let tree_locks = lift_lk_tree locks abspath in
      let rd = mul_left (mul_right a.rd lrd_lk) (lift_lk_lrd locks abspath) in
      let rd_t = mul_right rd (lift_lk_lrd all a.abspath_t) in
      let eu   = mul_left a.eu lrd_lk in
      let eu_p = mul_left a.eu (lift_lk_lrd all abspath_p) in
      let rd_tree = mul_pt_left f_none (mul_pt_right f_none a.rd_tree tree_locks) tree_locks in
      let rd_tree_p = mul_pt_right f_part rd_tree (lift_lk_tree all abspath_p) in
      let rd_tree_eu = add_uses f_all rd_tree_p a.eu in
      let eu_tree = mul_pt_left f_none (mul_pt_right f_none a.eu_tree tree_locks) tree_locks in
      let eu_tree_rd = add_defs f_part eu_tree rd in
      let eu_tree_t = mul_t_right f_all eu_tree_rd (lift_lk_tree all a.abspath_t) in
      let tree_c = TreeMap.mul (mul_rd_eu rd_tree eu_tree) (mul_eu_rd eu_tree rd_tree) in
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
      let filter_vars kill =
        let f ap = match ap with
          | Variable v -> may_use_conc v
          | _ -> PointerAnalysis.ap_is_shared ap
        in
        AP.Set.filter f kill
      in
      let get_deref e = match e with
        | AddrOf  ap -> AP.Set.singleton ap
        | _          -> AP.Set.singleton (Deref e)
      in
      let assign_weight lhs rhs =
        let ls   = LockPred.unit in
        let kill = filter_vars (AP.Set.singleton (AP.subscript 0 lhs)) in
        LK.TR.assign lhs rhs (ls, kill)
      in
      let assume_weight be =
        let ls   = LockPred.unit in
        let kill = filter_vars (AP.Set.map (AP.subscript 0) (Bexpr.get_uses be)) in
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
      | Assign (lhs, rhs) when may_use_conc lhs -> assign_weight (Variable lhs) rhs
      | Assume be | Assert (be, _) -> RDMap.unit (*assume_weight be*)
      | AssertMemSafe (e, _) -> assume_weight (Bexpr.of_expr e)
      (* Doesn't handle offsets at the moment *)
      | Builtin (Alloc (lhs, _, _)) when may_use_conc lhs
        -> assign_weight (Variable lhs) (Havoc (Var.get_type lhs))
      | _ -> RDMap.unit

    let eu_weight def =
      let f ap acc = match ap with
        | Variable v when not (may_use_conc v) -> acc
        | _ -> begin
            let pred = (LockPred.pred_weight def,
                        { SeqDep.current_name = Some (AP.subscript 0 ap);
                          SeqDep.killed = AP.Set.empty })
            in
            let tr   = LRD.TR.assume Bexpr.ktrue (AP.free_vars ap) pred in
            EUMap.update (def, ap) tr acc
          end
      in
      AP.Set.fold f (Def.get_uses def) EUMap.unit

    module Stab = LockLogic.Stabilizer(LKMinterm)

    let weight def =
      let abspath = (Stab.stabilise lk_weight) def in
      let rd = rd_weight def in
      let eu = eu_weight def in
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
      let query =
        let tmp = Analysis.mk_query rg weight Interproc.local root in
        Analysis.remove_dead_code tmp;
        tmp
      in
      let summary = Analysis.get_summary query root in
      let g (((def1, ap1), (def2, ap2)), tmp) =
        if (f_all tmp) != Tree.TR.zero then
          DG.add_edge_e dg (DG.E.create def1 (Pack.PairSet.singleton (Pack.mk_pair ap1 ap2)) def2)
      in
      BatEnum.iter g (TreeMap.enum summary.rd_tree_eu);
      BatEnum.iter g (TreeMap.enum summary.eu_tree_t);
      BatEnum.iter g (TreeMap.enum summary.tree_c)

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
    ignore(LockLogic.compute_races rg root);
    if !AliasLogic.must_alias then
      ConcDep.SeqDep.construct_dg ~solver:(ConcDep.SeqDep.RDAnalysisConc.solve rg root) file
    else
      ConcTrivDep.SeqDep.construct_dg ~solver:(ConcTrivDep.SeqDep.RDAnalysisConc.solve rg root) file
  in
    if !conc_edges then begin
      if !AliasLogic.must_alias then
        ConcDep.ConcRDAnalysis.add_conc_edges rg root dg
      else
        ConcTrivDep.ConcRDAnalysis.add_conc_edges rg root dg
    end;
    if !CmdLine.display_graphs then DG.display_labelled dg;
    dg

let chdfg_stats file =
  let dg = Log.phase "Construct hDFG" construct_conc_dg file in
  print_endline ("Vertices: " ^ (string_of_int (DG.nb_vertex dg)));
  print_endline ("Edges: " ^ (string_of_int (DG.nb_edges dg)))

let _ =
  CmdLine.register_pass
    ("-chdfg-stats", chdfg_stats, " Concurrent heap data flow graph statistics")

module I = Ai.ApronInterpretation
module InvGen = Solve.MakeAfgSolver(I)
let invariant_generation file =
  let changed = ref false in
  let remove_unreachable dg map file =
    let process_func func =
      let remove_vertex v =
        match v.dkind with
          | Assume _ ->
              if (DG.mem_vertex dg v
                  && I.is_bottom (InvGen.output map v))
              then begin
                Cfg.iter_succ_e (Cfg.remove_edge_e func.cfg) func.cfg v;
                Log.debug ("UNREACHABLE: " ^ (Def.show v));
                v.dkind <- Builtin Exit;
                changed := true
              end
          | _ -> ()
      in
      let init = Cfg.initial_vertex func.cfg in
        Cfg.iter_vertex remove_vertex func.cfg;
        CfgIr.remove_unreachable func.cfg init;
    in
      List.iter process_func file.funcs
  in
  let rec go () =
    let dg = Log.phase "Construct chDFG" construct_conc_dg file in
    let state = InvGen.mk_state dg in
    let map = InvGen.do_analysis state dg in
      Log.debug "REMOVE UNREACHABLE";
      changed := false;
      remove_unreachable dg map file;
      if !changed then go () else (dg, map)
  in
    ignore (Bddpa.initialize file);
    PointerAnalysis.simplify_calls file;
    let (dg,map) = go () in
      print_endline ("Vertices: " ^ (string_of_int (DG.nb_vertex dg)));
      print_endline ("Edges: " ^ (string_of_int (DG.nb_edges dg)));
      InvGen.check_assertions dg map

let _ =
  CmdLine.register_pass
    ("-chdfg",
     invariant_generation,
     " Invariant generation with concurrent heap data flow graph")

let sequentialish file =
  let expand_cfg cfg =
    let expand_forks def = match def.dkind with
      | Builtin (Fork (vo, tgt, elst)) ->
          let call = Def.mk (Call (vo, tgt, elst)) in
            Cfg.add_vertex cfg call;
            List.iter (fun v -> Cfg.add_edge cfg v call) (Cfg.pred cfg def);
            def.dkind <- Assume (Bexpr.ktrue)
      | _ -> ()
    in
      Cfg.iter_vertex expand_forks cfg
  in
    List.iter (fun func -> expand_cfg func.cfg) file.funcs

let _ =
  CmdLine.register_pass
    ("-sequentialish",
     sequentialish,
     " Replace forks with a nondeterministic call")
