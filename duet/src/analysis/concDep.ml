(*pp camlp4find deriving.syntax *)

open Core
open CfgIr
open Apak
open EqLogic

module DG = Afg.G
module Pack = Afg.Pack

(* Double lock sets *)
module LockPred = struct
  module LP = LockLogic.LockPred
  include LockLogic.CombinePred(Var)(LP)(LP)
  let implies sub x y =
    let sub' ap = Some (sub ap) in
      equal x (subst sub' y)
  let clear_fst (x, y) = (LP.unit, y)
  let clear_snd (x, y) = (x, LP.unit)
  let make_acq x = 
    let ls = { LP.par = LP.Pos;
               LP.acq = x;
               LP.rel = AP.Set.empty }
    in
      (ls, ls)
  let make_rel x = 
    let ls = { LP.par = LP.Pos;
               LP.acq = AP.Set.empty; 
               LP.rel = x }
    in
      (ls, ls)
  let neg (ls1, ls2) = (LP.neg ls1, LP.neg ls2)
  let is_empty (ls1, ls2) = AP.Set.is_empty ls1.LP.acq &&
                            AP.Set.is_empty ls2.LP.acq
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
    let pred_weight def = unit
  end
  module LRDPred = LockLogic.CombinePred(Var)(LockPred)(RDPred)
  module LRDMinterm = MakeEQ(LRDPred)
  module LRD = MakeFormula(LRDMinterm)

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

  module DFlow = struct
    type t = DefAP.t * DefAP.t deriving (Show, Compare)
    let format = Show_t.format
    let show = Show_t.show
    let compare = Compare_t.compare
    let hash (x, y) = Hashtbl.hash (DefAP.hash x, DefAP.hash y)
    let equal x y = compare x y = 0
  end
  module DefUse = struct
    type t = { def : LRD.TR.t;
               use : LRD.TR.t } deriving(Show,Compare)
    let format = Show_t.format
    let show = Show_t.show
    let compare = Compare_t.compare
    let equal x y = compare x y = 0
    let unit = { def = LRD.TR.zero; 
                 use = LRD.TR.zero }
    let mul x y = { def = LRD.TR.add x.def y.def;
                    use = LRD.TR.add x.use y.use }
  end
  module DFlowMap = Monoid.FunctionSpace.Total.Ordered.Make(DFlow)(DefUse)

  (* Path types. *)
  type abspath   = LK.TR.t deriving(Show,Compare)
  type abspath_t = LK.TR.t deriving(Show,Compare)
  type abspath_p = LK.TR.t deriving(Show,Compare)
  type rd   = RDMap.t deriving(Show,Compare)
  type rd_t = RDMap.t deriving(Show,Compare)
  type eu   = EUMap.t deriving(Show,Compare)
  type eu_p = EUMap.t deriving(Show,Compare)
  type du = DFlowMap.t deriving(Show,Compare)
  type ud = DFlowMap.t deriving(Show,Compare)

  (* Lift an LKTransition to an LRDTransition *)
  let lift_lk ?(fst_ls = true) ?(snd_ls = true) ?(kills = true) tr =
    let frame = LK.TR.get_frame tr in
    let f minterm rest =
      let (lk, kl) = LKMinterm.get_pred minterm in
      let eqs = LKMinterm.get_eqs minterm in
      let pred = 
        let lk = match (fst_ls, snd_ls) with
          | (true, true) -> lk
          | (false, false) -> LockPred.unit
          | (false, _) -> LockPred.clear_fst lk
          | (_, false) -> LockPred.clear_snd lk
        in
        let kl = if kills then kl else AP.Set.empty in
          (lk, { SeqDep.current_name = None; killed = kl })
      in
      let new_minterm = LRDMinterm.make eqs pred in
      let new_tr = LRD.TR.of_minterm frame new_minterm in
        LRD.TR.add new_tr rest
    in
      LK.TR.fold_minterms f tr LRD.TR.zero

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

  let mul_right x y = 
    let update_rd tr = filter_rd (LRD.TR.mul tr y) in
      RDMap.map update_rd x

  let mul_left x y = 
    let update_rd tr = filter_rd (LRD.TR.mul y tr) in
      RDMap.map update_rd x

  let killed_on_interleaving x y x_name y_name =
    let f (ls, k) = (LockPred.neg ls, k) in
    let g x = if Var.get_subscript x = 1 then Var.subscript x 3 else x in
    let y = LRDMinterm.subst g y in
    let y' = LRDMinterm.make (LRDMinterm.get_eqs y) (f (LRDMinterm.get_pred y)) in
    let z = LRDMinterm.exists (fun _ -> true) (LRDMinterm.mul x y') in
    let (ls, k) = LRDMinterm.get_pred z in
    let subst = LRDMinterm.get_subst z in
    let killed name = match name with
      | Some ap -> AP.Set.mem (AP.subst_var subst ap) k.SeqDep.killed
      | None -> false
    in
      not (LockPred.is_empty ls) || killed x_name || killed y_name

  let get_reaching ((def, def_ap), def_tr) ((use, use_ap), use_tr) =
    let def_frame = LRD.TR.get_frame def_tr in
    let use_frame = LRD.TR.get_frame use_tr in
    let get_name m = (snd (LRDMinterm.get_pred m)).SeqDep.current_name in
      if Pa.may_alias def_ap use_ap
      then
        let filter f =
          let h min1 min2 (d, u) = 
            if (f min1 min2) 
            then (LRD.TR.add (LRD.TR.of_minterm def_frame min1) d, 
                  LRD.TR.add (LRD.TR.of_minterm use_frame min2) u) 
            else (d, u)
          in
          let g min1 acc = LRD.TR.fold_minterms (h min1) use_tr acc in
            LRD.TR.fold_minterms g def_tr (LRD.TR.zero, LRD.TR.zero)
        in
        let f d u = match (get_name d, get_name u) with
          | (None, None) -> true
          | (d_name, u_name) ->
              not (killed_on_interleaving d u d_name u_name)
        in
          filter f
      else
        (LRD.TR.zero, LRD.TR.zero)

  let dflow rd eu =
    let g def acc use =
      let (d, u) = get_reaching def use in
        if (d = LRD.TR.zero && u = LRD.TR.zero) then acc
        else
          let tree = { DefUse.def = d; DefUse.use = u } in
            DFlowMap.mul acc (DFlowMap.update (fst def, fst use) tree DFlowMap.unit)
    in
    let f acc def = BatEnum.fold (g def) acc (EUMap.enum eu) in
    let tmp = BatEnum.fold f DFlowMap.unit (RDMap.enum rd) in
    Log.logf Log.info
      "dflow: **DEF** %a **USE** %a -> %a"
      RDMap.format rd
      EUMap.format eu
      DFlowMap.format tmp;
      tmp

  (* TODO: this *)
  let check_consistency du = du

  module ConcReachingDefs = struct
    type var = Var.t
    type t = { abspath : abspath;
               abspath_t : abspath_t;
               abspath_p : abspath_p;
               rd : rd;
               rd_t : rd_t;
               rd_c : rd_t;
               eu : eu;
               eu_p : eu_p;
               eu_c : eu_p;
               du : du;
               ud : ud }
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
                 du = DFlowMap.unit;
                 ud = DFlowMap.unit }
    let one = { abspath = LK.TR.one;
                abspath_t = LK.TR.one;
                abspath_p = LK.TR.one;
                rd = RDMap.unit;
                rd_t = RDMap.unit;
                rd_c = RDMap.unit;
                eu = EUMap.unit;
                eu_p = EUMap.unit;
                eu_c = EUMap.unit;
                du = DFlowMap.unit;
                ud = DFlowMap.unit }

    (* path = path1 ; path2,
     * terminated paths = terminate paths1 + path1 ; * terminated paths2
     * pointed paths = path1 ; pointed paths2 + pointed paths1 ; path2
     * reaching defs = reaching defs1 ; kill path2 + eq/lock path1 ; reaching defs2
     * terminated defs = terminated defs1 + reaching defs1 ; terminated paths2
     *                     + path1 ; terminated defs 2
     * concurrent defs = concurrent defs1 + eq path1 ; concurrent defs2
     * exposed uses = exposed uses1 + path1 ; exposed uses2
     * pointed uses = pointed uses1 + pointed paths1 ; exposed uses 2 
     *                     + path1 ; pointed uses 2
     * concurrent uses = concurrent uses1 + kill eq path1 ; concurrent uses2
     * du = du1 + path1;reaching defs2-concurrent uses1 + check(path1 ; du2)
     * ud = ud1 + concurrent defs1-path1;exposed uses2 + check(path1 ; ud2) *)

    let mul a b =
        { abspath   = LK.TR.mul a.abspath b.abspath;
          abspath_t = LK.TR.add 
                        a.abspath_t 
                        (LK.TR.mul a.abspath b.abspath_t);
          abspath_p = LK.TR.add 
                        (LK.TR.mul a.abspath_p (clear_fst b.abspath)) 
                        (LK.TR.mul (clear_kill a.abspath) b.abspath_p);
          rd        = RDMap.mul 
                        (mul_right a.rd (lift_lk ~fst_ls:false b.abspath)) 
                        (mul_left  b.rd (lift_lk ~kills:false a.abspath));
          rd_t      = RDMap.mul a.rd_t 
                        (RDMap.mul 
                           (mul_right a.rd (lift_lk ~fst_ls:false b.abspath_t))
                           (mul_left  b.rd_t (lift_lk ~kills:false a.abspath)));
          rd_c      = RDMap.mul a.rd_c 
                        (mul_left b.rd_c (lift_lk ~fst_ls:false ~snd_ls:false ~kills:false a.abspath));
          eu        = EUMap.mul a.eu (mul_left b.eu (lift_lk ~fst_ls:false a.abspath));
          eu_p      = EUMap.mul a.eu_p
                        (EUMap.mul 
                           (mul_left b.eu (lift_lk a.abspath_p))
                           (mul_left b.eu_p (lift_lk ~kills:false a.abspath)));
          eu_c      = EUMap.mul a.eu_c 
                        (mul_left b.eu_c (lift_lk ~fst_ls:false ~snd_ls:false ~kills:false a.abspath));
          du        = DFlowMap.unit;
          ud        = DFlowMap.unit }
 
    let add a b = { abspath = LK.TR.add a.abspath b.abspath;
                    abspath_t = LK.TR.add a.abspath_t b.abspath_t;
                    abspath_p = LK.TR.add a.abspath_p b.abspath_p;
                    rd = RDMap.mul a.rd b.rd;
                    rd_t = RDMap.mul a.rd_t b.rd_t;
                    rd_c = RDMap.mul a.rd_c b.rd_c;
                    eu = EUMap.mul a.eu b.eu;
                    eu_p = EUMap.mul a.eu_p b.eu_p;
                    eu_c = EUMap.mul a.eu_c b.eu_c;
                    du = DFlowMap.mul a.du b.du;
                    ud = DFlowMap.mul a.ud b.ud }
   
    (* path = path*,
     * terminated paths = path* ; terminated paths
     * pointed paths = path* ; pointed paths ; path*
     * reaching defs = path* ; reaching defs ; path*
     * terminated defs = path* ; reaching defs ; path* ; terminated paths
     *                   + path* ; terminated defs
     * concurrent defs = eq path* ; concurrent defs
     * exposed uses = path* ; exposed uses
     * pointed uses = path* ; pointed paths ; path* ; exposed uses
     *                + path* ; pointed uses
     * concurrent uses = eq path* ; concurrent uses
     * du =  *)
    let star a = 
      let abspath = LK.TR.star a.abspath in
      let abspath_t = LK.TR.mul abspath a.abspath_t in
      let abspath_p = LK.TR.mul 
                        (LK.TR.mul (clear_kill abspath) a.abspath_p)
                        (clear_fst abspath)
      in
      let rd = mul_left 
                 (mul_right a.rd (lift_lk ~fst_ls:false abspath))
                 (lift_lk ~kills:false abspath)
      in
      let rd_t = EUMap.mul 
                   (mul_right rd (lift_lk ~fst_ls:false a.abspath_t))
                   (mul_left a.rd_t (lift_lk ~kills:false abspath))
      in
      let rd_c = mul_left a.rd_c 
                   (lift_lk ~fst_ls:false ~snd_ls:false ~kills:false abspath)
      in
      let eu   = mul_left a.eu (lift_lk ~fst_ls:false abspath) in
      let eu_p = EUMap.mul 
                   (mul_left a.eu (lift_lk abspath_p))
                   (mul_left a.eu_p (lift_lk ~kills:false abspath))
      in
      let eu_c = mul_left a.eu_c 
                   (lift_lk ~fst_ls:false ~snd_ls:false ~kills:false abspath)
      in
        { abspath = abspath;
          abspath_t = abspath_t;
          abspath_p = abspath_p;
          rd   = rd;
          rd_t = rd_t;
          rd_c = rd_c;
          eu   = eu;
          eu_p = eu_p;
          eu_c = eu_c;
          du = DFlowMap.unit;
          ud = DFlowMap.unit }

    let exists f a =
      let g ((def, ap), rd) = match ap with
        | Variable v when not (f v) -> LRD.TR.zero
        | _ -> LRD.TR.exists f rd
      in
      let remove_locals rd =
        let h acc (da, rd) = RDMap.update da (g (da, rd)) acc in
          BatEnum.fold h RDMap.unit (RDMap.enum rd)
      in
      let remove_locals_dflow du =
        let h acc (((d1, ap1), (d2, ap2)), du) =
          let du' = { DefUse.def = g ((d1, ap1), du.DefUse.def);
                      DefUse.use = g ((d2, ap2), du.DefUse.use) }
          in
            DFlowMap.update ((d1, ap1), (d2, ap2)) du' acc
        in
          BatEnum.fold h DFlowMap.unit (DFlowMap.enum du)
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
          du = remove_locals_dflow a.du;
          ud = remove_locals_dflow a.ud }

    let widen = add
  end

  module ConcRDAnalysis = struct
    module Analysis = Interproc.MakePathExpr(ConcReachingDefs)
    open ConcReachingDefs

    let lk_weight def =
      let get_deref e = match e with 
        | AccessPath ap -> AP.Set.singleton (Deref (AccessPath ap))
        | AddrOf     ap -> AP.Set.singleton ap
        | _             -> AP.Set.empty
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

    let weight summaries def =
      let abspath = lk_weight def in
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
      let (rd_c, eu_c) = match def.dkind with
        | Builtin (Fork (vo, e, elst)) -> 
            let summary =
              try Analysis.HT.find summaries (LockLogic.get_func e)
              with Not_found -> one
            in
              (RDMap.mul summary.rd_t summary.rd_c,
               EUMap.mul summary.eu_p summary.eu_c)
        | _ -> (RDMap.unit, EUMap.unit)
      in
        { abspath = abspath;
          abspath_t = abspath;
          abspath_p = abspath;
          rd = rd;
          rd_t = rd;
          rd_c = rd_c;
          eu = eu;
          eu_p = eu;
          eu_c = eu_c;
          du = DFlowMap.unit;
          ud = DFlowMap.unit }


    let analyze file =
      match file.entry_points with
        | [main] -> begin
            let rg = Interproc.make_recgraph file in
            let local func_name =
              try
                let func = List.find (fun f -> Varinfo.equal func_name f.fname) (get_gfile()).funcs in
                let vars = Varinfo.Set.remove (return_var func_name)
                             (Varinfo.Set.of_enum (BatEnum.append (BatList.enum func.formals)
                                                     (BatList.enum func.locals)))
                in
                  fun (x, _) -> (Varinfo.Set.mem x vars)
              with Not_found -> (fun (_, _) -> false)
            in
            (* Adds edges to the callgraph for each fork. Shouldn't really have to do
             * this every time a new query is made *)
            let add_fork_edges q =
              let f (b, v) = match v.dkind with
                | Builtin (Fork (vo, e, elst)) -> Analysis.add_callgraph_edge q b (LockLogic.get_func e)
                | _ -> ()
              in
                BatEnum.iter f (Interproc.RG.vertices rg)
            in
            let rec iter_query old_query = 
              let eq sum1 sum2 =
                let f k v s = s && List.exists (equal v) (Analysis.HT.find_all sum1 k) in
                  Analysis.HT.fold f sum2 true
              in
              let new_query = Analysis.mk_query rg (weight (Analysis.get_summaries old_query)) local main in
                begin
                  add_fork_edges new_query;
                  Analysis.compute_summaries new_query;
                  if eq (Analysis.get_summaries old_query)
                        (Analysis.get_summaries new_query)
                  then new_query
                  else iter_query new_query
                end
            in
            let initial = Analysis.mk_query rg (weight (Analysis.HT.create 0)) local main
            in
            let query = begin
              add_fork_edges initial;
              Analysis.compute_summaries initial;
              iter_query initial
            end
            in
              query
          end
        | _      -> assert false

    let add_conc_edges file dg query =
      let f summary =
        let g (((def1, ap1), (def2, ap2)), _) =
          DG.add_edge_e dg (DG.E.create def1 (Pack.PairSet.singleton (Pack.mk_pair ap1 ap2)) def2)
        in
          BatEnum.iter g (DFlowMap.enum (dflow summary.rd_t summary.eu_c));
          BatEnum.iter g (DFlowMap.enum (dflow summary.rd_c summary.eu_p));
          BatEnum.iter g (DFlowMap.enum (dflow summary.rd_c summary.eu_c))
      in
        match file.entry_points with
          | [main] -> f (Analysis.get_summary query main)
          | _ -> assert false

  end
end

module ConcDep = Make(EqLogic.Hashed.MakeEQ(Var))
module ConcTrivDep = Make(EqLogic.Hashed.MakeTrivEQ(Var))

let construct_conc_dg file =
  let dg = begin
    ignore (Bddpa.initialize file);
    Pa.simplify_calls file;
    ignore (LockLogic.get_races ());
    if !AliasLogic.must_alias then 
      ConcDep.SeqDep.construct_dg ~solver:ConcDep.SeqDep.RDAnalysisConc.solve file
    else 
      ConcTrivDep.SeqDep.construct_dg ~solver:ConcTrivDep.SeqDep.RDAnalysisConc.solve file
  end in
    ConcDep.ConcRDAnalysis.add_conc_edges file dg (ConcDep.ConcRDAnalysis.analyze file);
  if !CmdLine.display_graphs then DG.display_labelled dg;
  dg

let chdfg_stats file =
  let dg = Log.phase "Construct hDFG" construct_conc_dg file in
    print_endline ("Vertices: " ^ (string_of_int (DG.nb_vertex dg)));
    print_endline ("Edges: " ^ (string_of_int (DG.nb_edges dg)))

let _ =
  CmdLine.register_pass 
    ("-chdfg-stats", chdfg_stats, " Concurrent heap data flow graph statistics")

let _ =
  CmdLine.register_pass 
    ("-chdfg-test", (fun x -> ConcDep.ConcRDAnalysis.analyze x; ()), " Concurrent heap data flow graph test")

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
