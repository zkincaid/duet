(*pp camlp4find deriving.syntax *)

open Core
open CfgIr
open Apak
open EqLogic

module DG = Afg.G
module LockPred = struct 
  include LockLogic.LockPred
  let implies sub x y = false
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

      (* Multiplication needs to rewrite both transition functions over the same
       * frame first to avoid losing equalities like x=x<3>, x<3>=y *)
      let mul_pointed x y =
        let frame_x = get_frame x in
        let frame_y = get_frame y in
        let x_minus_y = Var.Set.diff frame_x frame_y in
        let y_minus_x = Var.Set.diff frame_y frame_x in
        let x_eqs = subst sub1 (assume Bexpr.ktrue y_minus_x pred_unit) in
        let y_eqs = subst sub0 (assume Bexpr.ktrue x_minus_y pred_unit) in
          mul (mul x x_eqs) (mul y_eqs y)

      let make_pointed x y =
        let frame_x = get_frame x in
        let frame_y = get_frame y in
        let x_minus_y = Var.Set.diff frame_x frame_y in
        let y_minus_x = Var.Set.diff frame_y frame_x in
        let x_unify = mul x (assume Bexpr.ktrue y_minus_x pred_unit) in
        let y_unify = mul y (assume Bexpr.ktrue x_minus_y pred_unit) in
          mul (subst sub1 x_unify) (subst sub0 y_unify)
    end
    module State = Formula.State
    module PointedTR : module type of TR with type t = TR.t = struct
      include TR
      let mul = mul_pointed
    end
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
  module PointedEUMap =
    Monoid.FunctionSpace.Total.Ordered.Make
      (DefAP)
      (Ka.Ordered.AdditiveMonoid(LRD.PointedTR))

  let map_to_pointedmap map = 
    let f acc (x, y) = PointedEUMap.update x y acc in
      BatEnum.fold f PointedEUMap.unit (EUMap.enum map)

  (* Path types. *)
  type abspath   = LK.TR.t deriving(Show,Compare)
  type abspath_t = LK.TR.t deriving(Show,Compare)
  type abspath_p = LK.PointedTR.t deriving(Show,Compare)
  type rd   = RDMap.t deriving(Show,Compare)
  type rd_t = RDMap.t deriving(Show,Compare)
  type eu   = EUMap.t deriving(Show,Compare)
  type eu_p = PointedEUMap.t deriving(Show,Compare)

  (* Lift an LKTransition to an LRDTransition *)
  let lift_transition ?(locks = true) ?(kills = true) tr =
    let frame = LK.TR.get_frame tr in
    let f minterm rest =
      let (lk, kl) = LKMinterm.get_pred minterm in
      let eqs = LKMinterm.get_eqs minterm in
      let pred = 
        let lk = if locks then lk else LockPred.unit in
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

  let rd_mul_right rd abspath =
    let abspath = lift_transition abspath in
    let update_rd tr = filter_rd (LRD.TR.mul tr abspath) in
      RDMap.map update_rd rd

  let rd_mul_left rd abspath =
    let abspath = lift_transition ~kills:false abspath in
    let update_rd tr = filter_rd (LRD.TR.mul abspath tr) in
      RDMap.map update_rd rd

  let rd_mul_left_con rd abspath =
    let abspath = lift_transition ~locks:false ~kills:false abspath in
    let update_rd tr = filter_rd (LRD.TR.mul abspath tr) in
      RDMap.map update_rd rd

  let eu_mul_left eu abspath =
    let abspath = lift_transition abspath in
    let update_eu tr = filter_rd (LRD.TR.mul abspath tr) in
      EUMap.map update_eu eu 

  let eu_mul_left_pointed eu abspath =
    let abspath = lift_transition abspath in
    let update_eu tr = filter_rd (LRD.PointedTR.mul abspath tr) in
      PointedEUMap.map update_eu eu 

  let eu_mul_left_con eu abspath =
    let abspath = lift_transition ~locks:false abspath in
    let update_eu tr = filter_rd (LRD.PointedTR.mul abspath tr) in
      PointedEUMap.map update_eu eu 

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
               eu_c : eu_p }
               deriving(Show,Compare)

    let compare = Compare_t.compare
    let format = Show_t.format
    let show = Show_t.show

    let equal a b = compare a b = 0

    let zero = { abspath = LK.TR.zero;
                 abspath_t = LK.TR.zero;
                 abspath_p = LK.PointedTR.zero;
                 rd = RDMap.unit;
                 rd_t = RDMap.unit;
                 rd_c = RDMap.unit;
                 eu = EUMap.unit;
                 eu_p = PointedEUMap.unit;
                 eu_c = PointedEUMap.unit }
    let one = { abspath = LK.TR.one;
                abspath_t = LK.TR.one;
                abspath_p = LK.PointedTR.mul LK.TR.one LK.TR.one;
                rd = RDMap.unit;
                rd_t = RDMap.unit;
                rd_c = RDMap.unit;
                eu = EUMap.unit;
                eu_p = PointedEUMap.unit;
                eu_c = PointedEUMap.unit }

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
     * concurrent uses = concurrent uses1 + kill eq path1 ; concurrent uses2 *)
    let mul a b = 
      { abspath = LK.TR.mul a.abspath b.abspath;
        abspath_t = LK.TR.add 
                      a.abspath_t 
                      (LK.TR.mul a.abspath b.abspath_t);
        abspath_p = LK.PointedTR.add
                      (LK.PointedTR.mul a.abspath_p b.abspath)
                      (LK.PointedTR.mul a.abspath b.abspath_p);
        rd = RDMap.mul 
               (rd_mul_right a.rd b.abspath)
               (rd_mul_left  b.rd a.abspath);
        rd_t = RDMap.mul 
                 (RDMap.mul a.rd_t (rd_mul_right a.rd b.abspath_t))
                 (rd_mul_left b.rd_t a.abspath);
        rd_c = RDMap.mul a.rd_c (rd_mul_left_con b.rd_c a.abspath);
        eu = EUMap.mul a.eu (eu_mul_left b.eu a.abspath);
        eu_p = PointedEUMap.mul a.eu_p
                 (PointedEUMap.mul (eu_mul_left_pointed (map_to_pointedmap b.eu) a.abspath_p)
                                   (eu_mul_left_pointed b.eu_p a.abspath));
        eu_c = PointedEUMap.mul a.eu_c (eu_mul_left_con b.eu_c a.abspath) }

    let add a b = { abspath = LK.TR.add a.abspath b.abspath;
                    abspath_t = LK.TR.add a.abspath_t b.abspath_t;
                    abspath_p = LK.PointedTR.add a.abspath_p b.abspath_p;
                    rd = RDMap.mul a.rd b.rd;
                    rd_t = RDMap.mul a.rd_t b.rd_t;
                    rd_c = RDMap.mul a.rd_c b.rd_c;
                    eu = EUMap.mul a.eu b.eu;
                    eu_p = PointedEUMap.mul a.eu_p b.eu_p;
                    eu_c = PointedEUMap.mul a.eu_c b.eu_c }
   
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
     * concurrent uses = eq path* ; concurrent uses *)
    let star a = 
      let abspath = LK.TR.star a.abspath in
      let abspath_t = LK.TR.mul abspath a.abspath_t in
      let abspath_p = LK.PointedTR.mul 
                        (LK.PointedTR.mul abspath a.abspath_p)
                        abspath
      in
      let rd = rd_mul_left (rd_mul_right a.rd abspath) abspath in
        { abspath = abspath;
          abspath_t = abspath_t;
          abspath_p = abspath_p;
          rd = rd;
          rd_t = EUMap.mul (rd_mul_right rd a.abspath_t)
                           (rd_mul_left a.rd_t abspath);
          rd_c = rd_mul_left_con a.rd_c abspath;
          eu = eu_mul_left a.eu abspath;
          eu_p = PointedEUMap.mul (eu_mul_left_pointed (map_to_pointedmap a.eu) abspath_p)
                                  (eu_mul_left_pointed a.eu_p abspath);
          eu_c = eu_mul_left_con a.eu_c abspath }

    let exists f a =
      let remove_locals rd =
        let g acc ((def, ap), rd) = match ap with
          | Variable v when not (f v) -> acc
          | _ -> RDMap.update (def, ap) (LRD.TR.exists f rd) acc
        in
          BatEnum.fold g RDMap.unit (RDMap.enum rd)
      in
      let remove_locals_pointed rd =
        let g acc ((def, ap), rd) = match ap with
          | Variable v when not (f v) -> acc
          | _ -> PointedEUMap.update (def, ap) (LRD.PointedTR.exists f rd) acc
        in
          BatEnum.fold g PointedEUMap.unit (PointedEUMap.enum rd)
      in
        { abspath = LK.TR.exists f a.abspath;
          abspath_t = LK.TR.exists f a.abspath_t;
          abspath_p = LK.PointedTR.exists f a.abspath_p;
          rd = remove_locals a.rd;
          rd_t = remove_locals a.rd_t;
          rd_c = remove_locals a.rd_c;
          eu = remove_locals a.eu;
          eu_p = remove_locals_pointed a.eu_p;
          eu_c = remove_locals_pointed a.eu_c }

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
        let ls   = { LockPred.par = LockPred.Pos;
                     LockPred.acq = get_deref e;
                     LockPred.rel = AP.Set.empty } in
        let kill = AP.Set.empty in
          LK.TR.assume Bexpr.ktrue (Expr.free_vars e) (ls, kill)
      in
      let rel_weight e =
        let ls   = { LockPred.par = LockPred.Pos;
                     LockPred.acq = AP.Set.empty;
                     LockPred.rel = get_deref e } in
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

    let weight def =
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
        { abspath = abspath;
          abspath_t = abspath;
          abspath_p = LK.TR.make_pointed abspath LK.TR.one;
          rd = rd;
          rd_t = rd;
          rd_c = RDMap.unit;
          eu = eu;
          eu_p = map_to_pointedmap eu;
          eu_c = PointedEUMap.unit }


    let analyze file =
      match file.entry_points with
        | [main] -> begin
            let rg = 
              let rginit = Interproc.make_recgraph file in
              let f acc (_, v) = match Interproc.RG.classify v with
                | RecGraph.Atom _ -> acc
                | RecGraph.Block b -> 
                    begin 
                      try Interproc.RG.block_body acc b; acc
                      with Not_found -> 
                        let vert = Def.mk Initial in
                        let bloc = Interproc.RG.G.empty in
                          Interproc.RG.add_block acc b (Interproc.RG.G.add_vertex bloc vert) vert vert
                    end
              in
                BatEnum.fold f rginit (Interproc.RG.vertices rginit)
            in
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
            let query = Analysis.mk_query rg weight local main
            in
              add_fork_edges query;
              Analysis.compute_summaries query
          end
        | _      -> assert false
  end
end

module ConcDep = Make(EqLogic.Hashed.MakeEQ(Var))
module ConcTrivDep = Make(EqLogic.Hashed.MakeTrivEQ(Var))

let construct_conc_dg file =
  ignore (Bddpa.initialize file);
  Pa.simplify_calls file;
  if !AliasLogic.must_alias then 
    ConcDep.SeqDep.construct_dg ~solver:ConcDep.SeqDep.RDAnalysisConc.solve file
  else 
    ConcTrivDep.SeqDep.construct_dg ~solver:ConcTrivDep.SeqDep.RDAnalysisConc.solve file


let chdfg_stats file =
  let dg = Log.phase "Construct hDFG" construct_conc_dg file in
    print_endline ("Vertices: " ^ (string_of_int (DG.nb_vertex dg)));
    print_endline ("Edges: " ^ (string_of_int (DG.nb_edges dg)))

let _ =
  CmdLine.register_pass 
    ("-chdfg-stats", chdfg_stats, " Concurrent heap data flow graph statistics")

let _ =
  CmdLine.register_pass 
    ("-chdfg-test", ConcDep.ConcRDAnalysis.analyze, " Concurrent heap data flow graph test")
