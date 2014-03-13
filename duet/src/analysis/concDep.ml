(*pp camlp4find deriving.syntax *)

open Core
open CfgIr
open Apak
open EqLogic

module DG = Afg.G
module LockPred = LockLogic.LockPred

module Make(MakeEQ :
	      functor (P : Hashed.Predicate with type var = Var.t) ->
		Hashed.ConjFormula with type var = Var.t
				   and type pred = P.t) =
struct
  module SeqDep = AliasLogic.Make(MakeEQ)
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
  module RDPred = struct
    include SeqDep.RDPred
    let pred_weight def = unit
  end

  module LKPred  = LockLogic.CombinePred(Var)(LockPred)(KillPred)
  module LRDPred = LockLogic.CombinePred(Var)(LockPred)(RDPred)

  module LKTransition = LockLogic.MakePath(LKPred)
  module LKMinterm = LKTransition.Minterm
  module LRDTransition = LockLogic.MakePath(LRDPred)
  module LRDMinterm = LRDTransition.Minterm

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
      (Ka.Ordered.AdditiveMonoid(LRDTransition))
  module EUMap = RDMap
  module PointedEUMap =
    Ka.MakePointedFS
      (DefAP)
      (LRDTransition)

  module PointedLK = struct
    type t = { left : LKTransition.t;
               right : LKTransition.t }
               deriving (Show,Compare)
    let format = Show_t.format
    let show = Show_t.show
    let compare = Compare_t.compare
  end
  module PointedLKTrans = Putil.Set.Make(PointedLK)

  module PointedLRD = struct
    type t = { left : LRDTransition.t;
               right : LRDTransition.t }
               deriving (Show,Compare)
    let format = Show_t.format
    let show = Show_t.show
    let compare = Compare_t.compare
  end
  module PointedLRDTrans = Putil.Set.Make(PointedLRD)

  (* Path types. *)
  type abspath   = LKTransition.t deriving(Show,Compare)
  type abspath_t = LKTransition.t deriving(Show,Compare)
  type abspath_p = PointedLKTrans.t deriving(Show,Compare)
  type rd   = RDMap.t deriving(Show,Compare)
  type rd_t = RDMap.t deriving(Show,Compare)
  type eu   = EUMap.t deriving(Show,Compare)
  type eu_p = PointedEUMap.t deriving(Show,Compare)

  (* Lift an LKTransition to an LRDTransition *)
  let lift_kill_transition kill_tr =
    let frame = LKTransition.get_frame kill_tr in
    let f minterm rest =
      let (locks, killed) = LKMinterm.get_pred minterm in
      let eqs = LKMinterm.get_eqs minterm in
      let pred = 
        (locks, { SeqDep.current_name = None; killed = killed })
      in
      let new_minterm = LRDMinterm.make eqs pred in
      let new_tr = LRDTransition.of_minterm frame new_minterm in
        LRDTransition.add new_tr rest
    in
      LKTransition.fold_minterms f kill_tr LRDTransition.zero

  (* Lift an LKTransition to an LRDTransition, but forget about the killed
   access paths *)
  let lift_kill_transition_lock_eq kill_tr =
    let frame = LKTransition.get_frame kill_tr in
    let f minterm rest =
      let (locks, _) = LKMinterm.get_pred minterm in
      let eqs = LKMinterm.get_eqs minterm in
      let pred =
        (locks, { SeqDep.current_name = None; killed = AP.Set.empty })
      in
      let new_minterm = LRDMinterm.make eqs pred in
      let new_tr = LRDTransition.of_minterm frame new_minterm in
        LRDTransition.add new_tr rest
    in
      LKTransition.fold_minterms f kill_tr LRDTransition.zero

  (* Lift an LKTransition to an LRDTransition, but forget about the killed
   access paths and locksets *)
  let lift_kill_transition_eq kill_tr =
    let frame = LKTransition.get_frame kill_tr in
    let f minterm rest =
      let eqs = LKMinterm.get_eqs minterm in
      let pred =
        (LockPred.unit, { SeqDep.current_name = None; killed = AP.Set.empty })
      in
      let new_minterm = LRDMinterm.make eqs pred in
      let new_tr = LRDTransition.of_minterm frame new_minterm in
        LRDTransition.add new_tr rest
    in
      LKTransition.fold_minterms f kill_tr LRDTransition.zero

  (* Lift an LKTransition to an LRDTransition, but forget about locksets *)
  let lift_kill_transition_kill_eq kill_tr =
    let frame = LKTransition.get_frame kill_tr in
    let f minterm rest =
      let (_, killed) = LKMinterm.get_pred minterm in
      let eqs = LKMinterm.get_eqs minterm in
      let pred = 
        (LockPred.unit, { SeqDep.current_name = None; killed = killed })
      in
      let new_minterm = LRDMinterm.make eqs pred in
      let new_tr = LRDTransition.of_minterm frame new_minterm in
        LRDTransition.add new_tr rest
    in
      LKTransition.fold_minterms f kill_tr LRDTransition.zero

  (* Lift a set of pointed LKTransitions to a set of pointed LRDTransitions *)
  let lift_pointed_kill_transition kill_tr_p =
    let f kill_p rest = 
      PointedLRDTrans.add { PointedLRD.left = lift_kill_transition kill_p.PointedLK.left;
                            PointedLRD.right = lift_kill_transition kill_p.PointedLK.right }
        rest
    in
      PointedLKTrans.fold f kill_tr_p PointedLRDTrans.empty

  (* Remove dead definitions (definitions of memory locations which are
   overwritten later in the path) *)
  let filter_rd rd_tr =
    let frame = LRDTransition.get_frame rd_tr in
    let f minterm rest =
      let (locks, pred) = LRDMinterm.get_pred minterm in
      let add = match pred.SeqDep.current_name with
        | Some name -> not (AP.Set.mem name pred.SeqDep.killed)
        | None -> true
      in
        if add
        then LRDTransition.add (LRDTransition.of_minterm frame minterm) rest
        else rest
    in
      LRDTransition.fold_minterms f rd_tr LRDTransition.zero

  let rd_mul_right rd abspath =
    let kill = lift_kill_transition abspath in
    let update_rd kill_tr = filter_rd (LRDTransition.mul kill_tr kill) in
      RDMap.map update_rd rd

  let rd_mul_left rd abspath =
    let lockeqs = lift_kill_transition_lock_eq abspath in
    let update_rd kill_tr = filter_rd (LRDTransition.mul lockeqs kill_tr) in
      RDMap.map update_rd rd

  let rd_mul_left_con rd abspath =
    let eqs = lift_kill_transition_eq abspath in
    let update_rd kill_tr = filter_rd (LRDTransition.mul eqs kill_tr) in
      RDMap.map update_rd rd

  let eu_mul_left eu abspath =
    let kill = lift_kill_transition abspath in
    let update_eu kill_tr = filter_rd (LRDTransition.mul kill kill_tr) in
      EUMap.map update_eu eu 

  (* Filtering for pointed paths? *)
  let eu_mul_pointed_left eu abspath_p = 
    let kill = lift_pointed_kill_transition abspath_p in
    let update_pointed_eu def_ap kill_tr kill_p acc =
      let new_path = 
        PointedEUMap.singleton 
          def_ap 
          kill_p.PointedLRD.left 
          (LRDTransition.mul kill_p.PointedLRD.right kill_tr) 
          LRDTransition.one
      in
        PointedEUMap.add new_path acc
    in
    let update_eu acc (def_ap, kill_tr) = 
      PointedLRDTrans.fold (update_pointed_eu def_ap kill_tr) kill acc
    in
      BatEnum.fold update_eu PointedEUMap.one (EUMap.enum eu) 

  let pointed_eu_mul_left eu_p abspath =
    let kill = lift_kill_transition abspath in
      PointedEUMap.mul (PointedEUMap.empty kill) eu_p 

  let pointed_eu_mul_left_con eu_p abspath =
    let kill = lift_kill_transition_kill_eq abspath in
      PointedEUMap.mul (PointedEUMap.empty kill) eu_p 

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

    let zero = { abspath = LKTransition.zero;
                 abspath_t = LKTransition.zero;
                 abspath_p = PointedLKTrans.empty;
                 rd = RDMap.unit;
                 rd_t = RDMap.unit;
                 rd_c = RDMap.unit;
                 eu = EUMap.unit;
                 eu_p = PointedEUMap.zero;
                 eu_c = PointedEUMap.zero }
    let one = { abspath = LKTransition.one;
                abspath_t = LKTransition.one;
                abspath_p = PointedLKTrans.singleton 
                              { PointedLK.left = LKTransition.one;
                                PointedLK.right = LKTransition.one };
                rd = RDMap.unit;
                rd_t = RDMap.unit;
                rd_c = RDMap.unit;
                eu = EUMap.unit;
                eu_p = PointedEUMap.one;
                eu_c = PointedEUMap.one }

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
      let update_right x = 
        { x with PointedLK.right = LKTransition.mul x.PointedLK.right b.abspath }
      in
      let update_left y = 
        { y with PointedLK.left = LKTransition.mul a.abspath y.PointedLK.left }
      in
      { abspath = LKTransition.mul a.abspath b.abspath;
        abspath_t = LKTransition.add 
                      a.abspath_t 
                      (LKTransition.mul a.abspath b.abspath_t);
        abspath_p = PointedLKTrans.union
                      (PointedLKTrans.map update_right a.abspath_p)
                      (PointedLKTrans.map update_left b.abspath_p);
        rd = RDMap.mul 
               (rd_mul_right a.rd b.abspath)
               (rd_mul_left  b.rd a.abspath);
        rd_t = RDMap.mul 
                 (RDMap.mul a.rd_t (rd_mul_right a.rd b.abspath_t))
                 (rd_mul_left b.rd_t a.abspath);
        rd_c = RDMap.mul a.rd_c (rd_mul_left_con b.rd_c a.abspath);
        eu = EUMap.mul a.eu (eu_mul_left b.eu a.abspath);
        eu_p = PointedEUMap.add
                 a.eu_p 
                 (PointedEUMap.add
                    (eu_mul_pointed_left b.eu a.abspath_p)
                    (pointed_eu_mul_left b.eu_p a.abspath));
        eu_c = PointedEUMap.add a.eu_c (pointed_eu_mul_left_con b.eu_c a.abspath) }

    let add a b = { abspath = LKTransition.add a.abspath b.abspath;
                    abspath_t = LKTransition.add a.abspath_t b.abspath_t;
                    abspath_p = PointedLKTrans.union a.abspath_p b.abspath_p;
                    rd = RDMap.mul a.rd b.rd;
                    rd_t = RDMap.mul a.rd_t b.rd_t;
                    rd_c = RDMap.mul a.rd_c b.rd_c;
                    eu = EUMap.mul a.eu b.eu;
                    eu_p = PointedEUMap.mul a.eu_p b.eu_p;
                    eu_c = PointedEUMap.mul a.eu_c b.eu_c }
    
    let star a = 
      let abspath = LKTransition.star a.abspath in
      let abspath_t = LKTransition.mul abspath a.abspath_t in
      let abspath_p = 
        let extend_pointed x = 
          { PointedLK.left = LKTransition.mul abspath x.PointedLK.left;
            PointedLK.right = LKTransition.mul x.PointedLK.right abspath }
        in
          PointedLKTrans.map extend_pointed a.abspath_p in
        { abspath = abspath;
          abspath_t = abspath_t;
          abspath_p = abspath_p;
          rd = rd_mul_left (rd_mul_right a.rd abspath) abspath;
          rd_t = rd_mul_left (rd_mul_right a.rd abspath_t) abspath;
          rd_c = rd_mul_left_con a.rd_c abspath;
          eu = eu_mul_left a.eu abspath;
          eu_p = eu_mul_pointed_left a.eu abspath_p;
          eu_c = pointed_eu_mul_left_con a.eu_c abspath }

    let exists f a =
      let map_exists x = { PointedLK.left = LKTransition.exists f x.PointedLK.left;
                           PointedLK.right = LKTransition.exists f x.PointedLK.right }
      in
      let remove_locals rd =
        let g acc ((def, ap), rd) = match ap with
          | Variable v when not (f v) -> acc
          | _ -> RDMap.update (def, ap) (LRDTransition.exists f rd) acc
        in
          BatEnum.fold g RDMap.unit (RDMap.enum rd)
      in
        { abspath = LKTransition.exists f a.abspath;
          abspath_t = LKTransition.exists f a.abspath_t;
          abspath_p = PointedLKTrans.map map_exists a.abspath_p;
          rd = remove_locals a.rd;
          rd_t = remove_locals a.rd_t;
          rd_c = remove_locals a.rd_c;
          eu = remove_locals a.eu;
          (* These don't remove locals, though they should *)
          eu_p = PointedEUMap.map_codomain (LRDTransition.exists f) a.eu_p;
          eu_c = PointedEUMap.map_codomain (LRDTransition.exists f) a.eu_c }

    let widen = add
  end

  module ConcRDAnalysis = struct
    module Analysis = Interproc.MakePathExpr(ConcReachingDefs)
    open ConcReachingDefs

    let rd_weight def =
      let assign_weight lhs rhs = 
        let pred = (LockPred.pred_weight def, 
                    { SeqDep.current_name = Some (AP.subscript 0 lhs);
                      SeqDep.killed = AP.Set.empty })
        in
          RDMap.update (def, lhs) (LRDTransition.assign lhs rhs pred) RDMap.unit
      in
      let assume_weight bexpr =
        let uses = Bexpr.get_uses bexpr in
        let f ap acc = 
          let pred = (LockPred.pred_weight def, 
                      { SeqDep.current_name = Some (AP.subscript 0 ap);
                        SeqDep.killed = AP.Set.empty })
          in
          let tr = LRDTransition.assume bexpr (AP.free_vars ap) pred in
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
      let abspath = LKTransition.weight def in
      let rd = rd_weight def in
      let (eu, eu_p) = 
        let f ap (eu_acc, eu_p_acc) = 
          let pred = (LockPred.pred_weight def, 
                      { SeqDep.current_name = Some (AP.subscript 0 ap);
                        SeqDep.killed = AP.Set.empty })
          in
          let tr   = LRDTransition.assume Bexpr.ktrue (AP.free_vars ap) pred in
          let tr_p = { PointedLRD.left = tr;
                       PointedLRD.right = LRDTransition.one }
          in
          let new_p_eu = PointedEUMap.singleton (def, ap) tr LRDTransition.one LRDTransition.one in
            (EUMap.update (def, ap) tr eu_acc, PointedEUMap.add new_p_eu eu_p_acc)
        in
          AP.Set.fold f (Def.get_uses def) (EUMap.unit, PointedEUMap.one)
      in
        { abspath = abspath;
          abspath_t = abspath;
          abspath_p = PointedLKTrans.singleton 
                        { PointedLK.left = abspath;
                          PointedLK.right = LKTransition.one };
          rd = rd;
          rd_t = rd;
          rd_c = RDMap.unit;
          eu = eu;
          eu_p = eu_p;
          eu_c = PointedEUMap.one }


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
