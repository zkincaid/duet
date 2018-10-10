
open Srk
include Log.Make(struct let name = "refine_ops" end)


module type PreKleeneAlgebra = sig
  type t
  val mul : t -> t -> t
  val add : t -> t -> t
  val zero : t
  val one : t
  val star : t -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

open Graph


(*let refinetime = ref 0.0*)
(*
let timer f x = 
  let start_time = Unix.gettimeofday () in
  let result = f x in 
  let time = (Unix.gettimeofday ()) -. start_time in
*)
(*refinetime := refinetime +. time;*)



module DomainRefinement (PreKleeneWithoutTiming : PreKleeneAlgebra) = struct


  module PreKleene = struct
    type t = PreKleeneWithoutTiming.t
    let mul x y = Log.time "refine_ops" (PreKleeneWithoutTiming.mul x) y
    let add x y = Log.time "refine_ops" (PreKleeneWithoutTiming.add x) y
    let zero = PreKleeneWithoutTiming.zero
    let one = PreKleeneWithoutTiming.one
    let star x = Log.time "refine_ops" PreKleeneWithoutTiming.star x
    (*let equal = PreKleeneWithoutTiming.equal*)
    let equal x y = Log.time "refine_edge_tests" (PreKleeneWithoutTiming.equal x) y
    let compare = PreKleeneWithoutTiming.compare
  end


  (* Minimum graph signature for Johnsons algorithm *)
  module type BasicG = sig
    type t
    module V : Graph.Sig.VERTEX
    val nb_vertex : t -> int
    val iter_vertex : (V.t -> unit) -> t -> unit
    val iter_edges : (V.t -> V.t -> unit) -> t -> unit
  end

  module JohnsonCycle (G1: BasicG) = struct
    
    module Int = struct
      type t = int (* Vertex number *)
      let compare = Pervasives.compare 
      let hash = Hashtbl.hash
      let equal = (=)
    end

    module IntMap = Map.Make(Int)
    
    module JGraph = Imperative.Digraph.Concrete(Int)

    module SCC = Components.Make(JGraph)
    
    module VertexMap = Map.Make(struct type t = G1.V.t let compare = G1.V.compare end)
    
    let johnsonCycle g =
      let n = JGraph.nb_vertex g in
      
      let blocked = Array.make n false in
      let b = Array.make n [] in
      
      let circuits = ref [] in (* used to store the results *)
      let stack = Stack.create () in
      let s = ref 0 in

      let rec circuit v comp = 
	let rec unblock u =
	  blocked.(u) <- false;
	  List.iter 
	    (fun w -> 
	      if (blocked.(w)) then unblock w (* if blocked(w) then unblock(w) *)
	    ) b.(u);
	  b.(u) <- [] (* delete w from B(u) for all w that was in B(u) *)
	in
	let f = ref false in
	Stack.push v stack;
	blocked.(v) <- true;
	JGraph.iter_succ 
	  (fun w -> 
	    if w = !s then
	      let cycle = ref [] in
	      Stack.iter (fun a -> cycle := a :: !cycle) stack;
	      circuits := (!cycle :: !circuits); (* add what's on the stack to circuits *)
	      f := true
	    else if not (blocked.(w)) then if circuit w comp then f := true
	  ) comp v;
	if !f then unblock v
	else 
	  JGraph.iter_succ 
	  (fun w ->
	    if not (List.mem v (b.(w))) then b.(w) <- v :: (b.(w)) (* if v not on B(w) then add it *)
	  ) comp v;
	let _ = Stack.pop stack in
	!f
      in
      while !s < (n-1) do
	let subgraph = JGraph.copy g in 
	for i = 0 to !s - 1 do (* build subgraph of nodes s, s+1, ..., n *)
	  JGraph.remove_vertex subgraph i
	done;
	let comp_list = SCC.scc_list subgraph in (* get sccs of subgraph *)
	let non_trivial = List.filter (fun l -> List.length l > 1) comp_list in (* remove trival sccs *)
	let (smallest_vertex, respective_comp) = (* get scc with smallest vertex *)
	  List.fold_left 
	    (fun min_comp l -> 
	      let min_of_fst_min_comp_and_l = 
                List.fold_left (fun min_ el -> min min_ el) (fst min_comp) l 
                in
	      if min_of_fst_min_comp_and_l = fst min_comp then
		min_comp
	      else
		(min_of_fst_min_comp_and_l, l)
	    ) (n+1, []) non_trivial in
	s := smallest_vertex;
	let component_graph = JGraph.create () in
	List.iter 
          (fun node -> 
            JGraph.add_vertex component_graph node
          ) respective_comp; (* build up the component graph *)
	JGraph.iter_edges 
	  (fun v1 v2 ->
	    if ((List.mem v1 respective_comp) && (List.mem v2 respective_comp)) then
	      JGraph.add_edge component_graph v1 v2
	  ) subgraph;
	if (JGraph.nb_vertex component_graph) <> 0 then
	  (JGraph.iter_vertex 
	    (fun i -> 
	      blocked.(i) <- false;
	      b.(i) <- []
	    ) component_graph;
	  let _ = circuit !s component_graph in
	  s := !s + 1)
	else s := (n-1)
      done;
      !circuits

    (** This function takes in a graph object with the following signature
      module type BasicG = sig
	type t
	module V : Sig.VERTEX
	val nb_vertex : t -> int
	val iter_vertex : (V.t -> unit) -> t -> unit
	val iter_edges : (V.t -> V.t -> unit) -> t -> unit
      end
    *)
    let simpcycles inputGraph = 
      let jgraph = JGraph.create () in (* create a graph with integer vertices *)
      let s = ref 0 in (* the vertex labels *)
      let intToVertex = ref IntMap.(empty) in (* A map from the jgraph vertices to the original graph verticies *)
      let vertexToInt = ref VertexMap.(empty) in (* A map from the original graph vertices to the jgraph vertices *)
      G1.iter_vertex 
	(fun v -> 
	  JGraph.add_vertex jgraph !s;
	  intToVertex := IntMap.add !s v !intToVertex;
	  vertexToInt := VertexMap.add v !s !vertexToInt;
	  s := !s + 1
	) inputGraph; (* add vertices to jgraph and maps *)
      G1.iter_edges
	(fun v1 v2 ->
	  JGraph.add_edge jgraph 
                          (VertexMap.find v1 !vertexToInt) 
                          (VertexMap.find v2 !vertexToInt)
	) inputGraph; (* copy edges *)
     let cycles = johnsonCycle jgraph in (* get cycles of jgraph *)
     List.map 
       (fun l -> 
         List.map (fun a -> IntMap.find a !intToVertex) l
       ) cycles (* remap jgraph cycles to cycles of the original graph *)

  end
    
  module Int = struct
    type t = int
    let compare = Pervasives.compare
    let hash = Hashtbl.hash
    let equal = (=)
  end

  module IntMap = Map.Make(Int)
  
  module IntSet = Set.Make(Int)

  module RGraph = Imperative.Digraph.Concrete(Int)

  module LGraph = Imperative.Digraph.ConcreteLabeled(Int)(struct type t = PreKleene.t let compare = PreKleene.compare let default = PreKleene.one end)

  module SCCmod = Components.Make(RGraph)

  module Cycle = JohnsonCycle(RGraph)
    
  module Top = Topological.Make(RGraph)
  
  module TopL = Topological.Make(LGraph)

(*  let build_refinement_graph labels infeasiblepairs = 
    let refinement_graph = RGraph.create () in
    List.iter (fun label -> RGraph.add_vertex refinement_graph label) labels;
    let edge_set = 
      List.concat 
        (List.map 
          (fun x -> 
            List.map 
             (fun y -> (x, y)
          ) labels
        ) labels ) 
      in
    let edge_set = 
      List.filter 
        (fun pair -> not (List.mem pair infeasiblepairs)) 
      edge_set
      in
    List.iter 
      (fun edge -> 
        RGraph.add_edge refinement_graph 
                        (fst edge) 
                        (snd edge)
      ) edge_set;
    refinement_graph
*)

  let get_scc_expr_cycles refinement_graph nSCCs mapToComp =
    let self_loop_cycles = ref [] in
    RGraph.iter_edges
      (fun v1 v2 ->
        if v1 = v2 then self_loop_cycles := [v1] :: !self_loop_cycles
      ) refinement_graph;
    let self_loop_cycles = !self_loop_cycles in

    let sccs = Array.make nSCCs [] in
    RGraph.iter_vertex
      (fun vertex ->
        let comp_num = mapToComp vertex in
        sccs.(comp_num) <- vertex :: sccs.(comp_num)
      ) refinement_graph;

    Array.map
      (fun component ->
        if (List.exists (fun v -> List.mem [v] self_loop_cycles) component) then List.map (fun x -> [x]) component
        else
          let comp_graph = RGraph.copy refinement_graph in
          RGraph.iter_vertex
            (fun v ->
              if not (List.mem v component) then RGraph.remove_vertex comp_graph v
            ) refinement_graph;
          let cycle_list = Cycle.simpcycles comp_graph in
          if cycle_list = [] then []
          else
            let remove_dups xs = BatList.sort_unique Pervasives.compare xs in
            let unique_lengths = remove_dups (List.map List.length cycle_list) in
            let common_labels =
              List.fold_left
                (fun common cycle ->
                  List.filter (fun el -> List.mem el cycle) common
                ) (List.hd cycle_list) cycle_list
              in
            if List.length unique_lengths = 1 && List.length common_labels <> 0 then (* if cycles in scc have the same length and have common label *)
              if List.length cycle_list = 1 then cycle_list (* if it's just one cycle then output cycle *)
              else
                (* permute cycle to common label *)
                let common_label = List.nth common_labels 0 in
                let rec permute_to_label label lst prev =
                  match lst with
                  | [] -> List.rev prev
                  | hd :: tl -> if label = hd then lst @ (List.rev prev)
                                else permute_to_label label tl (hd :: prev)
                in
                (* output permuted cycles *)
                List.map (fun cycle -> permute_to_label common_label cycle []) cycle_list
            else
              let sccLabels = remove_dups (List.concat cycle_list) in
              (* output sum of labels *)
              List.map (fun label -> [label]) sccLabels
        ) sccs

(*
  let get_scc_expr_cycles refinement_graph nSCCs mapToComp =
    let cycles = Log.time "refine_johnsons" Cycle.simpcycles refinement_graph in
    let self_loop_cycles = ref [] in
    RGraph.iter_edges 
      (fun v1 v2 -> 
        if v1 = v2 then self_loop_cycles := [v1] :: !self_loop_cycles
      ) refinement_graph;
    let remove_dups xs = BatList.sort_unique Pervasives.compare xs in
    let cycles = 
      if List.length !self_loop_cycles <> 0 then remove_dups (!self_loop_cycles @ cycles)      else cycles 
    in
    let scc_cycles = Array.make nSCCs [] in
    List.iter
      (fun cycle ->
	let scc = mapToComp (List.hd cycle) in
	scc_cycles.(scc) <- cycle :: scc_cycles.(scc)
      ) cycles;
    Array.map
      (fun cycle_list ->
        if cycle_list = [] then []
        else 
	  let unique_lengths = remove_dups (List.map List.length cycle_list) in
          let common_labels =
            List.fold_left
              (fun common cycle ->
                List.filter (fun el -> List.mem el cycle) common
              ) (List.hd cycle_list) cycle_list
            in
	  if List.length unique_lengths = 1 && List.length common_labels <> 0 then (* if cycles in scc have the same length and have common label *)
	    if List.length cycle_list = 1 then cycle_list (* if it's just one cycle then output cycle *)
	    else
              (* permute cycle to common label *)
	      let common_label = List.nth common_labels 0 in
	      let rec permute_to_label label lst prev =
	        match lst with
	        | [] -> List.rev prev
	        | hd :: tl -> if label = hd then lst @ (List.rev prev)
		              else permute_to_label label tl (hd :: prev)
	      in
	      (* output permuted cycles *)
	      List.map (fun cycle -> permute_to_label common_label cycle []) cycle_list
	  else
	    let sccLabels = remove_dups (List.concat cycle_list) in
	    (* output sum of labels *)
	    List.map (fun label -> [label]) sccLabels
      ) scc_cycles
*)

  let refine labels label_to_atom refinement_graph = 
    (* get the strongly conncected components *)
    let (nSCCs, mapToComp) = SCCmod.scc refinement_graph in

    (* sccCycles is an array where sccCycles.(mapToComp node1) = sccCycles.(mapToComp node2) for any two nodes in the same scc. Also each element of sccCycles is a list of lists, where each sublist is a cycle in the strongly connected component and each cycle is oriented the same way *)
    let sccCycles = get_scc_expr_cycles refinement_graph nSCCs mapToComp in

    (* condPlus will be an automata where the only cycles are self-loops (the sccs) *)
    let condPlus = RGraph.create () in

    let cond_node_to_label = ref IntMap.(empty) in
   
    let cond_star_nodes = ref IntSet.(empty) in
 
    (* add the non-trivial scc nodes to condPlus *)
    Array.iteri
      (fun sccNum cycle_list ->
	if List.length cycle_list > 0 then (
          let cycles_extended = 
            List.map
              (fun cycle ->
                let first_el = label_to_atom (List.hd cycle) in
                let cycle_tail = List.tl cycle in
                List.fold_left 
                  (fun acc el -> PreKleene.mul acc (label_to_atom el))
                  first_el cycle_tail
              ) cycle_list 
            in
          let cycles_extend_hd = List.hd cycles_extended in
          let cycles_extend_tl = List.tl cycles_extended in
          let cycles_combine = 
            List.fold_left 
              PreKleene.add
            cycles_extend_hd cycles_extend_tl 
            in
          let cycle_val = PreKleene.star cycles_combine in
          RGraph.add_vertex condPlus sccNum;
          cond_star_nodes := IntSet.add sccNum !cond_star_nodes;
          cond_node_to_label := IntMap.add sccNum cycle_val !cond_node_to_label
        )
      ) sccCycles;

    (* add the trivial scc nodes to condPlus *)
    RGraph.iter_vertex
      (fun v ->
        let comp_num = mapToComp v in
        if not (RGraph.mem_vertex condPlus comp_num) then (
          RGraph.add_vertex condPlus comp_num;
          cond_node_to_label := IntMap.add comp_num (label_to_atom v) !cond_node_to_label
          )
      ) refinement_graph;

    (* In condPlus each node in refinementGraph may or may not get a head and tail version *)
    
    let next_node_val = ref nSCCs in

    let r_node_to_head = ref IntMap.(empty) in
    let r_node_to_tail = ref IntMap.(empty) in

    (* create component heads and tails *)
    Array.iteri
      (fun sccNum cycle_list ->
        if List.length cycle_list > 0 then
          if List.length (List.hd cycle_list) > 1 then
            List.iter
              (fun cycle ->
                let cycle_head_nodes = List.tl cycle in
                let cycle_tail_nodes = List.rev (List.tl (List.rev cycle)) in
                List.iter
                  (fun node ->
                    let cond_node = !next_node_val in
                    next_node_val := !next_node_val + 1;
                    cond_node_to_label := IntMap.add cond_node (label_to_atom node) !cond_node_to_label;
                    r_node_to_head := IntMap.add node cond_node !r_node_to_head;
                    RGraph.add_vertex condPlus cond_node
                  ) cycle_head_nodes;
                let cycle_head_to_cond = List.map (fun r_node -> IntMap.find r_node !r_node_to_head) cycle_head_nodes in
                let _ = List.fold_left
                  (fun succ_node cur_node ->
                    RGraph.add_edge condPlus cur_node succ_node;
                    cur_node
                  ) sccNum (List.rev cycle_head_to_cond) in
                List.iter
                  (fun node ->
                    let cond_node = !next_node_val in
                    next_node_val := !next_node_val + 1;
                    cond_node_to_label := IntMap.add cond_node (label_to_atom node) !cond_node_to_label;
                    r_node_to_tail := IntMap.add node cond_node !r_node_to_tail;
                    RGraph.add_vertex condPlus node
                  ) cycle_tail_nodes;
                let cycle_tail_to_cond = List.map (fun r_node -> IntMap.find r_node !r_node_to_tail) cycle_tail_nodes in
                let _ = List.fold_left
                  (fun prev_node cur_node ->
                    RGraph.add_edge condPlus prev_node cur_node;
                    cur_node
                  ) sccNum cycle_tail_to_cond in
                ()
              ) cycle_list
      ) sccCycles;


    (* add the edges between components *)
    RGraph.iter_edges 
      (fun l1 l2 -> 
	let v1 = mapToComp l1 in
	let v2 = mapToComp l2 in
	if v1 <> v2 then 
          let l1_tl =
            if not (IntMap.mem l1 !r_node_to_tail) then v1
            else (IntMap.find l1 !r_node_to_tail)
            in
          let l2_hd =
            if not (IntMap.mem l2 !r_node_to_head) then v2
            else (IntMap.find l2 !r_node_to_head)
            in
	  RGraph.add_edge condPlus l1_tl l2_hd
      ) refinement_graph;
   
    RGraph.add_vertex condPlus (-1); (* ENTER *)
    cond_node_to_label := IntMap.add (-1) PreKleene.one !cond_node_to_label;
    RGraph.add_vertex condPlus (-2); (* EXIT *)
    cond_node_to_label := IntMap.add (-2) PreKleene.one !cond_node_to_label;
    
    
    (* I'm not sure if this is needed. It depends if Top.iter allows mutation of the graph during exectution *)
    let rev_top = 
      Top.fold 
        (fun vert acc -> 
          if vert = (-1) || vert = (-2) then acc 
          else vert :: acc
        ) condPlus [] 
      in
    let top = List.rev rev_top in
    let one_from_enter_to_node = ref IntSet.(empty) in
    let one_from_node_to_exit = ref IntSet.(empty) in

    List.iter
      (fun v ->
        let predSet = IntSet.of_list (RGraph.pred condPlus v) in
        if IntSet.is_empty (IntSet.inter predSet !one_from_enter_to_node) then
          (RGraph.add_edge condPlus (-1) v);
        if IntSet.mem v !cond_star_nodes then
          one_from_enter_to_node := IntSet.add v !one_from_enter_to_node
      ) top;

    List.iter
      (fun v ->
        let succSet = IntSet.of_list (RGraph.succ condPlus v) in
        if IntSet.is_empty (IntSet.inter succSet !one_from_node_to_exit) then
          (RGraph.add_edge condPlus v (-2));
        if IntSet.mem v !cond_star_nodes then
          one_from_node_to_exit := IntSet.add v !one_from_node_to_exit
      ) rev_top;

    let labeledDag = LGraph.create () in
    RGraph.iter_vertex
      (fun v ->
        LGraph.add_vertex labeledDag v
      ) condPlus;
    
    RGraph.iter_edges
      (fun v1 v2 ->
        let edge_label = (IntMap.find v2 !cond_node_to_label) in
        LGraph.add_edge_e labeledDag (LGraph.E.create v1 edge_label v2)
      ) condPlus;


    (* labeledDag *)


    (* reverse top order. *)
    let rev_top = TopL.fold (fun vert acc -> vert :: acc) labeledDag [] in
    let node_regex_map = ref IntMap.(empty) in
    List.iter
      (fun x -> 
        node_regex_map := IntMap.add x PreKleene.one !node_regex_map
      ) rev_top;

    (* process the nodes in rev top order. Add expression to node_regex_map. Each expression represents an expression from the current node to the exit node *)
    Log.time "refine_node_collapsing" (List.iter 
      (fun node -> 
	let successor_exprs = LGraph.fold_succ
	  (fun successor acc ->
	    let labelNodeSucc = 
              LGraph.E.label (LGraph.find_edge labeledDag node successor) 
              in
            (PreKleene.mul labelNodeSucc (IntMap.find successor !node_regex_map)) :: acc
	  ) labeledDag node [] in
	let node_expr = if List.length successor_exprs = 0 then PreKleene.one
			else 
                          let successor_expr_hd = List.hd successor_exprs in
                          let successor_expr_tl = List.tl successor_exprs in
                          List.fold_left 
                            PreKleene.add 
                          successor_expr_hd successor_expr_tl 
          in
	node_regex_map := IntMap.add node node_expr !node_regex_map
      )) rev_top;

    (* the overall expression is from (nSCCs - 1) (__Enter) to (0) (__EXIT) *)
    IntMap.find (-1) !node_regex_map

  let build_refinement_graph labels label_to_atom =
    let all_pairs =
      List.concat (
        List.map
          (fun x -> List.map (fun y -> (x, y)) labels)
        labels
      ) in

    let self_check_first a b =
      if (fst a) = (snd a) then
        if (fst b) = (snd b) then Pervasives.compare a b
        else -1
      else
        if (fst b) = (snd b) then 1
        else Pervasives.compare a b
    in
    let all_pairs = List.sort self_check_first all_pairs in

    let refinement_graph = RGraph.create () in
    List.iter (fun label -> RGraph.add_vertex refinement_graph label) labels;

    let worklist = ref all_pairs in
    let self_loops = ref IntSet.(empty) in

    while List.length !worklist <> 0 do
      let pair_to_check = List.hd !worklist in
      worklist := List.tl !worklist;
      let infeasible = PreKleene.equal (PreKleene.mul (IntMap.find (fst pair_to_check) label_to_atom) (IntMap.find (snd pair_to_check) label_to_atom)) PreKleene.zero in
      if not infeasible then
        RGraph.add_edge refinement_graph (fst pair_to_check) (snd pair_to_check);
        if (fst pair_to_check) = (snd pair_to_check) then
          self_loops := IntSet.add (fst pair_to_check) !self_loops;
        let components_list = SCCmod.scc_list refinement_graph in
        let v1_comp_collap = ref (-1, false) in
        let v2_comp_collap = ref (-1, false) in
        List.iteri
          (fun list_index component ->
            let contains_self_loop = List.exists (fun el -> IntSet.mem el !self_loops) component in
            if List.mem (fst pair_to_check) component then v1_comp_collap := (list_index, contains_self_loop);
            if List.mem (snd pair_to_check) component then v2_comp_collap := (list_index, contains_self_loop);
            if contains_self_loop then
              worklist := List.filter (fun pair -> not (List.mem (fst pair) component && List.mem (snd pair) component)) !worklist
          ) components_list;
        if (fst !v1_comp_collap <> fst !v2_comp_collap) && (snd !v1_comp_collap) && (snd !v2_comp_collap) then
          worklist := List.filter (fun pair -> not (List.mem (fst pair) (List.nth components_list (fst !v1_comp_collap))) || not (List.mem (snd pair) (List.nth components_list (fst !v2_comp_collap)))) !worklist

    done;
    refinement_graph


  let refinement atoms = 
    let label_to_atom = ref IntMap.(empty) in
    let labels = ref [] in
    for i = 0 to (List.length atoms) - 1 do
      label_to_atom := IntMap.add i (List.nth atoms i) !label_to_atom;
      labels := i :: !labels
    done;
    let labels = !labels in
    let label_to_atom = !label_to_atom in
    let label_map input_label = 
      IntMap.find input_label label_to_atom
    in
    let refinement_graph = build_refinement_graph labels label_to_atom in
    Log.time "refine_final" (refine labels label_map) refinement_graph
end
