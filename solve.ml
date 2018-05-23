(* Solve a max-plus recurrence *)

open Graph;;

open Printf;;

(* Requisite types:
 *    weights: eventually GMP rationals; initially may be int; but, I do 
 *       need them to be allowed to be negative infinity
 *
 * Requisite data structures:
 *    Some numeric type...
 *    Matrix for input
 *        integer access, weight elements
 *    Digraph for matrix 
 *        Vertices have integers
 *        Edges have weight-type (eventually GMP rationals, I guess)
 *    Condensed (acyclic) digraph
 *        Vertices are addressed by integers
 *        Each vertex stands for a set of integers
 *        Edges are unweighted
 *
 *    Convenience data structures / operations:
 *         - map from components to contents
 *         - map from node to component ID
 *
 * Requisite operations:
 *    Compute a graph condensation:
 *    Topologically sort the strongly-connected components
 *    Find the ancestors of a component
 *    Find the descendants of a component
 *    Compute the simple cycles
 *
 * Better operations:
 *    Use a faster algorithm to compute slopes
 *)

type fweight = float;;  (* Finite weight. *) 
(* These are integers for now, but eventually we'll use GMP rationals *)

(* For easy dualization, I'm putting all maxes and mins in terms of best and worst *)
let fwt_best x y = max x y;;
let fwt_worst x y = min x y;;

let fwt_sub fw1 fw2 = fw1 -. fw2;;

type weight = Worst | Fin of fweight;;

let wt_add w1 w2 = 
    match w1 with | Worst -> Worst | Fin v1 ->
        match w2 with | Worst -> Worst | Fin v2 -> Fin (v1 +. v2)
;;

let wt_best w1 w2 = 
    match w1 with | Worst -> w2 | Fin v1 ->
        match w2 with | Worst -> w1 | Fin v2 -> Fin (fwt_best v1 v2)
;;

(*let wt_sub_fwt w1 fw2 =
    match w1 with | Worst -> Worst | Fin v1 -> Fin (fwt_sub v1 fw2)
;;*)

let wt_print wt = 
    match wt with | Worst -> (printf "NA") | Fin fwt -> (printf "%.1f" fwt)
;;

module V = struct
  type t = int (* vertex number *)
  let compare = Pervasives.compare
  let hash = Hashtbl.hash
  let equal = (=)
end;;
module E = struct
  type t = fweight
  let compare = Pervasives.compare
  let default = 0.0
end;;

(* Max-plus recurrence graph *)
module MPGraph = Imperative.Digraph.ConcreteLabeled(V)(E);;

module V2 = struct
  type t = int (* SCC number *)
  let compare = Pervasives.compare
  let hash = Hashtbl.hash
  let equal = (=)
end;;

module SCCGraph = Imperative.Digraph.Concrete(V2);;

(* Because Karp's algorithm uses a lot of data structures involving
 *   arrays starting at zero, I use the following imperative construct: 
 * This loops setting i from m (inclusive) up to n (inclusive). *)
let loopFromMToN m n init f = 
    let rec loopFromMToNAux i x =
        if (i > n) then x else
        loopFromMToNAux (i + 1) (f i x) in
    loopFromMToNAux m init
;;
(* Usage:
     let myResult = loopFromMToN m n initial (fun i accum ->
           (* compute new accum here using i and accum *)
         ) in
*)

let condense graph mapVertexToSCC = 
    let condensation = SCCGraph.create () in
    let doEdge e = 
        let srcSCC = mapVertexToSCC (MPGraph.E.src e) in 
        let dstSCC = mapVertexToSCC (MPGraph.E.dst e) in 
        SCCGraph.add_edge condensation srcSCC dstSCC in 
    MPGraph.iter_edges_e doEdge graph;
    condensation
;;

module Tests = struct
    module Knee1 = struct
        let matrix = [| [| (Fin 0.0);     Worst;     Worst     |];
                        [| (Fin (-14.0)); (Fin 3.0); Worst     |];
                        [| Worst;         (Fin 0.0); (Fin 1.0) |] |]
    end;;
end;;

let matrixToGraph matrix = 
    let graph = MPGraph.create () in
    let add_edges_in_row i row =
        let add_edge j wt = 
            match wt with | Worst -> () | Fin fwt ->
            MPGraph.add_edge_e graph (MPGraph.E.create i fwt j) in
        Array.iteri add_edge row in
    Array.iteri add_edges_in_row matrix;
    graph
;;

module MPComponents = Graph.Components.Make(MPGraph);;
module SCCOper = Graph.Oper.I(SCCGraph);;
module IntMap = Map.Make(struct type t = int let compare = compare end);;
module IntIntMap = Map.Make(struct type t = int * int let compare = compare end);;

(* Usage:
     let myResult = loopZeroToN n initial (fun i accum ->
           (* compute new accum here using i and accum *)
         ) in
*)

(* I chose Karp's algorithm because it was easy. *)
(*   We could use a faster alternative if time complexity becomes a concern. *)
let karpBestCycleMean graph nSCCs mapVertexToSCC mapSCCToVertices =
    (* Edges between SCCs are irrelevant, so we filter them out: *)
    let predecessors v =
        let unfiltered = MPGraph.pred graph v in
        List.filter (fun u -> ((mapVertexToSCC u) = (mapVertexToSCC v)))
                    unfiltered in
    let edge_weight u v = MPGraph.E.label (MPGraph.find_edge graph u v) in
    (* Loop over iSCC:, the SCC index *)
    loopFromMToN 0 (nSCCs - 1) IntMap.empty (fun iSCC bestCycleMean ->
        (* In this loop, we run Karp's algorithm on the iSCC^th SCC          *)
        let vertices = mapSCCToVertices.(iSCC) in 
        match vertices with 
        | [] -> failwith "Empty SCC" 
        | startVertex::_ -> (* arbitrary start vertex                        *)
        let nVertices = List.length vertices in
        (* In the following, fMap (which Karp calls "F") is an important     *)
        (*   data structure.  The (k,v) entry in fMap encodes the best       *)
        (*   total weight that can be achieved in k steps starting at        *)
        (*   startVertex and ending at v.                                    *)
        (* Set initial conditions for fMap *)
        let fMap = List.fold_left
            (fun fMap uVertex -> IntIntMap.add 
                (0, uVertex)
                (if (uVertex = startVertex) then (Fin 0.0) else Worst) 
                fMap) IntIntMap.empty vertices in
        (* Now, we will compute fMap (Karp's F_k(v)) using a recurrence.     *)
        (* Loop over the number of steps in a progression (Karp's "k"):      *)
        let fMap = loopFromMToN 1 nVertices fMap (fun steps fMap ->
            (* For each number of steps, this is what we do for each vertex: *)
            let addVertexToFMap fMap vVertex = 
                 IntIntMap.add (steps, vVertex) (* Add the following value:  *)
                    (let candidates = (List.map
                            (* Try adding one edge to the edge progresion:   *) 
                            (fun uVertex -> 
                                wt_add 
                                   (Fin (edge_weight uVertex vVertex)) 
                                   (IntIntMap.find (steps-1, uVertex) fMap))
                            (predecessors vVertex)) in

                        (* Find the best extension of this edge progression: *)
                        (List.fold_left wt_best Worst candidates))
                    fMap in (* Add that value to the map fMap                *)

            (* Loop over vVertex (the target vertex, Karp's "v"):            *)
            (List.fold_left addVertexToFMap fMap vertices)) in

        (* The heart of Karp's algorithm: *)
        (* For any given vVertex, this function computes a cycle mean for a  *)
        (*   cycle that forms part of an edge sequence ending at vVertex     *)
        let considerVertex vVertex = 
            (* Look up F_n(v), and ignore it if it's infinite                *)
            match (IntIntMap.find (nVertices, vVertex) fMap) with 
            | Worst -> Worst (* ignore *)
            | Fin fnv -> 
              (* We want the worst value, over all numbers of steps.         *)
              (*                                                             *)
              (* First, we scan over all numbers of steps (Karp's "k");      *)
              (*   we filter out infinite F_k(v) values.                     *)
              let pairs = loopFromMToN 0 (nVertices - 1) [] (fun steps pairs ->
                  (* Look up Karp's F_k(v).                                  *)
                  match (IntIntMap.find (nVertices, vVertex) fMap) with 
                  (* Ignore F_k(v) if it's infinite.                         *)
                  | Worst -> pairs
                  | Fin fkv -> (steps, fkv) :: pairs) in
              (* Now scan over pairs (steps, fkv) having finite fkv          *)
              match pairs with 
              (* There had better be at least one finite fkv...              *)
              | [] -> failwith "Failure in Karp's algorithm"
              | (steps, fkv) :: tail ->
                (* Compute a cycle mean: (F_n(v) - F_k(v)) / (n - k)         *)
                let cycleMean steps fnv fkv = 
                    (fwt_sub fnv fkv) /. (float_of_int (nVertices - steps)) in
                (* We'll initialize our fold with a finite fkv               *)
                let firstCycleMean = cycleMean steps fnv fkv in
                (* Here we specify that we want the worst, using a fold:     *)
                let foldHelper1 fwt (steps, fkv) = 
                    fwt_worst fwt (cycleMean steps fnv fkv) in
                (* Worst cycle mean among progressions ending at vVertex:    *)
                Fin (List.fold_left foldHelper1 firstCycleMean tail) in

        (* Here we specify that we want the best value over all final verts  *)
        let foldHelper2 wt vVertex = wt_best wt (considerVertex vVertex) in

        (* The best cycle mean, over all final vertices (vVertex) ...        *)
        let iSCCBestCycleMean = List.fold_left foldHelper2 Worst vertices in

        (* Add this SCC's best cycle mean to the map bestCycleMean:          *)
        (IntMap.add iSCC iSCCBestCycleMean bestCycleMean))
;;

let computeSlopes graph nSCCs mapVertexToSCC mapSCCToVertices criticalWeight = 
    let nVertices = MPGraph.nb_vertex graph in
    let condensation = condense graph mapVertexToSCC in
    let transCondensation = SCCOper.transitive_closure condensation in
    (* Initialize bounding slopes *)
    let slopes = Array.make_matrix nVertices nVertices Worst in
    (* Compute bounding slopes *)
    loopFromMToN 0 (nSCCs - 1) () (fun jSCC _ -> 
        SCCGraph.iter_pred (fun iSCC -> 
            let iVertices = mapSCCToVertices.(iSCC) in
            List.iter (fun iVertex ->
                SCCGraph.iter_succ (fun kSCC -> 
                    let kVertices = mapSCCToVertices.(kSCC) in
                    List.iter (fun kVertex ->
                        slopes.(iVertex).(kVertex) <-
                            wt_best 
                                slopes.(iVertex).(kVertex)
                                (IntMap.find jSCC criticalWeight)
                    ) kVertices
                ) transCondensation jSCC
            ) iVertices
        ) transCondensation jSCC
    );
    slopes
;;

(* (printf "nSCCs: %d\n" nSCCs); *)

let computeIntercepts graph slopes =
    let nVertices = MPGraph.nb_vertex graph in
    (* Initialize bounding intercepts *)
    let intercepts = Array.make_matrix nVertices nVertices Worst in
    loopFromMToN 0 (nVertices - 1) () (fun uVertex _ ->
        intercepts.(uVertex).(uVertex) <- Fin (0.0)
    );
    (* Compute bounding intercepts *)
    loopFromMToN 0 (nVertices - 1) () (fun iInput _ ->
        loopFromMToN 0 (nVertices - 1) () (fun iIteration _ ->
            loopFromMToN 0 (nVertices - 1) () (fun iFrom _ ->
                loopFromMToN 0 (nVertices - 1) () (fun iTo _ ->
                    match slopes.(iTo).(iInput) with
                    | Worst -> ()
                    | Fin slope ->
                        if (not (MPGraph.mem_edge graph iTo iFrom)) then ()
                        else let edge = MPGraph.E.label 
                                (MPGraph.find_edge graph iTo iFrom) in
                            intercepts.(iTo).(iInput) <-
                                wt_add intercepts.(iTo).(iInput)
                                    (Fin (fwt_sub edge slope))

                );
            );
        );
    );
    intercepts
;;

let createUpperBound graph = 
    let nVertices = MPGraph.nb_vertex graph in
    let (nSCCs, mapVertexToSCC) = (MPComponents.scc graph) in
    let mapSCCToVertices = Array.make nSCCs [] in
    loopFromMToN 0 (nVertices - 1) () (fun uVertex _ ->
        let iSCC = (mapVertexToSCC uVertex) in
        mapSCCToVertices.(iSCC) <- uVertex :: mapSCCToVertices.(iSCC));
    let criticalWeight = 
        karpBestCycleMean graph nSCCs mapVertexToSCC mapSCCToVertices in 
    let slopes = 
        computeSlopes graph nSCCs mapVertexToSCC mapSCCToVertices criticalWeight in
    let intercepts = 
        computeIntercepts graph slopes in
    (slopes, intercepts)
;;

let printMatrix matrix =
    loopFromMToN 0 ((Array.length matrix) - 1) () (fun iRow _ ->
        (printf "[");
        let row = matrix.(iRow) in
        let rowLength = (Array.length row) in 
        loopFromMToN 0 (rowLength - 1) () (fun iCol _ ->
            (wt_print row.(iCol));
            if (iCol < rowLength - 1) then (printf "\t") else ()
        );
        (printf "]\n");
    )
;;

let doTest matrix = 
    (printf "Input matrix:\n");
    printMatrix matrix;
    let graph = matrixToGraph matrix in
    let (slopes,intercepts) = createUpperBound graph in
    (printf "Slopes:\n");
    printMatrix slopes;
    (printf "Intercepts:\n");
    printMatrix intercepts;
    (printf "\n")
;;

let _ = 
    doTest Tests.Knee1.matrix;
    ()
;;

(*
let createUpperBound () = 
  (*  1. Construct a graph representation of the loop body matrix *) 
  (*  2. Compute the condensation of our graph *)
  (*  3. Compute critical circuit average weights (a.k.a. "critical weights") *)
  (*  4. Compute the bounding slopes: *)
  (*    First, initialize the values *)

  (*    The bounding slope in position (i,k) is the highest critical weight that is found    *)
  (*      in any circuit that is reachable from i and that can reach k.                      *)
  (*    So, we loop over each SCC (call it j),                                               *)
  (*      find all upstream SCCs (call each such i),                                         *)
  (*      and downstream SCCs (call each such k);                                            *)
  (*      then, what we have is (SCC_i) --*--> (SCC_j) --*--> (SCC_k)                        *)
  (*    Each time we find such a j, we update our slope for (i,k) to be j's critical weight  *)
  (*      if j's critical weight is greater than our current slope for (i,k).                *)
  (*  5. Compute the bounding intercepts (perform the "intercept propagation" steps)         *)

;;
*)



