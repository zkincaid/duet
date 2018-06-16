(* Solve a max-plus or min-plus recurrence *)

open Graph;;
open Printf;;
include Tropical_defs;;
open Printing;;

(* ------------------------------------------------------------------------- *)

(* Because Karp's algorithm uses a lot of data structures involving
 *   arrays starting at zero, I use the following imperative construct: 
 * We repeat f, setting i from m (inclusive) up to n (inclusive). *)
let loopFromMToN m n ?(increment=1) init f = 
    let test = if (increment > 0) then (fun i -> i > n) else (fun i -> i < n) in
    let rec loopFromMToNAux i x =
        if (test i) then x else
        loopFromMToNAux (i + increment) (f i x) in
    loopFromMToNAux m init
;;
(* Usage:
     let myResult = loopFromMToN m n initial (fun i accum ->
           (* compute new accum here using i and accum *)
         ) in
*)

(* ------------------------------------------------------------------------- *)

let condense graph nSCCs mapVertexToSCC = 
    let condensation = SCCGraph.create () in
    loopFromMToN 0 (nSCCs - 1) () (fun iSCC _ -> 
        SCCGraph.add_vertex condensation iSCC);
    let doEdge e = 
        let srcSCC = mapVertexToSCC (MPGraph.E.src e) in 
        let dstSCC = mapVertexToSCC (MPGraph.E.dst e) in 
        SCCGraph.add_edge condensation srcSCC dstSCC in 
    MPGraph.iter_edges_e doEdge graph;
    condensation
;;

let matrixToGraph matrix = 
    let graph = MPGraph.create () in
    Array.iteri (fun iVar row -> MPGraph.add_vertex graph iVar) matrix;
    let add_edges_in_row i row =
        let add_edge j wt = 
            match wt with | Inf -> () | Fin fwt ->
            MPGraph.add_edge_e graph (MPGraph.E.create i fwt j) in
        Array.iteri add_edge row in
    Array.iteri add_edges_in_row matrix;
    graph
;;

let alphabet = [|"a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"; "m";
                 "n"; "o"; "p"; "q"; "r"; "s"; "t"; "u"; "v"; "w"; "x"; "y"; "z"|]
;;

(* ------------------------------------------------------------------------- *)

let augmentMatrix matrix vector =
    let nVars = Array.length matrix in
    let augmented = Array.make_matrix (nVars + 1) (nVars + 1) Inf in
    loopFromMToN 0 nVars () (fun uVar _ ->
        loopFromMToN 0 nVars () (fun vVar _ ->
            if (vVar < nVars) then (
                if (uVar < nVars) then 
                    augmented.(uVar).(vVar) <- matrix.(uVar).(vVar)
                else ()
            ) else (
                if (uVar < nVars) then 
                    augmented.(uVar).(vVar) <- vector.(uVar)
                else
                    augmented.(uVar).(vVar) <- Fin fwt_zero)));
    augmented;;

let unaugmentMatrix augmented =
    let nVars = (Array.length augmented) - 1 in
    let matrix = Array.make_matrix nVars nVars Inf in
    let vector = Array.make nVars Inf in
    loopFromMToN 0 (nVars - 1) () (fun uVar _ ->
        loopFromMToN 0 nVars () (fun vVar _ ->
            if (vVar < nVars) then (
                matrix.(uVar).(vVar) <- augmented.(uVar).(vVar) 
            ) else (
                vector.(vVar) <- augmented.(uVar).(vVar))));
    (matrix, vector);;

(* ------------------------------------------------------------------------- *)

(* For easy dualization, I wrote my algorithms in terms of "best" and "worst";
 * in the max-plus semiring, best is max and worst is min;
 * in the min-plus semiring, best is min and worst is max. *)

module type DIRECTION = 
    sig
        val best : fweight -> fweight -> fweight
        val best_expr : expr list -> expr
        val best_noun : string
        val bound : expr -> expr -> inequation
        val bound_symbol : string
        val bound_adjective : string
        val worst : fweight -> fweight -> fweight
        val name : string
    end;;

module MaxDirection = 
    struct
        let best x y = if Mpq.cmp x y >= 0 then x else y
        let best_expr elist = Max elist
        let best_noun = "max"
        let bound e1 e2 = LessEq (e1, e2)
        let bound_symbol = "<="
        let bound_adjective = "Upper"
        let worst x y = if Mpq.cmp x y >= 0 then y else x
        let name = "Max-Plus"
    end;;

module MinDirection = 
    struct
        let best x y = if Mpq.cmp x y <= 0 then x else y;;
        let best_expr elist = Min elist;;
        let best_noun = "min"
        let bound e1 e2 = GreaterEq (e1, e2);;
        let bound_symbol = ">="
        let bound_adjective = "Lower"
        let worst x y = if Mpq.cmp x y <= 0 then y else x;;
        let name = "Min-Plus"
    end;;

(* ------------------------------------------------------------------------- *)

module Solver =
    functor (Dir: DIRECTION) ->
        struct
(* continues without indentation: *)
(* ======================================================================= *)


let wt_add w1 w2 = 
    match w1 with | Inf -> Inf | Fin v1 ->
        match w2 with | Inf -> Inf | Fin v2 -> Fin (fwt_add v1 v2)
;;

let wt_best w1 w2 = 
    match w1 with | Inf -> w2 | Fin v1 ->
        match w2 with | Inf -> w1 | Fin v2 -> Fin (Dir.best v1 v2)
;;

(* ------------------------------------------------------------------------- *)

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
                (if (uVertex = startVertex) then Fin fwt_zero else Inf) 
                fMap) IntIntMap.empty vertices in
        (* Now, we will compute fMap (Karp's F_k(v)) using a recurrence.     *)
        (* Loop over the number of steps (Karp's "k") in a progression:      *)
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
                        (List.fold_left wt_best Inf candidates))
                    fMap in (* Add that value to the map fMap                *)

            (* Loop over vVertex (the target vertex, Karp's "v"):            *)
            (List.fold_left addVertexToFMap fMap vertices)) in

        (*let _ = (printFMapEntries fMap startVertex) in*)
        
        (* The heart of Karp's algorithm: *)
        (* For any given vVertex, this function computes a cycle mean for a  *)
        (*   cycle that forms part of an edge sequence ending at vVertex     *)
        let considerVertex vVertex = 
            (* Look up F_n(v), and ignore it if it's infinite                *)
            match (IntIntMap.find (nVertices, vVertex) fMap) with 
            | Inf -> Inf (* ignore *)
            | Fin fnv -> 
              (* We want the worst value, over all numbers of steps.         *)
              (*                                                             *)
              (* First, we scan over all numbers of steps (Karp's "k");      *)
              (*   we filter out infinite F_k(v) values.                     *)
              let pairs = loopFromMToN 0 (nVertices - 1) [] (fun steps pairs ->
                  (* Look up Karp's F_k(v).                                  *)
                  match (IntIntMap.find (steps, vVertex) fMap) with 
                  (* Ignore F_k(v) if it's infinite.                         *)
                  | Inf -> pairs
                  | Fin fkv -> (steps, fkv) :: pairs) in

              (*let _ = (printIntFloatPairList pairs; printf "\n") in*)

              (* Now scan over pairs (steps, fkv) having finite fkv          *)
              match pairs with 
              (* There had better be at least one finite fkv...              *)
              | [] -> failwith "Failure in Karp's algorithm"
              | (steps, fkv) :: tail ->
                (* Compute a cycle mean: (F_n(v) - F_k(v)) / (n - k)         *)
                let cycleMean steps fnv fkv = 
                    fwt_div (fwt_sub fnv fkv) 
                            (fwt_sub (fwt_from_int nVertices) 
                                     (fwt_from_int steps)) in
                (* We'll initialize our fold with a finite fkv               *)
                let firstCycleMean = cycleMean steps fnv fkv in
                (* Here we specify that we want the worst, using a fold:     *)
                let foldHelper1 fwt (steps, fkv) = 
                    Dir.worst fwt (cycleMean steps fnv fkv) in
                (* Worst cycle mean among progressions ending at vVertex:    *)
                Fin (List.fold_left foldHelper1 firstCycleMean tail) in

        (* Here we specify that we want the best value over all final verts  *)
        let foldHelper2 wt vVertex = wt_best wt (considerVertex vVertex) in

        (* The best cycle mean, over all final vertices (vVertex) ...        *)
        let iSCCBestCycleMean = List.fold_left foldHelper2 Inf vertices in

        (* Add this SCC's best cycle mean to the map bestCycleMean:          *)
        (IntMap.add iSCC iSCCBestCycleMean bestCycleMean))
;;

let computeSlopes graph nSCCs mapVertexToSCC mapSCCToVertices criticalWeight = 
    let nVertices = MPGraph.nb_vertex graph in
    let condensation = condense graph nSCCs mapVertexToSCC in
    let transCondensation = SCCOper.transitive_closure condensation ~reflexive:true in
    (* Initialize bounding slopes *)
    let slopes = Array.make_matrix nVertices nVertices Inf in
    (* Compute bounding slopes *)
    (*    The bounding slope in position (i,k) is the highest critical       *)
    (*    weight that is found in any circuit that is reachable from i       *) 
    (*    and that can reach k.                                              *)
    (*    So, we loop over each SCC (call it j),                             *)
    (*      find all upstream SCCs (call each such i),                       *)
    (*      and downstream SCCs (call each such k);                          *)
    (*      then, what we have is (SCC_i) --*--> (SCC_j) --*--> (SCC_k)      *)
    (*    Each time we find such a j, we update our slope for (i,k) to be    *)
    (*      j's critical weight if j's critical weight is greater than our   *)
    (*      current slope for (i,k).                                         *)
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

let computeIntercepts graph slopes =
    let nVertices = MPGraph.nb_vertex graph in
    (* Initialize bounding intercepts *)
    let intercepts = Array.make_matrix nVertices nVertices Inf in
    loopFromMToN 0 (nVertices - 1) () (fun uVertex _ ->
        intercepts.(uVertex).(uVertex) <- Fin fwt_zero 
    );
    (* Compute bounding intercepts *)
    loopFromMToN 0 (nVertices - 1) () (fun iInput _ ->
        loopFromMToN 0 (nVertices - 1) () (fun iIteration _ ->
            loopFromMToN 0 (nVertices - 1) () (fun iFrom _ ->
                loopFromMToN 0 (nVertices - 1) () (fun iTo _ ->
                    (* Briefly:                           *)
                    (*   intercept[iTo,iInput] <-         *)
                    (*     best (intercept[iTo,iInput],   *)
                    (*           intercept[iFrom,iInput]  *)
                    (*           + edge[iTo,iFrom]        *)
                    (*           - slope[iTo,iInput])     *)
                    match slopes.(iTo).(iInput) with
                    | Inf -> ()
                    | Fin slope ->
                        if (not (MPGraph.mem_edge graph iTo iFrom)) then ()
                        else let edgeLabel = MPGraph.E.label 
                                (MPGraph.find_edge graph iTo iFrom) in
                            intercepts.(iTo).(iInput) <-
                                wt_best intercepts.(iTo).(iInput)
                                    (wt_add intercepts.(iFrom).(iInput)
                                        (Fin (fwt_sub edgeLabel 
                                                      slope)))

                );
            );
        );
    );
    intercepts
;;

let computeInverseVertexMap nSCCs nVertices mapVertexToSCC = 
    let mapSCCToVertices = Array.make nSCCs [] in
    loopFromMToN 0 (nVertices - 1) () (fun uVertex _ ->
        let iSCC = (mapVertexToSCC uVertex) in
        mapSCCToVertices.(iSCC) <- uVertex :: mapSCCToVertices.(iSCC));
    mapSCCToVertices
;;

let createBound graph =
    let nVertices = MPGraph.nb_vertex graph in
    (*  Step 1. Compute the condensation of our graph *)
    let (nSCCs, mapVertexToSCC) = (MPComponents.scc graph) in
    let mapSCCToVertices = computeInverseVertexMap nSCCs nVertices mapVertexToSCC in
    (*  Step 2. Compute critical circuit average weights *)
    let criticalWeight = 
        karpBestCycleMean graph nSCCs mapVertexToSCC mapSCCToVertices in 
    (*let _ = printCriticalWeights criticalWeight mapSCCToVertices in*)
    (*  Step 3. Compute the bounding slopes: *)
    let slopes = 
        computeSlopes graph nSCCs mapVertexToSCC mapSCCToVertices criticalWeight in
    (*  Step 4. Compute the bounding intercept: *)
    let intercepts = 
        computeIntercepts graph slopes in
    (slopes, intercepts)
;;

let createInequations loopCounterName variableNames slopes intercepts hasConstantColumn =
    let loopCounter = Input_variable loopCounterName in
    let subscript = SSVar loopCounterName in
    let makeBest subterms = if List.length subterms = 1 then
        List.nth subterms 0 else Dir.best_expr subterms in 
    let nCols = Array.length slopes in
    let nVars = if (hasConstantColumn) then nCols - 1 else nCols in
    loopFromMToN 0 (nVars - 1) [] (fun iOut inequations ->
        let subterms = loopFromMToN 0 (nCols - 1) [] (fun iIn subterms ->
            match slopes.(iOut).(iIn) with
            | Inf -> subterms
            | Fin slope ->
                match intercepts.(iOut).(iIn) with
                | Inf -> subterms
                | Fin intercept -> let subterm =
                    let addSlope summands = 
                        if fwt_is_zero slope then summands else
                        if fwt_is_one slope then loopCounter :: summands else
                        Product [loopCounter; Rational slope] :: summands in
                    let addIntercept summands = 
                        if fwt_is_zero intercept then summands else
                        Rational intercept :: summands in
                    let makeSum summands = 
                        match summands with 
                        | [] -> Rational fwt_zero
                        | one :: rest -> if List.length rest = 0 then one
                            else Sum summands in
                    if (iIn < nVars) then
                        (* This is for subterms based on variables. *)
                        (* template:   k * slope + intercept + inVar_0   *)
                        makeSum (addSlope (addIntercept
                            [ Base_case (variableNames.(iIn), 0) ]))
                    else
                        (* This is for the subterm based on a constant. *)
                        (* template:   k * slope + intercept   *)
                        makeSum (addSlope (addIntercept [])) in
                    subterm :: subterms
        ) in if List.length subterms = 0 then inequations (* no bound *)
        else let outVar = Output_variable (variableNames.(iOut), subscript) in
        (* inequation is a max/min over one or more subterms, like: *)
        (*    outVar <= max( ... subterms ... )                     *)
        (*      or, dually:                                         *)
        (*    outVar >= min( ... subterms ... )                     *)
        let inequation = Dir.bound outVar (makeBest subterms) in
        inequation :: inequations (* we built a new inequation *)
    )
;;

(* ----------------------------------------------------------------------- *)

let solveForBoundingMatricesFromMatrix matrix =
    let graph = matrixToGraph matrix in
    createBound graph
;;

let solveForInequationsFromMatrix matrix variableNames loopCounterName =
    let (slopes, intercepts) = solveForBoundingMatricesFromMatrix matrix in
    createInequations loopCounterName variableNames slopes intercepts false
;;

let solveForBoundingMatricesFromMatrixAndVector matrix vector =
    let augmented = augmentMatrix matrix vector in 
    let (slopes, intercepts) = solveForBoundingMatricesFromMatrix augmented in
    (unaugmentMatrix slopes, unaugmentMatrix intercepts)
;;

let solveForInequationsFromMatrixAndVector matrix vector variableNames loopCounterName =
    let augmented = augmentMatrix matrix vector in 
    let (slopes, intercepts) = solveForBoundingMatricesFromMatrix augmented in
    createInequations loopCounterName variableNames slopes intercepts true
;;

(* let computeBoundingMatricesFromEquations equations = ;; *)
(* let computeInequationsFromEquations equations = ;; *)

(* ----------------------------------------------------------------------- *)

let doMatrixTest matrix = 
    (printf "  Input (%s) matrix:\n" Dir.name);
    printMatrix matrix;
    let graph = matrixToGraph matrix in
    let (slopes,intercepts) = createBound graph in
    (* (printf "Slopes:\n"); printMatrix slopes;
    (printf "Intercepts:\n"); printMatrix intercepts; (printf "\n") *)
    (*(printf "  %s bound:\n" Dir.bound_adjective);
    printBound ~variableNames:alphabet slopes intercepts;*)
    let inequations = (createInequations "K" alphabet slopes intercepts false) in
    (printf "  As inequations:\n");
    (List.iter 
        (fun ineq -> (printf "    %s\n" (Printing.stringifyInequation ineq))) 
        inequations);
    ()
;;

let doMatrixVectorTest matrix vector = 
    (printf "  Input (%s) matrix and vector:\n" Dir.name);
    printMatrixAndVector matrix vector;
    let augmented = augmentMatrix matrix vector in
    let graph = matrixToGraph augmented in
    let (slopes, intercepts) = createBound graph in
    (* (printf "Slopes:\n"); printMatrix slopes;
    (printf "Intercepts:\n"); printMatrix intercepts; (printf "\n") *)
    (*(printf "  %s bound:\n" Dir.bound_adjective);
    printBound ~variableNames:alphabet slopes intercepts;*)
    let inequations = (createInequations "K" alphabet slopes intercepts true) in
    (printf "  As inequations:\n");
    (List.iter 
        (fun ineq -> (printf "    %s\n" (Printing.stringifyInequation ineq))) 
        inequations);
    ()
;;

(* ======================================================================= *)
(*   The body of the Solver functor is not indented. *)
  end;;
(* This is the end of the Solver functor. *)

module MaxPlus = Solver(MaxDirection);;
module MinPlus = Solver(MinDirection);;

(* ----------------------------------------------------------------------- *)

let maxPlusMatrixTest = MaxPlus.doMatrixTest;;
let minPlusMatrixTest = MinPlus.doMatrixTest;;

let maxPlusMatrixVectorTest = MaxPlus.doMatrixVectorTest;;
let minPlusMatrixVectorTest = MinPlus.doMatrixVectorTest;;

(* ----------------------------------------------------------------------- *)
(*    These functions are the public interface of our solver:              *)

let maxPlusSolveForBoundingMatricesFromMatrix = MaxPlus.solveForBoundingMatricesFromMatrix ;;
let minPlusSolveForBoundingMatricesFromMatrix = MinPlus.solveForBoundingMatricesFromMatrix ;;


let maxPlusSolveForInequationsFromMatrix = MaxPlus.solveForInequationsFromMatrix ;;
let minPlusSolveForInequationsFromMatrix = MinPlus.solveForInequationsFromMatrix ;;


let maxPlusSolveForBoundingMatricesFromMatrixAndVector = MaxPlus.solveForBoundingMatricesFromMatrixAndVector ;;
let minPlusSolveForBoundingMatricesFromMatrixAndVector = MinPlus.solveForBoundingMatricesFromMatrixAndVector ;;


let maxPlusSolveForInequationsFromMatrixAndVector = MaxPlus.solveForInequationsFromMatrixAndVector ;;
let minPlusSolveForInequationsFromMatrixAndVector = MinPlus.solveForInequationsFromMatrixAndVector ;;

(* let computeBoundingMatricesFromEquations equations = ;; *)
(* let computeInequationsFromEquations equations = ;; *)

