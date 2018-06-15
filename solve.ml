(* Solve a max-plus recurrence *)

open Graph;;

open Printf;;

(* ------------------------------------------------------------------------- *)

type subscript = 
  | SAdd of string * int    (** n+1, n+2, ... *)
  | SSVar of string         (** n *)
(*  | SSDiv of string * int   (** n/2, n/3, .. *) *)
  ;;

type expr = 
(* Use N-ary MPProduct and MPSum in preference to these *)
(*        | Plus of expr * expr     (** Binary addition *)
          | Minus of expr * expr    (** Binary subtraction *)
          | Times of expr * expr    (** Binary multiplication *)
          | Divide of expr * expr   (** Binary division *) *)
          | Product of expr list    (** N-ary multiplication *)
          | Sum of expr list        (** N-ary addition *)
          | Max of expr list        (** N-ary max *)
          | Min of expr list        (** N-ary min *)
       (* | Symbolic_Constant of string (** "x", "y", etc *) *)
          | Base_case of string * int   (** y_0, y_1, ... *)
          | Output_variable of string * subscript (** y_n, y_n+1, y_n+2, ... *)
          | Input_variable of string    (** Index variable *)

          | Rational of Mpq.t       (** @see <http://www.inrialpes.fr/pop-art/people/bjeannet/mlxxxidl-forge/mlgmpidl/html/Mpq.html> Not the package used here, but is equivalent to the documentation used in ocaml format*)

(*          | Pow of expr * expr      (** Binary exponentiation *) *)
(*          | Iif of string * subscript   (** Impliciltly intrepreted function *) *)
          ;;

type ovec = Ovec of string array * subscript;;

type matrix_rec =
          | VEquals of ovec * Mpq.t array array * ovec * expr array
(* for future use: *)
(*        | VLess of ovec * Mpq.t array array * ovec * expr array
          | VLessEq of ovec * Mpq.t array array * ovec * expr array
          | VGreater of ovec * Mpq.t array array * ovec * expr array
          | VGreaterEq of ovec * Mpq.t array array * ovec * expr array *)
          ;;

          
type inequation = 
          | Equals of expr * expr
          | LessEq of expr * expr
          | GreaterEq of expr * expr
;;

(* ------------------------------------------------------------------------- *)

(* Finite weights: *)
type fweight = Mpq.t;;
(* Possibly-infinite weights: *)
type weight = Inf | Fin of fweight;;

(* I should really make the following into a module that is a parameter to 
 *  the algorithm below, which should be another module *)

let fwt_add x y = 
    let retval = Mpq.init () in
    let _ = Mpq.add retval x y in
    retval;;
let fwt_sub x y =
    let retval = Mpq.init () in
    let _ = Mpq.sub retval x y in
    retval;;
let fwt_div x y =
    let retval = Mpq.init () in
    let _ = Mpq.div retval x y in
    retval;;
let fwt_from_int i = 
    let retval = Mpq.init () in 
    let _ = Mpq.set_si retval i 1 in
    retval;;
let fwt_zero = (* Should this be a function taking () ? *)
    let retval = Mpq.init () in 
    (* let _ = Mpq.set_si retval 0 0 in *)
    retval;;
let fwt_sprintf fwt = sprintf "%.1f" (Mpq.to_float fwt);;
let fwt_is_zero fwt = if Mpq.sgn fwt = 0 then true else false;; (*convenience*)

(* ------------------------------------------------------------------------- *)

(* For easy dualization, I'm putting all maxes and mins in terms of best and worst *)
let fwt_best x y = if Mpq.cmp x y >= 0 then x else y;;  (* DUALIZE *)
let fwt_best_expr elist = Max elist;;                   (* DUALIZE *)
let fwt_bound e1 e2 = LessEq (e1, e2);;                 (* DUALIZE *)
let fwt_worst x y = if Mpq.cmp x y >= 0 then y else x;; (* DUALIZE *)

module type DIRECTION = 
    sig
        val best : fweight -> fweight -> fweight
        val best_expr : expr list -> expr
        val bound : expr -> expr -> inequation
        val worst : fweight -> fweight -> fweight
        val word : string
        val symbol : string
    end;;

module MaxDirection = 
    struct
        let best x y = if Mpq.cmp x y >= 0 then x else y
        let best_expr elist = Max elist
        let bound e1 e2 = LessEq (e1, e2)
        let bound_symbol = "<="
        let worst x y = if Mpq.cmp x y >= 0 then y else x
        let word = "Upper"
    end;;

module MinDirection = 
    struct
        let best x y = if Mpq.cmp x y <= 0 then x else y;;
        let best_expr elist = Min elist;;
        let bound e1 e2 = GreaterEq (e1, e2);;
        let bound_symbol = ">="
        let worst x y = if Mpq.cmp x y <= 0 then y else x;;
        let word = "Lower"
    end;;

(* ------------------------------------------------------------------------- *)


let wt_add w1 w2 = 
    match w1 with | Inf -> Inf | Fin v1 ->
        match w2 with | Inf -> Inf | Fin v2 -> Fin (fwt_add v1 v2)
;;

let wt_best w1 w2 = 
    match w1 with | Inf -> w2 | Fin v1 ->
        match w2 with | Inf -> w1 | Fin v2 -> Fin (fwt_best v1 v2)
;;

let wt_sprintf wt = 
    match wt with | Inf -> (sprintf "NA") | Fin fwt -> fwt_sprintf fwt
;;

let wt_print wt = print_string (wt_sprintf wt);;

(* ------------------------------------------------------------------------- *)

module V = struct
  type t = int (* vertex number *)
  let compare = Pervasives.compare
  let hash = Hashtbl.hash
  let equal = (=)
end;;
module E = struct
  type t = fweight
  let compare = Pervasives.compare
  let default = fwt_zero
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

module MPComponents = Graph.Components.Make(MPGraph);;

module SCCOper = Graph.Oper.I(SCCGraph);;

module IntMap = Map.Make(struct type t = int let compare = compare end);;
module IntIntMap = Map.Make(struct type t = int * int let compare = compare end);;

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

let printMatrix matrix =
    let nRows = Array.length matrix in 
    if nRows = 0 then () else
    loopFromMToN 0 (nRows - 1) () (fun iRow _ ->
        (printf "    [ ");
        let row = matrix.(iRow) in
        let rowLength = (Array.length row) in 
        loopFromMToN 0 (rowLength - 1) () (fun iCol _ ->
            (wt_print row.(iCol));
            if (iCol < rowLength - 1) then (printf "\t") else ()
        );
        (printf " ]\n")
    )
;;

let rec printIntList intList = 
    match intList with | [] -> () | i :: rest ->
        (printf "%d " i; printIntList rest)
;;

let rec printIntFloatPairList theList = 
    match theList with | [] -> () | (i,f) :: rest ->
        (printf "(%d,%f) " i f; printIntFloatPairList rest)
;;

let rec printFMapEntries fMap iVertex = 
    let rec printFMapEntriesForOneVertex fMap iVertex steps = 
        if not (IntIntMap.mem (steps, iVertex) fMap) then () else 
         (wt_print (IntIntMap.find (steps, iVertex) fMap);
          printf " "; 
          printFMapEntriesForOneVertex fMap iVertex (steps + 1)) in
    if not (IntIntMap.mem (0, iVertex) fMap) then () else 
        (printf "Vertex %d has the sequence [ " iVertex;
         printFMapEntriesForOneVertex fMap iVertex 0;
         printf "]\n";
         printFMapEntries fMap (iVertex + 1))
;;

let printCriticalWeights criticalWeight mapSCCToVertices = 
    let printACriticalWeight iSCC wt = 
        (printf "SCC %d is [ " iSCC; 
         printIntList mapSCCToVertices.(iSCC); 
         printf "] and its critical weight is ";
         wt_print wt;
         printf "\n") in
    IntMap.iter printACriticalWeight criticalWeight
;;

let rec spaces i = if i <= 0 then "" else " "^(spaces (i-1))
;;

let alphabet = ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"; "m";
                "n"; "o"; "p"; "q"; "r"; "s"; "t"; "u"; "v"; "w"; "x"; "y"; "z"]
;;

let printUpperBound ?(variableNames=alphabet) slopes intercepts =
    let globalPrefix = "    " in
    let getVarName i =
        if (i < List.length variableNames) then List.nth variableNames i
        else "var("^(string_of_int i)^")" in
    let nVariables = Array.length slopes in
    let slopeString uVar vVar = 
        let slope = slopes.(uVar).(vVar) in
        match slope with 
        | Inf -> (false,"") 
        | Fin fwt -> if fwt_is_zero fwt then (true,"") else
                     (true,(sprintf " + (K * %s)" (wt_sprintf slope))) in
    let interceptString uVar vVar = 
        let intercept = intercepts.(uVar).(vVar) in
        match intercept with 
        | Inf -> (false,"") 
        | Fin fwt -> if fwt_is_zero fwt then (true,"") else
                     (true,(sprintf " + %s" (wt_sprintf intercept))) in 
    loopFromMToN 0 (nVariables - 1) () (fun uVar _ ->
        let header = (sprintf "%s%s[K] <= " globalPrefix (getVarName uVar)) in
        let prefix = (spaces (4 + (String.length header))) in
        (print_string header);
        let subterms = loopFromMToN (nVariables - 1) 0 ~increment:(-1) [] (fun vVar subterms ->
            let (bSlope, sSlope) = slopeString uVar vVar in
            let (bIntercept, sIntercept) = interceptString uVar vVar in
            if (not bSlope || not bIntercept) then subterms else
            let s = (sprintf "%s[0]%s%s" (getVarName vVar) sSlope sIntercept)
            in s :: subterms) in
        match subterms with 
        | [] -> printf "No bound\n"
        | str :: tail ->
            if ((List.length tail) = 0) then (printf "%s\n" str)
            else (printf "max(%s" str;
                  List.iter (fun str -> printf ",\n%s%s" prefix str) tail;
                  printf ")\n"))
;;

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
                    fwt_worst fwt (cycleMean steps fnv fkv) in
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

let createUpperBound graph =
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

let createInequations loopCounterName variableNames slopes intercepts = 
    let loopCounter = Input_variable loopCounterName in 
    let subscript = SSVar loopCounterName in
    let nVars = Array.length slopes in 
    loopFromMToN 0 (nVars - 1) [] (fun iOut inequations ->
        let subterms = loopFromMToN 0 (nVars - 1) [] (fun iIn subterms ->
            match slopes.(iOut).(iIn) with
            | Inf -> subterms
            | Fin slope -> match intercepts.(iOut).(iIn) with
                | Inf -> subterms
                | Fin intercept -> let subterm =
                    (* subterms look like:  k * slope + intercept + inVar_0  *)
                    Sum [ Product [loopCounter; Rational slope];
                          Rational intercept;
                          Base_case (variableNames.(iIn), 0) ] in
                    subterm :: subterms
        ) in if List.length subterms = 0 then inequations (* no bound *)
        else let outVar = Output_variable (variableNames.(iOut), subscript) in
        (* inequation is a max/min over one or more subterms, like: *)
        (*    outVar <= max( ... subterms ... )                     *)
        (*      or, dually:                                         *)
        (*    outVar >= min( ... subterms ... )                     *)
        let inequation = fwt_bound outVar (fwt_best_expr subterms) in
        inequation :: inequations (* we built a new inequation *)
    )
;;

(* ----------------------------------------------------------------------- *)
(*    These functions are the public interface of our solver:              *)

(* matrix is a weight array array *)
let solveForBoundingMatricesFromMatrix matrix =
    let graph = matrixToGraph matrix in
    createUpperBound graph
    (* returns a pair of weight array arrays: (slopes, intercepts) *)
;;

(* matrix is a weight array array *)
(* variableNames is a string array *)
(* loopCounterName is a string *)
let solveForInequationsFromMatrix matrix variableNames loopCounterName =
    let (slopes, intercepts) = solveForBoundingMatricesFromMatrix matrix in
    createInequations loopCounterName variableNames slopes intercepts
    (* returns an inequation list *)
;;

(* let computeBoundingMatricesFromEquations equations = ;; *)
(* let computeInequationsFromEquations equations = ;; *)

(* ----------------------------------------------------------------------- *)

type mpTest = {
    name : string;
    matrix : weight array array;
};;

let na = Inf;;
let d fwt = Fin (fwt_from_int fwt);;
let tests = [

    {name="knee-1"; matrix=[| 
     [| (d 0);     na;    na    |];
     [| (d (-14)); (d 3); na    |];
     [| na;        (d 0); (d 1) |];
    |] };

    {name="knee-2b"; matrix=[| 
     [| (d 5); na;    na;    na;    na;    na     |];
     [| (d 0); (d 0); na;    na;    na;    na     |];
     [| na;    (d 0); (d 0); na;    na;    na     |];
     [| na;    na;    (d 0); (d 0); na;    na     |];
     [| na;    na;    na;    (d 0); (d 0); na     |];
     [| na;    na;    na;    na;    (d 0); (d 1); |];
    |] };

    {name="zigzag-2b"; matrix=[| 
     [| na;    na;    na;    (d 7)  |];
     [| (d 0); na;    na;    na     |];
     [| na;    (d 0); na;    na     |];
     [| na;    na;    (d 1); na     |];
    |] };

    {name="zigzag-3"; matrix=[| 
     [| na;       na;       na;        (d (-3)) |];
     [| (d (-1)); na;       na;        na       |];
     [| na;       (d (-1)); na;        na       |];
     [| na;       na;       (d (-15)); na       |];
    |] };

    {name="zigzag-4"; matrix=[| 
     [| na;    (d (-1)); |];
     [| (d 1); na;       |];
    |] };

    {name="zigzag-5"; matrix=[| 
     [| na;    (d 2); na;    na;     na;    |];
     [| (d 0); na;    na;    na;     na;    |];
     [| na;    na;    na;    (d 10); na;    |];
     [| na;    na;    (d 0); na;     na;    |];
     [| (d 0); na;    na;    (d 0);  na;    |];
    |] };

    {name="cornercases-zerovars"; matrix=[| 
    |] };

    {name="cornercases-onevar"; matrix=[| 
     [| (d 5)|];
    |] };

    {name="cornercases-onevar-all-infinite"; matrix=[| 
     [| na |];
    |] };

    {name="cornercases-all-infinite-1"; matrix=[| 
     [| na;        na;    na    |];
     [| (d 0);     na;    na    |];
     [| (d (-14)); (d 3); na    |];
    |] };

    {name="cornercases-all-infinite-2"; matrix=[| 
     [| (d 0);     na;    na    |];
     [| na;        na;    na    |];
     [| (d (-14)); (d 3); na    |];
    |] };

    {name="cornercases-all-infinite-3"; matrix=[| 
     [| (d 0);     na;    na    |];
     [| (d (-14)); (d 3); na    |];
     [| na;        na;    na    |];
    |] };

];;

let doTest matrix = 
    (printf "  Input matrix:\n");
    printMatrix matrix;
    let graph = matrixToGraph matrix in
    let (slopes,intercepts) = createUpperBound graph in
    (*
    (printf "Slopes:\n");
    printMatrix slopes;
    (printf "Intercepts:\n");
    printMatrix intercepts;
    (printf "\n")
    *)
    printf "  Upper bound:\n";
    printUpperBound ~variableNames:alphabet slopes intercepts;
    ()
;;

let _ = 
    List.iter (fun test ->
        printf "**** TEST %s****\n" test.name; doTest test.matrix; printf "\n") 
        tests;
    (printf "**** ALL TESTS COMPLETE\n")
;;
