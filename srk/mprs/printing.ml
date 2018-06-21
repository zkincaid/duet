open Printf;;
open Tropical_defs;;

let loopFromMToN m n ?(increment=1) init f = 
    let test = if (increment > 0) then (fun i -> i > n) else (fun i -> i < n) in
    let rec loopFromMToNAux i x =
        if (test i) then x else
        loopFromMToNAux (i + increment) (f i x) in
    loopFromMToNAux m init
;;

(* ------------------------------------------------------------------------- *)

let fwt_sprintf fwt = sprintf "%.1f" (Mpq.to_float fwt);;

let wt_sprintf wt = 
    match wt with | Inf -> (sprintf "NA") | Fin fwt -> fwt_sprintf fwt
;;

let wt_print wt = print_string (wt_sprintf wt);;

(* ----------------------------------------------------------------------- *)

let rec implodeAux stringList sep = 
    match stringList with | [] -> "" | s :: rest ->
        (sep ^ s ^ (implodeAux rest sep))
;;

let implode stringList sep = 
    match stringList with 
    | [] -> ""
    | s :: rest -> s ^ (implodeAux rest sep)
;;

let stringifySubscript =  function
    | SAdd (s,i) -> sprintf "^[%s+%d]" s i
    | SSVar s -> sprintf "^[%s]" s
;;

let rec stringifyExpr = function
    | Product el -> sprintf "Product(%s)" (stringifyExprList el)
    | Sum el -> sprintf "Sum(%s)" (stringifyExprList el)
    | Max el -> sprintf "Max(%s)" (stringifyExprList el)
    | Min el -> sprintf "Min(%s)" (stringifyExprList el)
    | Base_case (s,i) -> sprintf "Base_case(%s)^[%d]" s i
    | Output_variable (s, ss) -> sprintf "Output_variable(%s)%s" s (stringifySubscript ss)
    | Input_variable s -> sprintf "Input_variable(%s)" s
    | Rational r -> sprintf "%.3f" (Mpq.to_float r)

and stringifyExprList el = implode (List.map stringifyExpr el) ","
;; 

let stringifyInequation = function
    | Equals (e1,e2) -> sprintf "%s == %s" (stringifyExpr e1) (stringifyExpr e2)
    | LessEq (e1,e2) -> sprintf "%s <= %s" (stringifyExpr e1) (stringifyExpr e2)
    | GreaterEq (e1,e2) -> sprintf "%s >= %s" (stringifyExpr e1) (stringifyExpr e2)
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

let printMatrixAndVector matrix vector =
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
        (printf " ]    \t[ ");
        (wt_print vector.(iRow));
        (printf " ]\n");
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

(*
let printBound ?(variableNames=alphabet) slopes intercepts =
    let globalPrefix = "    " in
    let getVarName i =
        if (i < Array.length variableNames) then variableNames.(i)
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
        let header = (sprintf "%s%s[K] %s " globalPrefix (getVarName uVar) Dir.bound_symbol) in
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
            else (printf "%s(%s" Dir.best_noun str;
                  List.iter (fun str -> printf ",\n%s%s" prefix str) tail;
                  printf ")\n"))
;;
*)


