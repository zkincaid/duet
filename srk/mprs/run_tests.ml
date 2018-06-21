(* Run tests of Max-Plus recurrences *)

open Mprs;;
open Printf;;
open Printing;;

(* ----------------------------------------------------------------------- *)

(* Used for testing only: *)
let dualizeMatrix matrix = 
    let nVars = Array.length matrix in
    let dual = Array.make_matrix nVars nVars Inf in
    loopFromMToN 0 (nVars - 1) () (fun uVar _ ->
        loopFromMToN 0 (nVars - 1) () (fun vVar _ ->
            let wt = matrix.(uVar).(vVar) in
            match wt with | Inf -> () | Fin fwt ->
            dual.(uVar).(vVar) <- (Fin (Tropical_defs.fwt_neg fwt))));
    dual;;

(* Used for testing only: *)
let dualizeVector vector =
    let nVars = Array.length vector in
    let dual = Array.make nVars Inf in
    loopFromMToN 0 (nVars - 1) () (fun uVar _ ->
        let wt = vector.(uVar) in
        match wt with | Inf -> () | Fin fwt ->
        dual.(uVar) <- Fin (Tropical_defs.fwt_neg fwt));
    dual;;

(* ----------------------------------------------------------------------- *)

type mpMatrixTest = {
    name : string;
    matrix : weight array array;
};;

type mpMatrixVectorTest = {
    name : string;
    matrix : weight array array;
    vector : weight array;
};;

let na = Inf;;
let d fwt = Fin (Tropical_defs.fwt_from_int fwt);;
let matrixTests = [

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

let matrixVectorTests = [

    {name="vector-zigzag-2b"; matrix=[| 
     [| na;    na;    na;    (d 7)  |];
     [| (d 0); na;    na;    na     |];
     [| na;    (d 0); na;    na     |];
     [| na;    na;    (d 1); na     |];
    |]; vector = [|
       (d 1);
       na;
       (d 50);
       na;
    |] };

    {name="vector-zigzag-4"; matrix=[| 
     [| na;    (d (-1)); |];
     [| (d 1); na;       |];
    |]; vector = [|
       (d 0);
       (d 10);
    |] };

    {name="vector-knee-1"; matrix=[| 
     [| (d 0);     na;    na    |];
     [| (d (-14)); (d 3); na    |];
     [| na;        (d 0); (d 1) |];
    |]; vector = [|
       (d 1);
       (d (-10));
       (d 5);
    |] };

];;

(* ----------------------------------------------------------------------- *)

let maxPlusDoAllTests () =
    (printf "BEGIN MAX-PLUS TESTS:\n\n");
    List.iter (fun (test:mpMatrixTest) ->
        printf "**** TEST %s****\n" test.name; 
        let _ = maxPlusMatrixTest test.matrix in 
        printf "\n") 
        matrixTests;
    (printf "BEGIN MAX-PLUS VECTOR TESTS:\n\n");
    List.iter (fun (test:mpMatrixVectorTest) ->
        printf "**** TEST %s****\n" test.name; 
        let _ = maxPlusMatrixVectorTest test.matrix test.vector in 
        printf "\n") 
        matrixVectorTests
;;

let minPlusDoAllTests () =
    (printf "BEGIN MIN-PLUS TESTS:\n\n");
    List.iter (fun (test:mpMatrixTest) ->
        printf "**** TEST %s****\n" test.name; 
        let (minS,minI) = minPlusMatrixTest test.matrix in 
        printf "\n";
        let (maxS,maxI) = maxPlusSolveForBoundingMatricesFromMatrix (dualizeMatrix test.matrix) in
        if (minS <> (dualizeMatrix maxS) || minI <> (dualizeMatrix maxI)) then
            failwith "DUALIZATION ERRROR!\n"
        else printf "Dualization check passed!\n\n") 
        matrixTests;
    (printf "BEGIN MIN-PLUS VECTOR TESTS:\n\n");
    List.iter (fun (test:mpMatrixVectorTest) ->
        printf "**** TEST %s****\n" test.name; 
        let ((minSm,minSv),(minIm,minIv)) = minPlusMatrixVectorTest test.matrix test.vector in
        printf "\n";
        let ((maxSm,maxSv),(maxIm,maxIv)) = maxPlusSolveForBoundingMatricesFromMatrixAndVector 
            (dualizeMatrix test.matrix) (dualizeVector test.vector) in
        if (minSm <> (dualizeMatrix maxSm) || minIm <> (dualizeMatrix maxIm) ||
            minSv <> (dualizeVector maxSv) || minIv <> (dualizeVector maxIv)) then
            failwith "DUALIZATION ERRROR!\n"
        else printf "Dualization check passed!\n\n")
        matrixVectorTests
;;

let _ = 
    maxPlusDoAllTests ();
    (printf "==========================================================\n\n");
    minPlusDoAllTests ();
    (printf "**** ALL TESTS COMPLETE\n")
;;
