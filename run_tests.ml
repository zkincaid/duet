(* Run tests of Max-Plus recurrences *)

open Mprs;;
open Printf;;
open Printing;;

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
        printf "**** TEST %s****\n" test.name; maxPlusMatrixTest test.matrix; printf "\n") 
        matrixTests;
    (printf "BEGIN MAX-PLUS VECTOR TESTS:\n\n");
    List.iter (fun (test:mpMatrixVectorTest) ->
        printf "**** TEST %s****\n" test.name; maxPlusMatrixVectorTest test.matrix test.vector; printf "\n") 
        matrixVectorTests
;;

let minPlusDoAllTests () =
    (printf "BEGIN MIN-PLUS TESTS:\n\n");
    List.iter (fun (test:mpMatrixTest) ->
        printf "**** TEST %s****\n" test.name; minPlusMatrixTest test.matrix; printf "\n") 
        matrixTests;
    (printf "BEGIN MIN-PLUS VECTOR TESTS:\n\n");
    List.iter (fun (test:mpMatrixVectorTest) ->
        printf "**** TEST %s****\n" test.name; minPlusMatrixVectorTest test.matrix test.vector; printf "\n") 
        matrixVectorTests
;;

let _ = 
    maxPlusDoAllTests ();
    (printf "==========================================================\n\n");
    minPlusDoAllTests ();
    (printf "**** ALL TESTS COMPLETE\n")
;;
