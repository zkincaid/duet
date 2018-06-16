(* Run tests of Max-Plus recurrences *)

open Mprs;;
open Printf;;

(* ----------------------------------------------------------------------- *)

let fwt_from_int i = 
    let retval = Mpq.init () in 
    let _ = Mpq.set_si retval i 1 in
    retval;;

type mpMatrixTest = {
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

(* ----------------------------------------------------------------------- *)

let maxPlusDoAllTests () =
    (printf "BEGIN MAX-PLUS TESTS:\n\n");
    List.iter (fun test ->
        printf "**** TEST %s****\n" test.name; maxPlusMatrixTest test.matrix; printf "\n") 
        tests;;

let minPlusDoAllTests () =
    (printf "BEGIN MIN-PLUS TESTS:\n\n");
    List.iter (fun test ->
        printf "**** TEST %s****\n" test.name; minPlusMatrixTest test.matrix; printf "\n") 
        tests;;

let _ = 
    maxPlusDoAllTests ();
    (printf "==========================================================\n\n");
    minPlusDoAllTests ();
    (printf "**** ALL TESTS COMPLETE\n")
;;
