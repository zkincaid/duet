(* Run tests of Max-Plus recurrences *)

open Mprs;;
open Printf;;

(* ----------------------------------------------------------------------- *)

let _ = 
    maxPlusTests ();
    (printf "==========================================================\n\n");
    minPlusTests ();
    (printf "**** ALL TESTS COMPLETE\n")
;;
