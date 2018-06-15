(* Run tests of Max-Plus recurrences *)

open Mprs;;
open Printf;;

(* ----------------------------------------------------------------------- *)

let _ = 
    Mprs.MaxPlus.doAllTests ();
    (printf "==========================================================\n\n");
    Mprs.MinPlus.doAllTests ();
    (printf "**** ALL TESTS COMPLETE\n")
;;
