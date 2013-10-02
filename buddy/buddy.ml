(**************************************************************************)
(*  Copyright (C) 2008 Akihiko Tozawa and Masami Hagiya.                  *)
(*  Copyright (C) 2009 2010 Pietro Abate <pietro.abate@pps.jussieu.fr     *)
(*                                                                        *)
(*  This library is free software: you can redistribute it and/or modify  *)
(*  it under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 3 of the    *)
(*  License, or (at your option) any later version.  A special linking    *)
(*  exception to the GNU Lesser General Public License applies to this    *)
(*  library, see the COPYING file for more information.                   *)
(**************************************************************************)

type bdd
type bddpair
type var = int

type value = False | True | Unknown
type solution = SAT | UNSAT | UNKNOWN

exception IOError
exception EmptyList
let _ = 
  Callback.register_exception "buddy_exn_IOError" IOError;
  Callback.register_exception "buddy_exn_EmptyList" EmptyList;
;;

(* from bdd.h *)

let _BDDOP_AND = 0
let _BDDOP_XOR = 1
let _BDDOP_OR =  2
let _BDDOP_NAND = 3
let _BDDOP_NOR = 4
let _BDDOP_IMP = 5
let _BDDOP_BIIMP = 6
let _BDDOP_DIFF = 7
let _BDDOP_LESS = 8
let _BDDOP_INVIMP = 9

let _BDD_REORDER_NONE = 0
let _BDD_REORDER_WIN2  =  1
let _BDD_REORDER_WIN2ITE = 2
let _BDD_REORDER_SIFT = 3
let _BDD_REORDER_SIFTITE = 4
let _BDD_REORDER_WIN3 = 5
let _BDD_REORDER_WIN3ITE = 6
let _BDD_REORDER_RANDOM = 7

let _BDD_REORDER_FREE = 0
let _BDD_REORDER_FIXED = 1

(* external functions *)

external bdd_compare : bdd -> bdd -> int = "wrapper_bdd_compare"
external bdd_init : int -> int -> unit = "wrapper_bdd_init"
external bdd_done : unit -> unit = "wrapper_bdd_done"

external bdd_setvarnum : int -> unit = "wrapper_bdd_setvarnum"

external bdd_varnum : unit -> int = "wrapper_bdd_varnum"

external bdd_ithvar : int -> bdd = "wrapper_bdd_ithvar"

external bdd_nithvar : int -> bdd = "wrapper_bdd_nithvar"

external bdd_true : unit -> bdd = "wrapper_bdd_true"
external bdd_false : unit -> bdd = "wrapper_bdd_false"
external bdd_not : bdd -> bdd = "wrapper_bdd_not"
external bdd_and : bdd -> bdd -> bdd = "wrapper_bdd_and"
external bdd_or : bdd -> bdd -> bdd = "wrapper_bdd_or"

external bdd_xor : bdd -> bdd -> bdd = "wrapper_bdd_xor"
external bdd_imp : bdd -> bdd -> bdd = "wrapper_bdd_imp"
external bdd_biimp : bdd -> bdd -> bdd = "wrapper_bdd_biimp"
external bdd_ite : bdd -> bdd -> bdd -> bdd = "wrapper_bdd_ite"
external bdd_apply : bdd -> bdd -> int -> bdd = "wrapper_bdd_apply"

external bdd_exist : bdd -> bdd -> bdd = "wrapper_bdd_exist"
external bdd_forall : bdd -> bdd -> bdd = "wrapper_bdd_forall"

external bdd_appex : bdd -> bdd -> int -> bdd -> bdd = "wrapper_bdd_appex"
external bdd_appall : bdd -> bdd -> int -> bdd -> bdd = "wrapper_bdd_appall"

external bdd_satone : bdd -> bdd = "wrapper_bdd_satone"
external bdd_satoneset : bdd -> bdd -> bdd -> bdd = "wrapper_bdd_satone"

external bdd_allsat : bdd -> unit = "wrapper_bdd_allsat"
(* external bdd_allsat : bdd -> ((var * value) list -> unit) -> unit = "wrapper_bdd_allsat" *)
external bdd_satcount : bdd -> int = "wrapper_bdd_satcount"
external bdd_satcountln : bdd -> float = "wrapper_bdd_satcountln"
external bdd_makeset : var list -> bdd = "wrapper_bdd_makeset"

external bdd_restrict : bdd -> bdd -> bdd = "wrapper_bdd_restrict"
external bdd_simplify : bdd -> bdd -> bdd = "wrapper_bdd_restrict"
external bdd_var : bdd -> int = "wrapper_bdd_var"
external bdd_high : bdd -> bdd = "wrapper_bdd_high"
external bdd_low : bdd -> bdd = "wrapper_bdd_low"
external bdd_support : bdd -> bdd = "wrapper_bdd_support"
external bdd_nodecount : bdd -> int = "wrapper_bdd_nodecount"
external bdd_newpair : unit -> bddpair = "wrapper_bdd_newpair"
external bdd_setpair : bddpair -> int -> int -> int = "wrapper_bdd_setpair"
external bdd_replace : bdd -> bddpair -> bdd = "wrapper_bdd_replace"

external bdd_varblockall : unit -> unit = "wrapper_bdd_varblockall"
external bdd_addvarblock : bdd -> int -> int = "wrapper_bdd_addvarblock"
external bdd_intaddvarblock : int -> int -> int -> int = "wrapper_bdd_intaddvarblock"
external bdd_setvarorder : int list -> unit = "wrapper_bdd_setvarorder"
external bdd_getvarorder : unit -> int list = "wrapper_bdd_getvarorder"
external bdd_reorder : int -> int = "wrapper_bdd_reorder"
external bdd_autoreorder : int -> int = "wrapper_bdd_autoreorder"
external bdd_enable_reorder : unit -> unit = "wrapper_bdd_enable_reorder"
external bdd_disable_reorder : unit -> unit = "wrapper_bdd_disable_reorder"
external bdd_reorder_verbose : int -> int = "wrapper_bdd_reorder_verbose"
external bdd_level2var : int -> int = "wrapper_bdd_level2var"
external bdd_var2level : int -> int = "wrapper_bdd_var2level"

external bdd_setmaxincrease : int -> int = "wrapper_bdd_setmaxincrease"
external bdd_setminfreenodes : int -> int = "wrapper_bdd_setminfreenodes"
(*external bdd_setallocnum : int -> int = "wrapper_bdd_setallocnum"*)
(*external bdd_setincreasefactor : float -> float = "wrapper_bdd_setincreasefactor"*)
external bdd_setcacheratio : int -> int = "wrapper_bdd_setcacheratio"
external bdd_isrunning : unit -> bool = "wrapper_bdd_isrunning"

external bdd_fprintorder : out_channel -> unit = "wrapper_bdd_fprintorder"
external bdd_fprinttable : out_channel -> bdd -> unit = "wrapper_bdd_fprinttable"
external bdd_fprintdot : out_channel -> bdd -> unit = "wrapper_bdd_fprintdot"
external bdd_fprintset : out_channel -> bdd -> unit = "wrapper_bdd_fprintset"

external bdd_save : out_channel -> bdd -> unit = "wrapper_bdd_save"
external bdd_load : in_channel -> bdd = "wrapper_bdd_load"

external bdd_bigapply : bdd list -> int -> bdd = "wrapper_bdd_bigapply"

let bdd_bigand bdd = bdd_bigapply bdd _BDDOP_AND
let bdd_bigor bdd = bdd_bigapply bdd _BDDOP_OR

(* create a conjunction of positive variables *)

external bdd_createset : (int -> bool) -> bdd = "wrapper_bdd_createset"


(* fdd stuff *)
external fdd_extdomain : int -> int = "wrapper_fdd_extdomain"
external fdd_overlapdomain : int -> int -> int = "wrapper_fdd_overlapdomain"
external fdd_clearall : unit -> unit = "wrapper_fdd_clearall"
external fdd_domainnum : unit -> int = "wrapper_fdd_domainnum"
external fdd_domainsize : int -> int = "wrapper_fdd_domainsize"
external fdd_varnum : int -> int = "wrapper_fdd_varnum"
external fdd_vars : int -> int array = "wrapper_fdd_vars"
external fdd_ithvar : int -> int -> bdd = "wrapper_fdd_ithvar"
external fdd_ithset : int -> bdd = "wrapper_fdd_ithset"
external fdd_domain : int -> bdd = "wrapper_fdd_domain"
external fdd_equals : int -> int -> bdd = "wrapper_fdd_equals"
external fdd_intaddvarblock : int -> int -> int -> int = "wrapper_fdd_intaddvarblock"
external fdd_setpair : bddpair -> int -> int -> int = "wrapper_fdd_setpair"
external fdd_allsat : bdd -> (int list) -> unit = "wrapper_fdd_allsat"

external fdd_printset : bdd -> unit = "wrapper_fdd_printset"

let varcount = ref 0
let bdd_newvar () = 
  let v = 
    if bdd_varnum() <= !varcount then 
      (bdd_setvarnum (!varcount + 1); !varcount)
    else !varcount
  in
  incr varcount; v
;;

let bdd_init ?(nodenum=1000) ?(cachesize=100) () = 
  bdd_init nodenum cachesize;
  ignore(bdd_reorder_verbose(0))
;;

let bdd_done () =
  varcount := 0;
  bdd_done ()
;;

type reorder_strategy = Win2 | Win2ite | Win3 | Win3ite | Sift | Siftite | Random
let int_of_strategy = function
  |Win2ite -> _BDD_REORDER_WIN2ITE
  |Win2 -> _BDD_REORDER_WIN2
  |Win3 -> _BDD_REORDER_WIN3
  |Win3ite -> _BDD_REORDER_WIN3ITE
  |Sift -> _BDD_REORDER_SIFT
  |Siftite -> _BDD_REORDER_SIFTITE
  |Random -> _BDD_REORDER_RANDOM

let bdd_autoreorder ?(strategy=Win2ite) () =
  let str = int_of_strategy(strategy) in
  ignore(bdd_autoreorder str)

let bdd_reorder ?(strategy=Win2ite) () =
  let str = int_of_strategy(strategy) in
  ignore(bdd_reorder str)

let bdd_setvarorder l =
  if List.length l = bdd_varnum() then
    bdd_setvarorder l
  else
    let nl = ref (List.rev l) in
    for i = 0 to bdd_varnum() - 1 do
      if List.mem i l then ()
      else nl := i::!nl
    done;
    bdd_setvarorder (List.rev !nl)
;;

let value_of_var = function
  |  0 -> False
  |  1 -> True
  | -1 -> Unknown
  | _ -> assert false

let string_of_value = function
  |True -> "true"
  |False -> "false"
  |Unknown -> "unknown"

let bdd_true = bdd_true ()
let bdd_false = bdd_false ()
let bdd_pos var = if bdd_varnum() <= var then assert false else bdd_ithvar(var);;
let bdd_neg var = if bdd_varnum() <= var then assert false else bdd_nithvar(var);;

let bdd_relprod q =
  let qbdd = ref bdd_true and n = ref 0 in 
  fun a b -> 
    if !n != bdd_varnum () then qbdd := bdd_createset q else ();
    bdd_appex a b _BDDOP_AND !qbdd
;;

let bdd_satoneset ?(pol=true) bdd vars =
  let p = if pol then bdd_true else bdd_false in
  bdd_satoneset bdd (bdd_makeset vars) p
;;

let bdd_allsat f bdd =
  Callback.register "__allsat_handler" f;
  bdd_allsat bdd
;;

let fdd_allsat f bdd vars =
  let shift0 = List.map (fun x -> x lsl 1) in
  let shift1 = List.map (fun x -> (x lsl 1) + 1) in
  let to_int_list xs =
    List.fold_right
      (fun n ints ->
	 if n == 0 then shift0 ints
	 else if n == 1 then shift1 ints
	 else (shift0 ints) @ (shift1 ints))
      xs
      [0]
  in
  let rec iter_choices sofar = function
    | [] -> f sofar
    | (x::xs) -> List.iter (fun y -> iter_choices (y::sofar) xs) x
  in
  let g xs =
    iter_choices [] (List.map to_int_list xs)
  in
  Callback.register "__fdd_allsat_handler" g;
  fdd_allsat bdd (List.rev vars)
;;

exception EmptyBdd

(* iterate through a certain set satisfying d *)

let rec bdd_setfold f d t = 
  if d = bdd_false then raise EmptyBdd
  else if d = bdd_true then t 
  else 
    let e = bdd_low d in 
    if e <> bdd_false then bdd_setfold f e t 
    else bdd_setfold f (bdd_high d) (f (bdd_var d) t)

let bdd_diff a b = bdd_apply a b _BDDOP_DIFF

let bdd_or x y =
  if x = bdd_false then y
  else (if y = bdd_false then x
	else (bdd_or x y ))
