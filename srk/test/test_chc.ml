open Srk
open OUnit
open Syntax
open Test_pervasives
open Chc
open Iteration

let pd = (module QLIALift(Product(LinearRecurrenceInequation)(PolyhedronGuard)) :
  PreDomain)
(*
let typ_symbol_fo srk sym =
  match typ_symbol srk sym with
  | `TyInt -> `TyInt
  | `TyReal -> `TyReal
  | `TyBool -> `TyBool
  | _ -> assert false

let mk_rel_atom_fresh srk fp ?(name="R") syms =
  let typs = List.map (typ_symbol_fo srk) syms in
  let rel = mk_relation fp ~name typs in
  mk_rel_atom srk fp rel syms

let mk_n_rel_atoms_fresh srk fp ?(name="R") syms n = 
  BatArray.init n (fun _ -> mk_rel_atom_fresh srk fp ~name syms)*)

let countup1 () =
  let r1 = mk_symbol srk ~name:"R1" (`TyFun ([`TyInt], `TyBool)) in
  let r2 = mk_symbol srk ~name:"R2" (`TyFun ([`TyInt], `TyBool)) in
  let error = mk_symbol srk ~name:"Error" `TyBool in
 
  let fp = Fp.empty in
  let prop1 = Proposition.mk_proposition srk r1 ["x"] in
  let prop2 = Proposition.mk_proposition srk r2 ["x'"] in
  let errorprop = Proposition.mk_proposition srk error [] in
  let fp =
    let open Infix in
    Fp.add_rule fp prop2 [prop1] (var 0 `TyInt = var 1 `TyInt + (int 1)) |> 
    fun fp -> Fp.add_rule fp prop1 [prop2] (var 0 `TyInt = var 1 `TyInt + (int 1)) |>
    fun fp -> Fp.add_rule fp prop1 [] ((int 0) <= var 0 `TyInt) |>
    fun fp -> Fp.add_rule fp errorprop [prop2] (var 0 `TyInt <= (int 0)) |>
    fun fp -> Fp.add_query fp error
  in
  let res = Fp.check srk fp pd in
  assert (res = `No)

let countup2 () =
  let r1 = mk_symbol srk ~name:"R1" (`TyFun ([`TyInt], `TyBool)) in
  let r2 = mk_symbol srk ~name:"R2" (`TyFun ([`TyInt], `TyBool)) in
  let error = mk_symbol srk ~name:"Error" `TyBool in
 
  let fp = Fp.empty in
  let prop1 = Proposition.mk_proposition srk r1 ["x"] in
  let prop2 = Proposition.mk_proposition srk r2 ["x'"] in
  let errorprop = Proposition.mk_proposition srk error [] in
  let fp =
    let open Infix in
    Fp.add_rule fp prop2 [prop1] (var 0 `TyInt = var 1 `TyInt + (int 1)) |> 
    fun fp -> Fp.add_rule fp prop1 [prop2] (var 0 `TyInt = var 1 `TyInt + (int 1)) |>
    fun fp -> Fp.add_rule fp prop1 [] ((int 0) <= var 0 `TyInt) |>
    fun fp -> Fp.add_rule fp errorprop [prop2] ((int 0) <= var 0 `TyInt) |>
    fun fp -> Fp.add_query fp error
  in
  let res = Fp.check srk fp pd in
  assert (res = `Unknown)

(* x only goes up on some iteration; y goes up on all; verify that if
 * initially x = y then cannot end with y < x *)
let xskipcount () =
  let r1 = mk_symbol srk ~name:"R1" (`TyFun ([`TyInt; `TyInt], `TyBool)) in
  let r2 = mk_symbol srk ~name:"R2" (`TyFun ([`TyInt; `TyInt], `TyBool)) in
  let r3 = mk_symbol srk ~name:"R2" (`TyFun ([`TyInt; `TyInt], `TyBool)) in

  let fp = Fp.empty in
  let prop1 = Proposition.mk_proposition srk r1 ["x"; "y"] in
  let prop2 = Proposition.mk_proposition srk r2 ["x'"; "y'"] in
  let prop3 = Proposition.mk_proposition srk r3 ["x''"; "y''"] in
  let fp =
    let open Infix in
    Fp.add_rule fp prop1 [] (var 0 `TyInt = var 1 `TyInt) |>
    fun fp -> Fp.add_rule fp prop2 [prop1] (var 0 `TyInt = var 2 `TyInt + (int 1) && var 1 `TyInt = var 3 `TyInt) |>
    fun fp -> Fp.add_rule fp prop2 [prop1] (var 0 `TyInt = var 2 `TyInt && var 1 `TyInt = var 3 `TyInt) |>
    fun fp -> Fp.add_rule fp prop1 [prop2] (var 0 `TyInt = var 2 `TyInt && var 1 `TyInt = var 3 `TyInt + (int 1)) |> 
    fun fp -> Fp.add_rule fp prop3 [prop1] (var 1 `TyInt < var 0 `TyInt && var 0 `TyInt = var 2 `TyInt && var 1 `TyInt = var 3 `TyInt) |>
    fun fp -> Fp.add_query fp r3
  in
  let res = Fp.solve srk fp pd in
  let phi = mk_exists srk `TyInt (mk_exists srk `TyInt (res (int_of_symbol r3))) in
  assert_equiv_formula phi (mk_false srk)

let countupsuplin () =
  let r1 = mk_symbol srk ~name:"R1" (`TyFun ([`TyInt], `TyBool)) in
  let r2 = mk_symbol srk ~name:"R2" (`TyFun ([`TyInt], `TyBool)) in
  let r3 = mk_symbol srk ~name:"R3" (`TyFun ([`TyInt], `TyBool)) in
  let error = mk_symbol srk ~name:"Error" `TyBool in
 
  let fp = Fp.empty in
  let prop1 = Proposition.mk_proposition srk r1 ["x"] in
  let prop2 = Proposition.mk_proposition srk r2 ["y'"] in
  let prop3 = Proposition.mk_proposition srk r3 ["z''"] in
  let errorprop = Proposition.mk_proposition srk error [] in
  let fp =
    let open Infix in
    Fp.add_rule fp prop3 [] (mk_true srk) |>
    fun fp -> Fp.add_rule fp prop2 [prop1; prop3] (var 0 `TyInt = var 1 `TyInt + (int 1)) |> 
    fun fp -> Fp.add_rule fp prop1 [prop2] (var 0 `TyInt = var 1 `TyInt + (int 1)) |>
    fun fp -> Fp.add_rule fp prop1 [] ((int 0) <= var 0 `TyInt) |>
    fun fp -> Fp.add_rule fp errorprop [prop2] (var 0 `TyInt <= (int 0)) |>
    fun fp -> Fp.add_query fp error
  in
  let res = Fp.check srk fp pd in
  assert (res = `No)

let failure_suplin () =
  let r1 = mk_symbol srk ~name:"R1" (`TyFun ([`TyInt], `TyBool)) in
  let r2 = mk_symbol srk ~name:"R2" (`TyFun ([`TyInt], `TyBool)) in
  let r3 = mk_symbol srk ~name:"R3" (`TyFun ([`TyInt], `TyBool)) in
  let error = mk_symbol srk ~name:"Error" `TyBool in
 
  let fp = Fp.empty in
  let prop1 = Proposition.mk_proposition srk r1 ["x"] in
  let prop2 = Proposition.mk_proposition srk r2 ["y'"] in
  let prop3 = Proposition.mk_proposition srk r3 ["z''"] in
  let errorprop = Proposition.mk_proposition srk error [] in
  let fp =
    let open Infix in
    Fp.add_rule fp prop3 [] (mk_true srk) |>
    fun fp -> Fp.add_rule fp prop2 [prop1; prop3] (var 0 `TyInt = var 1 `TyInt + (int 1)) |> 
    fun fp -> Fp.add_rule fp prop1 [prop2] (var 0 `TyInt = var 1 `TyInt + (int 1)) |>
    fun fp -> Fp.add_rule fp prop1 [] ((int 0) <= var 0 `TyInt) |>
    fun fp -> Fp.add_rule fp errorprop [prop2] (var 0 `TyInt <= (int 0)) |>
    fun fp -> Fp.add_rule fp prop3 [prop1] (mk_true srk) |>
    fun fp -> Fp.add_query fp error
  in
  let res = Fp.check srk fp pd in
  assert (res = `No)


let test_init () =
  let fp = Chc.ChcSrkZ3.parse_file srk "/Users/jakesilverman/Documents/arraycopy2.smt2" in
  Log.errorf "Fp is \n%a\n\n\n\n" (Chc.Fp.pp srk) fp;
  assert false
  
  let suite = "Chc" >:::
  [
    (*"test_init" >:: test_init;*)
    "countup1" >:: countup1;
    "counterup2" >:: countup2;
    "xskipcount" >:: xskipcount;
    "countupsuplin" >:: countupsuplin;
    "failure_suplin" >:: (fun _ -> 
        assert_raises 
          (Failure "No methods for solving non super linear chc systems") 
          failure_suplin);
  ]
