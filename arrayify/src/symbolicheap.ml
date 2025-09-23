open Variable
open Srk
open SrkZ3.Solver

type int_term =
    Int of int
  | Var of var
  | Times of int * int_term
  | Add of int_term * int_term
  | Sub of int_term * int_term  | PSub of pointer_term * pointer_term
  | Offset of pointer_term
and pointer_term = Pointer of pvar | PointerSum of pointer_term * int_term
type block = Block of pointer_term | BVar of bvar

type formula =
  | True
  |  Leq of int_term * int_term
  | Eq of int_term * int_term
  | BlockEq of block * block
  | And of formula * formula
  | Or of formula * formula
  | Not of formula

module HeapElem = struct 
  type t = Array of bvar | TrueHeap 
  let hash = Hashtbl.hash
  let compare a b = if hash a < hash b then -1 else if hash a > hash b then 1 else 0
end
module Heap = Set.Make(HeapElem)
type symbolicheap = formula * Heap.t

let true_sheap = (True, Heap.singleton TrueHeap)

let rec string_of_int_term t =
  let rec aux t =
    match t with
    | Int i -> string_of_int i
    | Var v -> Variable.var_name v
    | Times (i, t) -> Printf.sprintf "%d * (%s)" i (aux t)
    | Sub (t1, t2) -> Printf.sprintf "(%s - %s)" (aux t1) (aux t2)
    | Add (t1, t2) -> Printf.sprintf "(%s + %s)" (aux t1) (aux t2)
    | PSub (p1, p2) -> Printf.sprintf "(%s - %s)" (string_of_pointer_term p1) (string_of_pointer_term p2)
    | Offset p -> Printf.sprintf "Offset(%s)" (string_of_pointer_term p)
  in
  aux t
and string_of_pointer_term p =
  match p with
  | Pointer p -> pvar_name p
  | PointerSum (p, t) -> Printf.sprintf "(%s + %s)" (string_of_pointer_term p) (string_of_int_term t)

let string_of_block b =
  match b with
  | Block p -> Printf.sprintf "Block(%s)" (string_of_pointer_term p)
  | BVar b -> Variable.bvar_name b

let rec string_of_formula f =
  match f with
  | True -> "True"
  | Leq (t1, t2) -> Printf.sprintf "(%s <= %s)" (string_of_int_term t1) (string_of_int_term t2)
  | Eq (t1, t2) -> Printf.sprintf "(%s = %s)" (string_of_int_term t1) (string_of_int_term t2)
  | BlockEq (b1, b2) -> Printf.sprintf "(%s = %s)" (string_of_block b1) (string_of_block b2)
  | And (f1, f2) -> Printf.sprintf "(%s AND %s)" (string_of_formula f1) (string_of_formula f2)
  | Or (f1, f2) -> Printf.sprintf "(%s OR %s)" (string_of_formula f1) (string_of_formula f2)
  | Not f1 -> Printf.sprintf "NOT(%s)" (string_of_formula f1)

let string_of_heap h =
  let elems = Heap.elements h in
  let elem_strings = List.map (function
    | HeapElem.Array b -> Printf.sprintf "Array(%s)" (Variable.bvar_name b)
    | HeapElem.TrueHeap -> "TrueHeap"
  ) elems in
  Printf.sprintf "{%s}" (String.concat ", " elem_strings)

let string_of_symbolicheap (f, h) =
  Printf.sprintf "Formula: %s\nHeap: %s" (string_of_formula f) (string_of_heap h)

let rec int_term_to_syntaxterm srk t = 
  match t with 
  | Int i -> Syntax.mk_int srk i
  | Var v -> Variable.var_to_svar v
  | Times (i, t) -> Syntax.mk_mul srk [(Syntax.mk_int srk i); (int_term_to_syntaxterm srk t)]
  | Add (t1, t2) -> Syntax.mk_add srk [(int_term_to_syntaxterm srk t1); (int_term_to_syntaxterm srk t2)]
  | Sub (t1, t2) -> Syntax.mk_sub srk (int_term_to_syntaxterm srk t1) (int_term_to_syntaxterm srk t2)
  | PSub (p1, p2) -> Syntax.mk_sub srk (pointer_term_to_offsetsyntaxterm srk p1) (pointer_term_to_offsetsyntaxterm srk p2)
  | Offset p -> pointer_term_to_offsetsyntaxterm srk p
and pointer_term_to_offsetsyntaxterm srk p =
  match p with 
  | Pointer p -> Variable.pvaroffset_to_svar p
  | PointerSum (p, t) -> Syntax.mk_add srk [(pointer_term_to_offsetsyntaxterm srk p); (int_term_to_syntaxterm srk t)]

  let rec pointer_term_to_blocksyntaxterm srk p =
    match p with 
    | Pointer p -> Variable.pvarblock_to_svar p
    | PointerSum (p, _) -> pointer_term_to_blocksyntaxterm srk p
  let block_to_syntaxterm srk b =
  match b with
  | Block p -> pointer_term_to_blocksyntaxterm srk p
  | BVar b -> Variable.bvar_to_svar b


  let rec formula_to_syntaxformula srk (f : formula) : 'a Syntax.formula = 
  match f with 
  | True -> Syntax.mk_true srk 
  | Leq (t1, t2) -> Syntax.mk_leq srk (int_term_to_syntaxterm srk t1) (int_term_to_syntaxterm srk t2)
  | Eq (t1, t2) -> Syntax.mk_eq srk (int_term_to_syntaxterm srk t1) (int_term_to_syntaxterm srk t2)
  | BlockEq (b1, b2) -> Syntax.mk_eq srk (block_to_syntaxterm srk b1) (block_to_syntaxterm srk b2)
  | And (f1, f2) -> Syntax.mk_and srk [formula_to_syntaxformula srk f1; formula_to_syntaxformula srk f2]
  | Or (f1, f2) -> Syntax.mk_or srk [formula_to_syntaxformula srk f1; (formula_to_syntaxformula srk f2)]
  | Not f1 -> Syntax.mk_not srk (formula_to_syntaxformula srk f1)

let empty_sheap = True, Heap.empty

let sheap_equals (f1, h1) (f2, h2) = Heap.equal h1 h2 && (f1 = f2 || (
    let srk = Global.srk in
    let solver = Global.solver in 
    let s1 = formula_to_syntaxformula srk f1 in
    let s2 = formula_to_syntaxformula srk f2 in
    reset solver; add solver [s1; Syntax.mk_not srk s2];
    let result = check solver in 
    match result with 
    | `Sat -> false
    | `Unsat -> (
      reset solver; add solver [s2; Syntax.mk_not srk s1];
      let result = check solver in 
      match result with 
      | `Sat -> false
      | `Unsat -> true
      | `Unknown -> raise (Failure "Unknown equivalence from Z3")
      )
    | `Unknown -> raise (Failure "Unknown equivalence from Z3")
))

let sheap_single_b (f, h : symbolicheap) (p : pvar) : bvar option = 
  let s = formula_to_syntaxformula Global.srk f in 
  Heap.fold (fun e acc -> 
    match e with 
    | Array b -> (
      let b_svar = Variable.bvar_to_svar b in 
      let p = Variable.pvarblock_to_svar p in 
      let eq = Syntax.mk_eq Global.srk b_svar p in
      reset Global.solver; add Global.solver [s; Syntax.mk_not Global.srk eq];
      match check Global.solver with 
      | `Sat -> acc
      | `Unsat -> Some b
      | `Unknown -> raise (Failure "Unknown equivalence from Z3")
    )
    | _ -> acc
  ) h None

let all_pvars f : pvar list = 
  let rec go f acc = 
    match f with 
    | True -> acc
    | Leq (t1, t2) -> go_term t1 (go_term t2 acc)
    | Eq (t1, t2) -> go_term t1 (go_term t2 acc)
    | BlockEq (b1, b2) -> go_block b1 (go_block b2 acc)
    | And (f1, f2) -> go f1 (go f2 acc)
    | Or (f1, f2) -> go f1 (go f2 acc)
    | Not f1 -> go f1 acc
  and go_block b acc = 
    match b with 
    | Block p -> go_pointer_term p acc
    | BVar _ -> acc
  and go_term t acc =
    match t with 
    | Int _ -> acc
    | Var _ -> acc
    | Times (_, t) -> go_term t acc
    | Add (t1, t2) -> go_term t1 (go_term t2 acc)
    | Sub (t1, t2) -> go_term t1 (go_term t2 acc)
    | PSub (p1, p2) -> go_pointer_term p1 (go_pointer_term p2 acc)
    | Offset p -> go_pointer_term p acc
  and go_pointer_term p acc =
    match p with 
    | Pointer p -> p :: acc
    | PointerSum (p, t) -> go_pointer_term p (go_term t acc)
  in 
  let with_repeats = go f [] in 
  List.fold_left (fun acc p -> if List.mem p acc then acc else p :: acc) [] with_repeats 

let pointer_equalities (f, h : symbolicheap) : (pvar * bvar) list = 
  let all_pvars = all_pvars f in
  List.fold_left (fun acc p -> match sheap_single_b (f, h) p with 
  | Some b -> (p, b) :: acc
  | None -> acc
  ) [] all_pvars

let quantify_out_var (f, h : symbolicheap) (v : var) : symbolicheap = 
  let rec quantify_out_int_term it v_name = 
    match it with 
    | Int _ -> it, false
    | Var v -> if v = v_name then Var (prime_var v), true else it, false
    | Times (i, t) -> 
      let t', b = quantify_out_int_term t v_name in 
      Times (i, t'), b
    | Add (t1, t2) ->
      let t1', b1 = quantify_out_int_term t1 v_name in 
      let t2', b2 = quantify_out_int_term t2 v_name in 
      Add (t1', t2'), b1 || b2
    | Sub (t1, t2) -> 
      let t1', b1 = quantify_out_int_term t1 v_name in
      let t2', b2 = quantify_out_int_term t2 v_name in
      Sub (t1', t2'), b1 || b2
    | PSub (p1, p2) -> 
      let p1', b1 = quantify_out_pointer_term p1 v_name in 
      let p2', b2 = quantify_out_pointer_term p2 v_name in 
      PSub (p1', p2'), b1 || b2
    | Offset p -> 
      let p', b = quantify_out_pointer_term p v_name in 
      Offset p', b
  and quantify_out_pointer_term pt v_name = 
    match pt with 
    | Pointer _ -> pt, false
    | PointerSum (p, t) -> 
      let p', b = quantify_out_pointer_term p v_name in 
      let t', b' = quantify_out_int_term t v_name in 
      PointerSum (p', t'), b || b'
    in 
  let rec quantify_out_formula f v_name = 
    match f with 
    | True -> True, false
    | Leq (t1, t2) -> 
      let t1', b1 = quantify_out_int_term t1 v_name in 
      let t2', b2 = quantify_out_int_term t2 v_name in 
      Leq (t1', t2'), b1 || b2
    | Eq (t1, t2) ->
      let t1', b1 = quantify_out_int_term t1 v_name in 
      let t2', b2 = quantify_out_int_term t2 v_name in 
      Eq (t1', t2'), b1 || b2
    | BlockEq (_, _) -> f, false
    | And (f1, f2) -> 
      let f1', b1 = quantify_out_formula f1 v_name in 
      let f2', b2 = quantify_out_formula f2 v_name in 
      And (f1', f2'), b1 || b2
    | Or (f1, f2) ->
      let f1', b1 = quantify_out_formula f1 v_name in 
      let f2', b2 = quantify_out_formula f2 v_name in 
      Or (f1', f2'), b1 || b2
    | Not f1 ->
      let f1', b1 = quantify_out_formula f1 v_name in 
      Not f1', b1
    in 
  let rec go v_name formula = 
    let f', b = quantify_out_formula formula (prime_var v_name) in 
    if b then go (prime_var v_name) f' else quantify_out_formula f' v_name
  in 
  (fst (go v f)), h

let quantify_out_pvar (f, h : symbolicheap) (p : pvar) : symbolicheap = 
  let rec quantify_out_int_term it p_name = 
    match it with 
    | Int _ -> it, false
    | Var _ -> it, false
    | Times (i, t) -> 
      let t', b = quantify_out_int_term t p_name in 
      Times (i, t'), b
    | Add (t1, t2) ->
      let t1', b1 = quantify_out_int_term t1 p_name in 
      let t2', b2 = quantify_out_int_term t2 p_name in 
      Add (t1', t2'), b1 || b2
    | Sub (t1, t2) ->
      let t1', b1 = quantify_out_int_term t1 p_name in
      let t2', b2 = quantify_out_int_term t2 p_name in
      Sub (t1', t2'), b1 || b2
    | PSub (p1, p2) -> 
      let p1', b1 = quantify_out_pointer_term p1 p_name in 
      let p2', b2 = quantify_out_pointer_term p2 p_name in 
      PSub (p1', p2'), b1 || b2
    | Offset p -> 
      let p', b = quantify_out_pointer_term p p_name in 
      Offset p', b
  and quantify_out_pointer_term pt p_name = 
    match pt with 
    | Pointer p -> if p = p_name then Pointer (prime_pvar p), true else pt, false
    | PointerSum (p, t) -> 
      let p', b = quantify_out_pointer_term p p_name in 
      let t', b' = quantify_out_int_term t p_name in 
      PointerSum (p', t'), b || b'
  in 
  let quantify_out_block b p_name = 
    match b with 
    | Block p -> 
      let p', b = quantify_out_pointer_term p p_name in 
      Block p', b
    | BVar _ -> b, false
  in
  let rec quantify_out_formula f p_name = 
    match f with 
    | True -> True, false
    | Leq (t1, t2) -> 
      let t1', b1 = quantify_out_int_term t1 p_name in 
      let t2', b2 = quantify_out_int_term t2 p_name in 
      Leq (t1', t2'), b1 || b2
    | Eq (t1, t2) ->
      let t1', b1 = quantify_out_int_term t1 p_name in 
      let t2', b2 = quantify_out_int_term t2 p_name in 
      Eq (t1', t2'), b1 || b2
    | BlockEq (bt1, bt2) -> 
      let bt1', b1 = quantify_out_block bt1 p_name in 
      let bt2', b2 = quantify_out_block bt2 p_name in 
      BlockEq (bt1', bt2'), b1 || b2
    | And (f1, f2) -> 
      let f1', b1 = quantify_out_formula f1 p_name in 
      let f2', b2 = quantify_out_formula f2 p_name in 
      And (f1', f2'), b1 || b2
    | Or (f1, f2) ->
      let f1', b1 = quantify_out_formula f1 p_name in 
      let f2', b2 = quantify_out_formula f2 p_name in 
      Or (f1', f2'), b1 || b2
    | Not f1 ->
      let f1', b1 = quantify_out_formula f1 p_name in 
      Not f1', b1
  in
  let rec go p_name formula = 
    let f', b = quantify_out_formula formula (prime_pvar p_name) in 
    if b then go (prime_pvar p_name) f' else quantify_out_formula f' p_name
  in 
  (fst (go p f)), h

let pt_eq (p1 : pointer_term) (p2 : pointer_term) : formula =
  And (Eq (Offset p1, Offset p2), BlockEq (Block p1, Block p2))