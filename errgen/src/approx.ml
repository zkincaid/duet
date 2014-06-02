(*pp camlp4find deriving.syntax *)

open Ast
open Apak
open Ark
open ArkPervasives

include Log.Make(struct let name = "errgen" end)

module C = struct
  type t = cmd_type deriving (Show,Compare)
  let compare = Compare_t.compare
  let show = Show_t.show
  let format = Show_t.format
  let default = Skip
end
module Cfa = struct
  include ExtGraph.Persistent.Digraph.MakeBidirectionalLabeled(Putil.PInt)(C)
end
module CfaDisplay = ExtGraph.Display.MakeLabeled(Cfa)(Putil.PInt)(C)

let build_cfa s =
  let fresh =
    let m = ref (-1) in
    fun () -> (incr m; !m)
  in
  let add_edge cfa u lbl v =
    Cfa.add_edge_e cfa (Cfa.E.create u lbl v)
  in
  let rec go cfa entry = function
    | Cmd Skip -> (cfa, entry)
    | Cmd c ->
      let succ = fresh () in
      (add_edge cfa entry c succ, succ)
    | Seq (c, d) ->
      let (cfa, exit) = go cfa entry c in
      go cfa exit d
    | Ite (phi, c, d) ->
      let succ, enter_then, enter_else = fresh (), fresh (), fresh () in
      let cfa = add_edge cfa entry (Assume phi) enter_then in
      let cfa = add_edge cfa entry (Assume (Not_exp phi)) enter_else in
      let (cfa, exit_then) = go cfa enter_then c in
      let (cfa, exit_else) = go cfa enter_else d in
      (Cfa.add_edge (Cfa.add_edge cfa exit_then succ) exit_else succ, succ)
    | While (phi, body, _) ->
      let (cfa, enter_body) = go cfa entry (Cmd (Assume phi)) in
      let (cfa, exit_body) = go cfa enter_body body in
      let cfa = Cfa.add_edge cfa exit_body entry in
      go cfa entry (Cmd (Assume (Not_exp phi)))
  in
  let entry = fresh () in
  let (cfa, exit) = go (Cfa.add_vertex Cfa.empty entry) entry s in
  (cfa, entry, exit)

let primify_cfa g =
  let f e g =
    Cfa.add_edge_e
      g
      (Cfa.E.create (Cfa.E.src e) (primify_cmd (Cfa.E.label e)) (Cfa.E.dst e))
  in
  Cfa.fold_edges_e f g Cfa.empty

module Pair(M : Putil.Ordered) = struct
  type t = M.t * M.t deriving (Show)
  module Compare_t = struct
    type a = t
    let compare (a,b) (c,d) = match M.compare a c with
      | 0 -> M.compare b d
      | c -> c
  end
  let compare = Compare_t.compare
  let show = Show_t.show
  let format = Show_t.format
  let equal x y = compare x y = 0
  let hash = Hashtbl.hash
end

(* Tensor product *)
module TCfa = struct
  module VP = Pair(Putil.PInt)
  module CP = Pair(C)
  module G = ExtGraph.Persistent.Digraph.MakeBidirectionalLabeled
    (struct
      include VP
      module Set = Putil.Hashed.Set.Make(VP)
      module Map = Putil.Map.Make(VP)
      module HT = BatHashtbl.Make(VP)
     end)
    (struct
      include CP
      let default = (Skip, Skip)
     end)
  module D = ExtGraph.Display.MakeLabeled(G)(VP)(CP)
  include G
  include D
  let tensor (g,g_entry) (h, h_entry) =
    let add_vertex v (worklist, tensor) =
      if mem_vertex tensor v then (worklist, tensor)
      else (v::worklist, add_vertex tensor v)
    in
    let add_succ u (worklist, tensor) (e,f) =
      let v = Cfa.E.dst e, Cfa.E.dst f in
      let lbl = Cfa.E.label e, Cfa.E.label f in
      let (worklist, tensor) = add_vertex v (worklist, tensor) in
      (worklist, add_edge_e tensor (E.create u lbl v))
    in
    let rec fix (worklist, tensor) =
      match worklist with
      | [] -> tensor
      | ((u,v)::worklist) ->
	fix (BatEnum.fold
	       (add_succ (u,v))
	       (worklist, tensor)
	       (Putil.cartesian_product
		  (Cfa.enum_succ_e g u)
		  (Cfa.enum_succ_e h v)))
    in
    let entry = (g_entry, h_entry) in
    fix ([entry], G.add_vertex empty entry)
end

module StrVar = struct
  type t = string deriving (Compare)
  include Putil.MakeFmt(struct
    type a = t
    let format formatter str = Format.pp_print_string formatter str
  end)
  let compare = Compare_t.compare
  let hash = Hashtbl.hash
  let equal x y = x = y
  let prime x = x ^ "^"
  let to_smt x = Smt.real_var x
  let of_smt sym = match Smt.symbol_refine sym with
    | Smt.Symbol_string str -> str
    | Smt.Symbol_int _ -> assert false
  let typ _ = TyReal
  module E = Enumeration.Make(Putil.PString)
  let enum = E.empty ()
  let tag = E.to_int enum
end

module K = Transition.Make(StrVar) (* Transition PKA *)
module T = K.T
module F = K.F
module V = K.V
module D = T.D

let eps_mach = QQ.exp (QQ.of_int 2) (-53)

let rec real_aexp = function
  | Real_const k -> T.const k
  | Sum_exp (s, t) -> T.add (real_aexp s) (real_aexp t)
  | Diff_exp (s, t) -> T.sub (real_aexp s) (real_aexp t)
  | Mult_exp (s, t) -> T.mul (real_aexp s) (real_aexp t)
  | Var_exp v -> T.var (K.V.mk_var v)
  | Unneg_exp t -> T.neg (real_aexp t)
  | Havoc_aexp -> T.var (K.V.mk_tmp "havoc" TyReal)
let rec real_bexp = function
  | Bool_const true -> F.top
  | Bool_const false -> F.bottom
  | Eq_exp (s, t) -> F.eq (real_aexp s) (real_aexp t)
  | Ne_exp (s, t) -> F.negate (F.eq (real_aexp s) (real_aexp t))
  | Gt_exp (s, t) -> F.gt (real_aexp s) (real_aexp t)
  | Lt_exp (s, t) -> F.lt (real_aexp s) (real_aexp t)
  | Ge_exp (s, t) -> F.geq (real_aexp s) (real_aexp t)
  | Le_exp (s, t) -> F.leq (real_aexp s) (real_aexp t)
  | And_exp (phi, psi) -> F.conj (real_bexp phi) (real_bexp psi)
  | Or_exp (phi, psi) -> F.disj (real_bexp phi) (real_bexp psi)
  | Not_exp phi -> F.negate (real_bexp phi)
  | Havoc_bexp -> F.leqz (T.var (K.V.mk_tmp "havoc" TyReal))

let rec float_aexp = function
  | Real_const k -> (T.const (Mpqf.of_float (Mpqf.to_float k)), F.top)
  | Sum_exp (s, t) -> float_binop T.add s t
  | Diff_exp (s, t) -> float_binop T.sub s t
  | Mult_exp (s, t) -> float_binop T.mul s t
  | Var_exp v -> (T.var (K.V.mk_var v), F.top)
  | Unneg_exp t ->
    let (t, t_err) = float_aexp t in
    (T.neg t, t_err)
  | Havoc_aexp -> (T.var (K.V.mk_tmp "havoc" TyReal), F.top)
and float_binop op s t =
  let (s,s_err) = float_aexp s in
  let (t,t_err) = float_aexp t in
  let err = T.var (K.V.mk_tmp "err" TyReal) in
  let term = op s t in
  let err_magnitude = T.mul term (T.const eps_mach) in
  let err_constraint =
    F.disj
      (F.conj
	 (F.leq (T.neg err_magnitude) err)
	 (F.leq err err_magnitude))
      (F.conj
	 (F.leq (T.neg err_magnitude) err)
	 (F.leq err (T.neg err_magnitude)))
  in
  (T.add term err, F.conj err_constraint (F.conj s_err t_err))

let rec float_bexp = function
  | Bool_const true -> F.top
  | Bool_const false -> F.bottom
  | Eq_exp (s, t) -> float_bool_binop F.eq s t
  | Gt_exp (s, t) -> float_bool_binop F.gt s t
  | Lt_exp (s, t) -> float_bool_binop F.lt s t
  | Ge_exp (s, t) -> float_bool_binop F.geq s t
  | Le_exp (s, t) -> float_bool_binop F.leq s t
  | And_exp (phi, psi) -> F.conj (float_bexp phi) (float_bexp psi)
  | Or_exp (phi, psi) -> F.disj (float_bexp phi) (float_bexp psi)
  | Havoc_bexp -> F.leqz (T.var (K.V.mk_tmp "havoc" TyReal))
  | Ne_exp _ -> assert false
  | Not_exp _ -> assert false
and float_bool_binop op s t =
  let (s,s_err) = float_aexp s in
  let (t,t_err) = float_aexp t in
  F.conj (op s t) (F.conj s_err t_err)
let float_bexp bexp = float_bexp (nnf bexp)

let print_bounds vars formula =
  let f v =
    T.sub
      (T.var (V.mk_var (StrVar.prime v)))
      (T.var (V.mk_var (StrVar.prime (primify v))))
  in
  let g v bounds =
    let bound_str =
      match bounds with
      | (Some x, Some y) ->
	string_of_float (Mpqf.to_float (QQ.max (Mpqf.abs x) (Mpqf.abs y)))
      | (_, _) -> "oo"
    in
    Format.printf "  | %s - %s' | <= %s@\n" v v bound_str
  in
  List.iter2 g vars (F.optimize (List.map f vars) formula)

type magic
module A = Fixpoint.MakeAnalysis(TCfa)(struct
  type t = magic D.t option
  include Putil.MakeFmt(struct
    type a = t
    let format formatter = function
      | Some x -> D.format formatter x
      | None -> Format.pp_print_string formatter "_|_"
  end)
  let join x y = match x,y with
    | Some x, Some y -> Some (D.join x y)
    | Some x, None | None, Some x -> Some x
    | None, None -> None
  let widen x y = match x,y with
    | Some x, Some y -> Some (D.widen x y)
    | Some x, None | None, Some x -> Some x
    | None, None -> None
  let bottom = None
  let equal x y = match x,y with
    | Some x, Some y -> D.equal x y
    | None, None -> true
    | _, _ -> false
end)
let formula_of_prop = function
  | Some prop -> F.of_abstract prop
  | None -> F.bottom

let float_post man cmd prop =
  let project prop = D.exists man (fun p -> V.lower p != None) prop in
  (* Assumptions can be non-linear; Apron's linearization works better by
     iterating assumptions.  It's possible that this iteration won't terminate
     - it depends on the details of Apron's linearization. *)
  let rec assume prop phi =
    let next = F.abstract_assume man prop phi in
    if D.equal next prop then prop
    else assume next phi
  in
  match cmd with
  | Assign (v, rhs) ->
    let (rhs, rhs_err) = float_aexp rhs in
    project (F.abstract_assign man
	       (assume prop rhs_err)
	       (V.mk_var v)
	       rhs)
  | Assume phi -> project (F.abstract_assume man prop (float_bexp phi))
  | Skip | Assert _ | Print _ -> prop

let real_post man cmd prop =
  match cmd with
  | Assign (v, rhs) -> F.abstract_assign man prop (V.mk_var v) (real_aexp rhs)
  | Assume phi -> F.abstract_assume man prop (real_bexp phi)
  | Skip | Assert _ | Print _ -> prop

let tensor_post man (fcmd, rcmd) prop =
  let post = float_post man fcmd (real_post man rcmd prop) in
  logf ~level:3 "pre:@\n %a@\ncmd: %a/%a@\npost:@\n %a"
    D.format prop
    C.format fcmd
    C.format rcmd
    D.format post;
  post



let iter_analyze tensor entry =
  let lower man = function
    | Some x -> x
    | None -> D.bottom man D.Env.empty
  in
  let analyze man vertex_tr =
    let tr e = function
      | Some prop ->
	let (flbl, rlbl) = TCfa.E.label e in
	Some (tensor_post man (flbl, rlbl) prop)
      | None -> None
    in
    A.analyze_ldi vertex_tr ~edge_transfer:tr ~delay:2 ~max_decrease:2 tensor
  in
  let box = Box.manager_of_box (Box.manager_alloc ()) in
  let box_result =
    let vtr v prop =
      if v = entry then Some (D.top box D.Env.empty) else prop
    in
    analyze box vtr
  in
  let man = Polka.manager_of_polka (Polka.manager_alloc_loose ()) in
  let result =
    let vtr v prop =
      if v = entry then Some (D.top man D.Env.empty) else begin
	match prop with
	| None -> None
	| Some prop ->
	  let box = formula_of_prop (A.output box_result v) in
	  Some (F.abstract_assume man prop box)
      end
    in
    analyze man vtr
  in
  let print (u, v) =
    let prop = lower man (A.output result (u, v)) in
    if D.is_bottom prop then Format.printf "At (%d, %d): unreachable@\n" u v
    else begin
      let sigma v = match V.lower v with
	| Some v -> T.var (V.mk_var (StrVar.prime v))
	| None -> assert false
      in
      let phi = F.of_abstract prop in
      let vars =
	let f v = v.[String.length v - 1] != ''' in
	List.filter f (K.VarSet.elements (K.formula_free_program_vars phi))
      in

      Format.printf "At (%d, %d):@\n" u v;
(*      Format.printf "%a@\n@?" D.format prop;*)
      print_bounds vars (F.subst sigma phi)
    end
  in
  Format.printf "Error bounds (iterative analysis):@\n";
  TCfa.iter_vertex print tensor;
  Format.printf "==================================@\n";
  result

let float_weight cmd =
  match cmd with
  | Assign (v, rhs) ->
    let (rhs, rhs_err) = float_aexp rhs in
    { K.assign v rhs with K.guard = rhs_err }
  | Assume phi -> K.assume (float_bexp phi)
  | Skip -> K.one
  | Assert _ | Print _ -> K.one

let real_weight cmd =
  match cmd with
  | Assign (v, rhs) -> K.assign v (real_aexp rhs)
  | Assume phi -> K.assume (real_bexp phi)
  | Skip -> K.one
  | Assert _ | Print _ -> K.one

module P = Pathexp.MakeElim(TCfa)(K)

let tensor_weight result e =
  let (flbl, rlbl) = TCfa.E.label e in
  (* real & float operate on disjoint sets of variables, so sequential
     composition is non-interfering *)
  F.opt_simplify_strategy := [F.qe_cover];
  let inv = K.assume (formula_of_prop (A.output result (TCfa.E.src e))) in
  let fweight = K.simplify (K.normalize (K.mul inv (float_weight flbl))) in
  K.mul fweight (real_weight rlbl)


let analyze tensor entry =
  let result = iter_analyze tensor entry in
  let pathexp = P.single_src tensor (tensor_weight result) entry in
  let print (u,v) =
    let pathexp = pathexp (u,v) in
    let vars =
      let f v = v.[String.length v - 1] != ''' in
      List.filter f (K.VarSet.elements (K.modifies pathexp))
    in
    let phi = K.to_formula pathexp in
    if F.is_sat phi then begin
      Format.printf "At (%d, %d):@\n" u v;
      print_bounds vars phi
    end else Format.printf "At (%d, %d): unreachable@\n" u v;
  in
  Format.printf "Error bounds (path expression analysis):@\n";
  TCfa.iter_vertex print tensor;
  Format.printf "========================================@\n"

(*********** Main function ****************
*******************************************)

let read_and_process infile =
   let lexbuf  = Lexing.from_channel infile in
   let Prog prog = Parser.main Lexer.token lexbuf in
   let (cfa, e, _) = build_cfa prog in
   let tensor = TCfa.tensor (cfa, e) (primify_cfa cfa, e) in
   (* forget stuttering for now ... *)

   let tensor =
     let f (u, v) g =
       if u != v then TCfa.remove_vertex g (u, v) else g
     in
     TCfa.fold_vertex f tensor tensor
   in

   analyze tensor (e,e)

let guard_ex =
  let man = Box.manager_alloc () in
  fun p phi -> F.of_abstract (F.abstract ~exists:(Some p) man phi)

let _ =
  if Array.length Sys.argv <> 2 then
    Format.eprintf "usage: %s input_filename\n" Sys.argv.(0)
  else
    let infile = open_in Sys.argv.(1) in
(*
    Log.set_verbosity_level "errgen" 2;
    Log.set_verbosity_level "ark.formula" 2;
    Log.set_verbosity_level "ark.transition" 2;
*)
    K.opt_higher_recurrence := false;
    K.opt_disjunctive_recurrence_eq := false;
    K.opt_polyrec := false;
    K.opt_recurrence_ineq := true;
    K.opt_unroll_loop := false;
    K.opt_loop_guard := Some guard_ex;
    read_and_process infile;
    close_in infile;
    Log.print_stats ()
