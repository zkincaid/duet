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
  module VP = struct
    module I = Pair(Putil.PInt)
    include I
    module Set = Putil.Hashed.Set.Make(I)
    module Map = Putil.Map.Make(I)
    module HT = BatHashtbl.Make(I)
  end
  module CP = struct
    include Pair(C)
    let default = (Skip, Skip)
  end
  module G = ExtGraph.Persistent.Digraph.MakeBidirectionalLabeled(VP)(CP)
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
module TW = Loop.Wto(TCfa)
module TL = Loop.SccGraph(TCfa)

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

module K = struct
  include Transition.Make(StrVar) (* Transition PKA *)
  let star x =
    logf ~level:1 "Loop summarization...";
    let tr = star x in
    let res = { tr with guard = F.nudge tr.guard } in
    logf ~level:1 "loop:%a" format res;
    Log.print_stats ();
    res
end
module T = K.T
module F = K.F
module V = K.V
module D = T.D

let eps_mach = QQ.exp (QQ.of_int 2) (-53)
let eps_0 = QQ.exp (QQ.of_int 2) (-53)

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
module AbstractDomain = struct
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
  let lower man = function
    | Some x -> x
    | None -> D.bottom man D.Env.empty
  let lift f = function
    | Some x -> Some (f x)
    | None -> None
end
module A = Fixpoint.MakeAnalysis(TCfa)(AbstractDomain)
module IA = Fixpoint.MakeAnalysis(Cfa)(AbstractDomain)


let formula_of_prop = function
  | Some prop -> F.of_abstract prop
  | None -> F.bottom

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

let float_post man cmd prop =
  let project prop = D.exists man (fun p -> V.lower p != None) prop in
  match cmd with
  | Assign (v, rhs) -> K.abstract_post man (float_weight cmd) prop
  | Assume phi -> project (F.abstract_assume man prop (float_bexp phi))
  | Skip | Assert _ | Print _ -> prop

let real_post man cmd prop =
  match cmd with
  | Assign (v, rhs) -> F.abstract_assign man prop (V.mk_var v) (real_aexp rhs)
  | Assume phi -> F.abstract_assume man prop (real_bexp phi)
  | Skip | Assert _ | Print _ -> prop

let tensor_post man (fcmd, rcmd) prop =
  let post = float_post man fcmd (real_post man rcmd prop) in
  logf ~level:3 "@\npre:@\n %a@\ncmd: %a/%a@\npost:@\n %a@\n"
    D.format prop
    C.format fcmd
    C.format rcmd
    D.format post;
  post

(* Analyze floating & real program separately; annotation for a tensor node
   (u,v) is the conjunction of the (floating) annotation at u with the (real)
   annoation at v.  *)
let analyze_sep (float,float_entry) (real,real_entry) =
  let man = Box.manager_of_box (Box.manager_alloc ()) in
  let analyze abs_post cfa entry =
    let vertex_tr v prop =
      if v = entry then Some (D.top man D.Env.empty) else prop
    in
    let tr e =
      AbstractDomain.lift (fun prop -> abs_post man (Cfa.E.label e) prop)
    in
    let result =
      IA.analyze_ldi vertex_tr ~edge_transfer:tr ~delay:3 ~max_decrease:2 cfa
    in
    IA.output result
  in
  let float_annotation = analyze float_post float float_entry in
  let real_annotation = analyze real_post real real_entry in
  logf ~level:1 "@\n";
  logf ~level:1 ~attributes:[Log.Bold] "Float invariants:";
  Cfa.iter_vertex (fun v ->
    logf ~level:1 "Float invariant for %d:@\n%a"
      v
      D.format (AbstractDomain.lower man (float_annotation v))
  ) float;
  logf ~level:1 "@\n";
  logf ~level:1 ~attributes:[Log.Bold] "Real invariants:";
  Cfa.iter_vertex (fun v ->
    logf ~level:1 "Real invariant for %d:@\n%a"
      v
      D.format (AbstractDomain.lower man (real_annotation v))
  ) real;
  logf ~level:1 "@\n";
  fun (u, v) ->
    F.conj
      (F.of_abstract (AbstractDomain.lower man (float_annotation u)))
      (F.of_abstract (AbstractDomain.lower man (real_annotation v)))

module P = Pathexp.MakeElim(TCfa)(K)

(* Aux function for Chebyshev distance: given an enumeration of terms, returns
   a pair (d, phi) consisting of a (fresh) variable d and a formula phi such
   that that the formula implies that the variable is the maximum of the
   absolute values of all the terms (so if terms is an enumeration of all
   differences "x' - x", then the variable is constrained to by the chebyshev
   distance. *)
let chebyshev terms =
  let d = V.mk_tmp "dist" TyReal in
  let terms = BatEnum.append terms (BatEnum.map T.neg (BatEnum.clone terms)) in
  let ub = F.big_conj (BatEnum.map (F.geq (T.var d)) (BatEnum.clone terms)) in
  let eq = F.big_disj (BatEnum.map (F.eq (T.var d)) terms) in
  (d, F.conj ub eq)

let absolute_value term =
  let abs = V.mk_tmp "abs" TyReal in
  let at = T.var abs in
  (abs,
   F.disj
     (F.conj (F.leq (T.neg term) at) (F.leq at term)) (* term >= 0 *)
     (F.conj (F.leq term at) (F.leq at (T.neg at)))) (* term <= 0 *)

(* Aux function for Manhattan distance (see chebyshev) *)
let manhattan terms =
  let d = V.mk_tmp "dist" TyReal in
  let (abs_vars, abs_cons) =
    BatEnum.uncombine (BatEnum.map absolute_value terms)
  in
  let abs_terms = BatEnum.map T.var abs_vars in
  (d, F.conj (F.big_conj abs_cons) (F.eq (T.var d) (T.sum abs_terms)))

let forall p phi = F.negate (F.exists p (F.negate phi))

let greedy vars float_tr real_tr real_tr_other =
  let open K in
  let open BatPervasives in

  let get_transform v tr =
    try M.find v tr.transform
    with Not_found -> T.var (V.mk_var v)
  in

  (* Distance between the post-state of float_tr and real_tr *)
  let (dist, dist_cons) =
    let terms =
      let diff v =
	T.sub (get_transform v float_tr) (get_transform (primify v) real_tr)
      in
      BatEnum.map diff (BatList.enum vars)
    in
    chebyshev terms
  in

  (* Distance between the post-state of float_tr and real_tr_other *)
  let (other_dist, other_dist_cons) =
    let terms =
      let diff v =
	T.sub
	  (get_transform v float_tr)
	  (get_transform (primify v) real_tr_other)
      in
      BatEnum.map diff (BatList.enum vars)
    in
    let (other_dist, other_cons) = chebyshev terms in
    let guard =
      F.qe_lme
	(fun v -> V.equal other_dist v || V.lower v != None)
	(F.conj other_cons (F.conj float_tr.guard real_tr_other.guard))
    in
    (other_dist, guard)
  in

  (* real_tr minimizes post-state distance *)
  let dist_guard =
    let phi =
      F.disj
	(F.negate other_dist_cons)
	(F.leq (T.sub (T.var dist) (T.var other_dist)) (T.const eps_0))
    in
    forall (not % (V.equal other_dist)) phi
  in

  let guard =
    F.conj
      dist_guard
      (F.conj (F.conj float_tr.guard real_tr.guard) dist_cons);
  in
  let add_transform v t tr = M.add v t tr in
  { guard = guard;
    transform = M.fold add_transform float_tr.transform real_tr.transform }


let iter_analyze_nonstuttering vars float real tensor entry =
  let annotation = analyze_sep float real in
  let analyze man vertex_tr =
    let tr e = function
      | Some prop ->
	let real_vertex = snd (TCfa.E.src e) in
	let real_other =
	  let f e tr = K.add (real_weight (Cfa.E.label e)) tr in
	  Cfa.fold_succ_e f (fst real) real_vertex K.zero
	in
	let (flbl, rlbl) = TCfa.E.label e in
	let tr =
	  greedy vars (float_weight flbl) (real_weight rlbl) real_other
	in
	let post = K.abstract_post man tr prop in
	logf "@\npre:@\n %a@\ncmd: %a/%a@\ntr:@\n %a@\npost:@\n %a@\n"
	  D.format prop
	  C.format flbl
	  C.format rlbl
	  K.format tr
	  D.format post;
	Some post
      | None -> None
    in
    A.analyze_ldi vertex_tr ~edge_transfer:tr ~delay:3 ~max_decrease:0 tensor
  in
  let man = Polka.manager_of_polka (Polka.manager_alloc_loose ()) in
  let result =
    let vtr v prop =
      if v = entry then Some (D.top man D.Env.empty) else begin
	match prop with
	| None -> None
	| Some prop ->
	  logf "At: %a@\nprop: %a"
	    TCfa.VP.format v
	    F.format (annotation v);
	  Some (F.abstract_assume man prop (annotation v))
      end
    in
    analyze man vtr
  in
  let print (u, v) =
    let prop = AbstractDomain.lower man (A.output result (u, v)) in
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
      print_bounds vars (F.subst sigma phi)
    end
  in
  Format.printf "Error bounds (iterative analysis, nonstuttering):@\n";
  TCfa.iter_vertex print tensor;
  Format.printf "==================================@\n";
  result

let analyze_nonstuttering vars float real tensor entry =
  let annotation = analyze_sep float real in
  let weight e =
    let open K in
    let inv = F.nudge (annotation (TCfa.E.src e)) in
    let real_vertex = snd (TCfa.E.src e) in
    let real_other =
      let f e tr = K.add (real_weight (Cfa.E.label e)) tr in
      Cfa.fold_succ_e f (fst real) real_vertex K.zero
    in
    let (flbl, rlbl) = TCfa.E.label e in
    let tr =
      greedy vars (float_weight flbl) (real_weight rlbl) real_other
    in
    { tr with guard = F.conj inv tr.guard }
  in
  let pathexp = P.single_src tensor weight entry in
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
  Format.printf "Error bounds (path expression analysis, nonstuttering):@\n";
  TCfa.iter_vertex print tensor;
  Format.printf "========================================@\n"

(*********** Main function ****************
*******************************************)
let read_and_process infile =
   let lexbuf  = Lexing.from_channel infile in
   let Prog prog = Parser.main Lexer.token lexbuf in
   let (cfa, e, _) = build_cfa prog in
   let real_cfa = primify_cfa cfa in
   let tensor = TCfa.tensor (cfa, e) (real_cfa, e) in
   (* forget stuttering for now ... *)

(*
   let tensor =
     let f (u, v) g =
       if u != v then TCfa.remove_vertex g (u, v) else g
     in
     TCfa.fold_vertex f tensor tensor
   in
   *)

   Format.printf "Program size: %d nodes, %d edges@\n"
     (Cfa.nb_vertex cfa)
     (Cfa.nb_edges cfa);
   Format.printf "Tensor size: %d nodes, %d edges@\n"
     (TCfa.nb_vertex tensor)
     (TCfa.nb_edges tensor);
(*
   TCfa.display tensor;
   TL.display_scc (TL.construct tensor) TCfa.VP.show;
*)
   logf ~level:1 "Iteration order:@\n%a"
     (Loop.format_wto TCfa.VP.format) (TW.create tensor);
   Format.printf "Loop headers: %a@\n"
     Show.format<TCfa.VP.t list>
     (BatList.of_enum (TL.enum_headers (TL.construct tensor)));

   ignore (analyze_nonstuttering
	     (collect_vars prog)
	     (cfa,e)
	     (real_cfa,e)
	     tensor
	     (e,e))

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
    Log.set_verbosity_level "errgen" 2;
    ArkPervasives.opt_default_accuracy := 10;
    NumDomain.opt_max_coeff_size := None;
    K.opt_higher_recurrence := false;
    K.opt_disjunctive_recurrence_eq := false;
    K.opt_polyrec := false;
    K.opt_recurrence_ineq := true;
    K.opt_unroll_loop := false;
    K.opt_loop_guard := Some guard_ex;
    try
      read_and_process infile
    with Apron.Manager.Error exc ->
      Log.errorf "Error: %a" Apron.Manager.print_exclog exc;
    close_in infile;
    Log.print_stats ()
