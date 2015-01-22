open Ast
open Apak
open Ark
open ArkPervasives
open BatPervasives

include Log.Make(struct let name = "errgen" end)

let eps_mach = QQ.exp (QQ.of_int 2) (-53)
let eps_0 = QQ.exp (QQ.of_int 2) (-53)

let approxify = primify
let idealify x = x

module Var = struct
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
  include Transition.Make(Var) (* Transition PKA *)

  let absolute_value term =
    let abs = V.mk_tmp "abs" TyReal in
    let at = T.var abs in
    (abs,
     F.conj
       (F.conj (F.leq term at) (F.leq (T.neg term) at))
       (F.disj (F.eq term at) (F.eq (T.neg term) at)))

  let default = one

  let modified_floats tr =
    let is_primed v = v.[String.length v - 1] = ''' in
    VarSet.filter (fun v -> not (is_primed v)) (modifies tr)

  let simplify tr =
    let vars =
      VarSet.elements (formula_free_program_vars tr.guard)
    in
    let postify v =
      try M.find v tr.transform
      with Not_found -> T.var (V.mk_var v)
    in
    let post_diff = (* difference between pre-state and post-state vars *)
      List.map (fun (v, rhs) ->
	T.sub rhs (T.var (V.mk_var v))
      ) (BatList.of_enum (M.enum tr.transform))
    in
    let templates =
      (List.map (fun v -> T.var (V.mk_var v)) vars)
      @ (BatList.of_enum (M.values tr.transform))
      @ post_diff
    in
    let box = F.boxify templates tr.guard in

    (* difference beween float & real vars *)
    let approx_diff x =
      let mk_var v = T.var (V.mk_var v) in
      let pre_diff = T.sub (mk_var (idealify x)) (mk_var (approxify x)) in
      let post_diff = T.sub (postify (idealify x)) (postify (approxify x)) in
      let mk_box phi =
	F.conj
	  phi
	  (F.boxify
	     [pre_diff; post_diff; T.sub post_diff pre_diff]
	     (F.conj phi tr.guard))
      in
      let positive = F.geq pre_diff T.zero in
      let increasing = F.leq pre_diff post_diff in
      let negative = F.negate positive in
      let decreasing = F.negate increasing in
      F.big_disj (BatList.enum [
	mk_box (F.conj positive increasing);
	mk_box (F.conj positive decreasing);
	mk_box (F.conj negative increasing);
	mk_box (F.conj negative decreasing);
      ])
    in
    let approx_diff_guard =
      F.big_conj
	(BatEnum.map approx_diff (VarSet.enum (modified_floats tr)))
    in
    { tr with guard = F.nudge (F.conj box approx_diff_guard) }

  let star tr =
    let mk_nondet v _ =
      T.var (V.mk_tmp ("nondet_" ^ (Var.show v)) (Var.typ v))
    in
    let loop_counter = T.var (V.mk_real_tmp "K") in
    let loop =
      { transform = M.mapi mk_nondet tr.transform;
	guard = F.leqz (T.neg loop_counter) }
    in
    let postify v =
      try M.find v loop.transform
      with Not_found -> T.var (V.mk_var v)
    in
    let loop_body =
      let add_eq v rhs phi = F.conj (F.eq (postify v) rhs) phi in
      F.linearize
	(fun () -> V.mk_real_tmp "nonlin")
	(M.fold add_eq tr.transform tr.guard)
    in
    let with_bound f = function
      | Some x -> f x
      | None -> F.top
    in
    let recurrence_ineq diff_term ivl =
      let lower =
	with_bound
	  (fun lo -> F.leq (T.mul loop_counter (T.const lo)) diff_term)
	  (Interval.lower ivl)
      in
      let upper =
	with_bound
	  (fun hi -> F.leq diff_term (T.mul loop_counter (T.const hi)))
	  (Interval.upper ivl)
      in
      F.conj lower upper
    in

    let loop =
      let terms =
	M.fold
	  (fun v t ts -> (T.sub t (T.var (V.mk_var v)))::ts)
	  loop.transform
	  []
      in
      let recur =
	let bounds = F.optimize terms loop_body in
	F.big_conj (BatList.enum (List.map2 recurrence_ineq terms bounds))
      in
      { loop with guard = F.conj loop.guard recur }
    in

    let mk_box t ivl =
      let lo =
	with_bound (fun lo -> F.leq (T.const lo) t) (Interval.lower ivl)
      in
      let hi =
	with_bound (fun hi -> F.leq t (T.const hi)) (Interval.upper ivl)
      in
      F.conj lo hi
    in

    let attractor x =
      let pre_diff =
	T.sub (T.var (V.mk_var (idealify x))) (T.var (V.mk_var (approxify x)))
      in
      let post_diff =
	T.sub (postify (idealify x)) (postify (approxify x))
      in
      let positive = F.geq pre_diff T.zero in
      let increasing = F.leq pre_diff post_diff in
      let negative = F.negate positive in
      let decreasing = F.negate increasing in

      let mk_case phi =
	let diff = T.sub post_diff pre_diff in
	match F.optimize [diff; post_diff] phi with
	| [recur; box] ->
	  F.conj (recurrence_ineq diff recur) (mk_box post_diff box)
	| _ -> assert false
      in

      logf ~level:1 "formula: %a" F.format loop_body;
      logf ~level:1 "stable: %a" F.format
			 (F.disj
			    (F.conj positive increasing)
			    (F.conj negative decreasing));

      let stable_bounds =
	let bounds =
	  F.optimize
	    [post_diff]
	    (F.conj loop_body (F.disj (F.conj positive increasing)
				 (F.conj negative decreasing)))
	in
	match bounds with
	| [box] -> mk_box post_diff box
	| _ -> assert false
      in
      let pd_bounds =
	mk_case
	  (F.conj
	     (F.conj (F.negate stable_bounds) loop_body)
	     (F.conj positive decreasing))
      in
      let ni_bounds =
	mk_case
	  (F.conj
	     (F.conj (F.negate stable_bounds) loop_body)
	     (F.conj negative increasing))
      in
      logf ~level:1 "pd_bounds: %a" F.format pd_bounds;
      logf ~level:1 "ni_bounds: %a" F.format ni_bounds;
      logf ~level:1 "stable_bounds: %a" F.format stable_bounds;
      F.disj stable_bounds (F.disj pd_bounds ni_bounds)
    in
    let plus_guard =
      let vars = VarSet.elements (formula_free_program_vars loop_body) in
      let templates =
	(List.map (fun v -> T.var (V.mk_var v)) vars)
	@ (BatList.of_enum (M.values loop.transform))
      in
      let attractors =
	F.big_conj (BatEnum.map attractor (VarSet.enum (modified_floats tr)))
      in
      F.conj (F.boxify templates loop_body) attractors
    in
    let zero_guard =
      let eq (v, t) = F.eq (T.var (V.mk_var v)) t in
      F.conj
	(F.eqz loop_counter)
	(F.big_conj (BatEnum.map eq (M.enum loop.transform)))
    in
    let star_guard = F.disj plus_guard zero_guard in
    let loop = { loop with guard = F.conj loop.guard star_guard } in
    logf ~level:1 "loop summary:@\n%a" format loop;
    loop

end
module T = K.T
module F = K.F
module V = K.V
module D = T.D

let linearize = F.linearize (fun () -> V.mk_real_tmp "nonlin")

let not_tmp v = V.lower v != None

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

module Cfa = struct
  module G = ExtGraph.Persistent.Digraph.MakeBidirectionalLabeled(Putil.PInt)(K)
  include G
  include ExtGraph.Display.MakeLabeled(G)(Putil.PInt)(K)
  let collect_vars cfa =
    edges_e cfa /@ (K.modifies % E.label)
    |> BatEnum.reduce K.VarSet.union
    |> K.VarSet.elements
end

module Slice = ExtGraph.Slice.Make(Cfa)
module VSet = Putil.PInt.Set
module L = Loop.SccGraph(Cfa)
module Top = Graph.Topological.Make(Cfa)

let add_edge g v u k =
  if Cfa.mem_edge g v u then begin
    let e = Cfa.find_edge g v u in
    let g = Cfa.remove_edge_e g e in
    Cfa.add_edge_e g (Cfa.E.create v (K.add (Cfa.E.label e) k) u)
  end else Cfa.add_edge_e g (Cfa.E.create v k u)

let add_edge_e g e =
  add_edge g (Cfa.E.src e) (Cfa.E.dst e) (Cfa.E.label e)

let elim v g =
  assert (Cfa.mem_vertex g v);
  assert (not (Cfa.mem_edge g v v));
  let f se h =
    let v_to_se = Cfa.E.label se in
    let add pe h =
      let weight = K.mul (Cfa.E.label pe) v_to_se in
      add_edge h (Cfa.E.src pe) (Cfa.E.dst se) weight
    in
    Cfa.fold_pred_e add g v h
  in
  Cfa.fold_succ_e f g v (Cfa.remove_vertex g v)


let reduce_cfa cfa entry exit =
  let scc = L.construct cfa in
  let is_header = L.is_header scc in
  let is_cp v = is_header v || v = entry || v = exit in
  let cp = BatList.of_enum (BatEnum.filter is_cp (Cfa.vertices cfa)) in
  logf ~level:1 "Entry: %d" entry;
  logf ~level:1 "Exit: %d" exit;
  logf ~level:1 "Cutpoints: %a" Show.format<int list> cp;
  let dag =
    let f g v =
      Cfa.fold_succ_e (fun e g -> Cfa.remove_edge_e g e) cfa v g
    in
    List.fold_left f cfa cp
  in
  let add_succs cpg u =
    assert (Cfa.mem_vertex dag u);
    let graph =
      Cfa.fold_succ_e (fun e g -> add_edge_e g e) cfa u dag
    in
    assert (Cfa.mem_vertex graph u);
    let graph =
      Top.fold (fun v g ->
	if is_cp v then g else elim v g
      ) graph graph
    in
    assert (Cfa.mem_vertex graph u);
    Cfa.fold_succ_e (fun e cpg -> add_edge_e cpg e) graph u cpg
  in
  List.fold_left add_succs Cfa.empty cp

let build_cfa s weight =
  let fresh =
    let m = ref (-1) in
    fun () -> (incr m; !m)
  in
  let add_edge cfa u lbl v =
    add_edge_e cfa (Cfa.E.create u (weight lbl) v)
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

let float_weight = function
  | Assign (v, rhs) ->
    let (rhs, rhs_err) = float_aexp rhs in
    { K.assign v rhs with K.guard = rhs_err }
  | Assume phi -> K.assume (float_bexp phi)
  | Skip -> K.one
  | Assert _ | Print _ -> K.one

let real_weight = function
  | Assign (v, rhs) -> K.assign v (real_aexp rhs)
  | Assume phi -> K.assume (real_bexp phi)
  | Skip -> K.one
  | Assert _ | Print _ -> K.one

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
module A = Fixpoint.MakeAnalysis(Cfa)(AbstractDomain)

(* Analyze floating & real program separately; annotation for a tensor node
   (u,v) is the conjunction of the (floating) annotation at u with the (real)
   annoation at v.  *)
let analyze_sep (approx,approx_entry) (ideal,ideal_entry) =
  let man = Box.manager_of_box (Box.manager_alloc ()) in
  let analyze cfa entry =
    let vertex_tr v prop =
      if v = entry then Some (D.top man D.Env.empty) else prop
    in
    let tr e =
      AbstractDomain.lift (fun prop -> K.abstract_post man (Cfa.E.label e) prop)
    in
    let result =
      A.analyze_ldi vertex_tr ~edge_transfer:tr ~delay:3 ~max_decrease:2 cfa
    in
    A.output result
  in
  let approx_annotation = analyze approx approx_entry in
  let ideal_annotation = analyze ideal ideal_entry in
  logf ~level:1 "@\n";
  logf ~level:1 ~attributes:[Log.Bold] "Approx invariants:";
  Cfa.iter_vertex (fun v ->
    logf ~level:1 "Approx invariant for %d:@\n%a"
      v
      D.format (AbstractDomain.lower man (approx_annotation v))
  ) approx;
  logf ~level:1 "@\n";
  logf ~level:1 ~attributes:[Log.Bold] "Ideal invariants:";
  Cfa.iter_vertex (fun v ->
    logf ~level:1 "Ideal invariant for %d:@\n%a"
      v
      D.format (AbstractDomain.lower man (ideal_annotation v))
  ) ideal;
  logf ~level:1 "@\n";
  fun (u, v) ->
    F.conj
      (F.of_abstract (AbstractDomain.lower man (approx_annotation u)))
      (F.of_abstract (AbstractDomain.lower man (ideal_annotation v)))

let add_stuttering cfa =
  (* For each edge u --k--> v such that u has a self loop u --k'--> u, add
     relabel the u->v edge u --(k + k'k)--> v. *)
  let g e cfa =
    let u = Cfa.E.src e in
    let v = Cfa.E.dst e in
    if Cfa.mem_edge cfa u u then
      let k = Cfa.E.label e in
      let k' = Cfa.E.label (Cfa.find_edge cfa u u) in
      add_edge cfa u v (K.mul (K.add k' (K.mul k' k')) k)
    else cfa
  in
  let stutter v cfa = add_edge cfa v v K.one in
  Cfa.fold_vertex stutter cfa
    (Cfa.fold_edges_e g cfa cfa)

(******************************************************************************)
(* Tensor *)

module TCfa = struct
  module VP = struct
    module I = struct
      type t = int * int deriving (Compare, Show)
      let compare = Compare_t.compare
      let show = Show_t.show
      let format = Show_t.format
      let equal x y = compare x y = 0
      let hash = Hashtbl.hash
    end
    include I
    module Set = Putil.Hashed.Set.Make(I)
    module Map = Putil.Map.Make(I)
    module HT = BatHashtbl.Make(I)
  end
  module G = ExtGraph.Persistent.Digraph.MakeBidirectionalLabeled(VP)(K)
  module D = ExtGraph.Display.MakeSimple(G)(VP)
  include G
  include D
end
module TW = Loop.Wto(TCfa)
module TL = Loop.SccGraph(TCfa)

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

(* Aux function for Manhattan distance (see chebyshev) *)
let manhattan terms =
  let d = V.mk_tmp "dist" TyReal in
  let (abs_vars, abs_cons) =
    BatEnum.uncombine (BatEnum.map K.absolute_value terms)
  in
  let abs_terms = BatEnum.map T.var abs_vars in
  (d, F.conj (F.big_conj abs_cons) (F.eq (T.var d) (T.sum abs_terms)))

let forall p phi = F.negate (F.exists p (F.negate phi))

let greedy annotation vars approx_tr ideal_tr ideal_succs =
  let open K in
  let open BatPervasives in

  let get_transform v tr =
    try M.find v tr.transform
    with Not_found -> T.var (V.mk_var v)
  in

  (* Distance between the post-state of approx_tr and ideal_tr *)
  let (dist, dist_cons) =
    let terms =
      let diff v =
	T.sub
	  (get_transform (idealify v) ideal_tr)
	  (get_transform (approxify v) approx_tr)
      in
      BatEnum.map diff (BatList.enum vars)
    in
    chebyshev terms
  in

  (* Distance between the post-state of approx_tr and ideal_succs *)
  let (other_dist, other_dist_cons) =
    let terms =
      let diff v =
	T.sub
	  (get_transform (idealify v) ideal_succs)
	  (get_transform (approxify v) approx_tr)
      in
      BatEnum.map diff (BatList.enum vars)
    in
    let (other_dist, other_cons) = chebyshev terms in
    let guard =
      F.qe_lme
	(fun v -> V.equal other_dist v || not_tmp v)
	(F.big_conj (BatList.enum [
	  other_cons;
	  approx_tr.guard;
	  ideal_succs.guard;
	  annotation;
	]))
    in
    (other_dist, guard)
  in

  (* ideal_tr minimizes post-state distance *)
  let dist_guard =
    let phi =
      F.disj
	(F.negate other_dist_cons)
	(F.leq (T.sub (T.var dist) (T.var other_dist)) (T.const eps_0))
    in
    let lin_phi =
      linearize (F.conj annotation phi)
    in
    forall (not % (V.equal other_dist)) lin_phi
  in
  let guard =
    F.big_conj (BatList.enum [
      dist_guard;
      approx_tr.guard;
      ideal_tr.guard;
      dist_cons;
      annotation
    ])
  in
  let add_transform v t tr = M.add v t tr in
  let res =
  { guard = guard;
    transform = M.fold add_transform approx_tr.transform ideal_tr.transform }
  in
  let res = K.simplify res in
  logf "@\nGreedy transition:@\n%a@\n@\n" K.format res;
  res

(* Maps a vertex v to a transition which approximates the transition relation
   starting at v (and going anywhere) *)
let tr_succs cfa =
  let f e tr = K.add (Cfa.E.label e) tr in
  Memo.memo (fun v -> Cfa.fold_succ_e f cfa v K.zero)

type ctx =
  { annotation : int * int -> F.t;
    tr_succs : int -> K.t;
    vars : string list;
    approx_cfa : Cfa.t;
    ideal_cfa : Cfa.t }

let tensor_edge ctx e1 e2 =
  let open K in
  let src = (Cfa.E.src e1, Cfa.E.src e2) in
  let dst = (Cfa.E.dst e1, Cfa.E.dst e2) in
  let succs = ctx.tr_succs (Cfa.E.src e2) in
  let tr =
    greedy (ctx.annotation src) ctx.vars (Cfa.E.label e1) (Cfa.E.label e2) succs
  in
  TCfa.E.create src tr dst

let sync ctx (g, g_entry) (h, h_entry) =
  let add_edge g_edge tensor =
    let f h_edge tensor =
      if Cfa.E.dst g_edge = Cfa.E.dst h_edge then
	TCfa.add_edge_e tensor (tensor_edge ctx g_edge h_edge)
      else
	tensor
    in
    Cfa.fold_succ_e f h (Cfa.E.src g_edge) tensor
  in
  Cfa.fold_edges_e add_edge g TCfa.empty

let rec expand ctx (u, v) pathexp (g, changed) =
  logf ~attributes:[Log.Green] "Expanding (%d, %d)" u v;
  let sigma v = match K.V.lower v with
    | None -> T.var v
    | Some v ->
      try K.M.find v pathexp.K.transform
      with Not_found -> T.var (V.mk_var v)
  in
  let tensor_guard =
    let guards =
      BatEnum.map (fun e ->
	(TCfa.E.label e).K.guard
      ) (TCfa.enum_succ_e g (u, v))
    in
    F.qe_lme not_tmp (F.big_disj guards)
  in
  let tensor_guard_assert =
    F.negate (F.subst sigma tensor_guard)
  in
  let phi = F.conj (K.to_formula pathexp) tensor_guard_assert in
  let edges =
    BatEnum.map
      (uncurry (tensor_edge ctx))
      (Putil.cartesian_product
	 (Cfa.enum_succ_e ctx.approx_cfa u)
	 (Cfa.enum_succ_e ctx.ideal_cfa v))
  in
  let f (graph, phi, changed) e =
    let weight = TCfa.E.label e in
    let guard = F.subst sigma weight.K.guard in
    if F.is_sat (F.conj phi guard) then begin
      let dst = TCfa.E.dst e in
      let psi = F.conj phi (F.negate (F.qe_lme not_tmp guard)) in
      logf ~level:1 ~attributes:[Log.Green] "  Added an edge: %a -> %a"
	TCfa.VP.format (u, v)
	TCfa.VP.format dst;

(*
      let s = new Smt.solver in
      s#assrt (F.to_smt (F.conj phi guard));
      ignore (s#check ());
      let m = s#get_model () in
      Format.printf "tensor guard: %a@\n" Show.format<F.t option> (F.select_disjunct (fun v -> m#eval_qq (T.V.to_smt v)) tensor_guard_assert);
      Format.printf "tr: %a@\n" K.M.format pathexp.K.transform;
      Format.printf "%s@\n" (m#to_string ());
      assert false
      *)

      if TCfa.mem_vertex graph dst then
	(TCfa.add_edge_e graph e, psi, true)
      else
	(fst (expand ctx dst (K.mul pathexp weight)
		(TCfa.add_edge_e graph e, false)),
	 psi,
	 true)
    end else
      (graph, phi, changed)
  in
  let (g, _, changed) = (BatEnum.fold f (g, phi, changed) edges) in
  (g, changed)

let print_bounds vars pathexp =
  let post v =
    try K.M.find v pathexp.K.transform
    with Not_found -> T.var (V.mk_var v)
  in
  let f v = T.sub (post (idealify v)) (post (approxify v)) in
  let g v bounds =
    let bound_str =
      match Interval.lower bounds, Interval.upper bounds with
      | (Some x, Some y) ->
	string_of_float (Mpqf.to_float (QQ.max (Mpqf.abs x) (Mpqf.abs y)))
      | (_, _) -> "oo"
    in
    Format.printf "  | %s - %s' | <= %s@\n" v v bound_str
  in
  List.iter2 g vars (F.optimize (List.map f vars) pathexp.K.guard)

let analyze ctx tensor entry =
  let rec fix tensor =
    logf ~level:1 ~attributes:[Log.Bold] "Computing path expressions...";
    let pathexp = P.single_src tensor TCfa.E.label entry in
    let check (u, v) (g, changed) =
      let pathexp = pathexp (u, v) in
      expand ctx (u,v) pathexp (g, changed)
(*
      (g, changed)
*)
    in
    let (tensor, changed) =
      TCfa.fold_vertex check tensor (tensor, false)
    in
    if changed then fix tensor else (pathexp, tensor)
  in
  let (pathexp, tensor) = fix tensor in
  let print (u,v) =
    let pathexp = pathexp (u,v) in
    let vars =
      let f v = v.[String.length v - 1] != ''' in
      List.filter f (K.VarSet.elements (K.modifies pathexp))
    in
    if F.is_sat pathexp.K.guard then begin
      Format.printf "At (%d, %d):@\n" u v;
      print_bounds vars pathexp
    end else Format.printf "At (%d, %d): unreachable@\n" u v;
  in
  Format.printf "Error bounds (path expression analysis):@\n";
  TCfa.iter_vertex print tensor;
  Format.printf "========================================@\n"

let guard_ex p phi =
  let vars =
    K.VarSet.elements (K.formula_free_program_vars phi)
  in
  let vars =
    List.filter (fun v -> p (V.mk_var v)) vars
  in
  let templates =
    let is_primed v =
      v.[String.length v - 1] = '''
      || (v.[String.length v - 1] = '^' && v.[String.length v - 2] = ''')
    in
    let unprimed =
      List.filter (fun v -> not (is_primed v)) vars
    in
    let primify v =
      if v.[String.length v - 1] = '^'
      then (String.sub v 0 (String.length v - 1)) ^ "'^"
      else v ^ "'"
    in
    (List.map (fun v -> T.var (V.mk_var v)) vars)
    @ (List.map
	 (fun v -> T.sub (T.var (V.mk_var v)) (T.var (V.mk_var (primify v))))
	 unprimed)
  in
  F.boxify templates phi

let usage_msg = "Usage: approx [OPTIONS] <ideal> <approx>\n"
              ^ "       approx [OPTIONS] -float <file>"

let ideal = ref None
let approx = ref None


let parse_file filename weight =
  let infile = Pervasives.open_in filename in
  let lexbuf = Lexing.from_channel infile in
  let Prog prog = Parser.main Lexer.token lexbuf in
  Pervasives.close_in infile;
  build_cfa prog weight

let anon_fun s =
  match !ideal, !approx with
  | None, _ -> ideal := Some (parse_file s real_weight)
  | Some _, None -> approx := Some (parse_file s (real_weight % primify_cmd))
  | _, _ -> failwith "Too many input files"

let float_arg =
  let set_float s =
    if !ideal == None && !approx == None then begin
      ideal := Some (parse_file s real_weight);
      approx := Some (parse_file s (float_weight % primify_cmd))
    end else
      failwith "Too many input files"
  in
  ("-float",
   Arg.String set_float,
   " Set approximate program to be floating point implementation")

let verbose_arg =
  ("-verbose",
   Arg.String (fun v -> Log.set_verbosity_level v Log.info),
   " Raise verbosity for a particular module")

let verbose_list_arg =
  ("-verbose-list",
   Arg.Unit (fun () ->
     print_endline "Available modules for setting verbosity:";
     Hashtbl.iter (fun k _ ->
       print_endline (" - " ^ k);
     ) Log.loggers;
     exit 0;
   ),
   " List modules which can be used with -verbose")

let spec_list = [
    float_arg;
    verbose_arg;
    verbose_list_arg
  ]

let _ =
  Arg.parse (Arg.align spec_list) anon_fun usage_msg;
  match !ideal, !approx with
  | Some (ideal_cfa, ideal_entry, ideal_exit),
    Some (approx_cfa, approx_entry, approx_exit) ->
     begin
       let ideal_cfa = reduce_cfa ideal_cfa ideal_entry ideal_exit in
       let approx_cfa = reduce_cfa approx_cfa approx_entry approx_exit in
       let annotation =
	 analyze_sep (approx_cfa,approx_entry) (ideal_cfa,ideal_entry)
       in
       let ideal_cfa = add_stuttering ideal_cfa in
       let ctx =
	 { annotation = annotation;
	   tr_succs = tr_succs ideal_cfa;
	   vars = Cfa.collect_vars ideal_cfa;
	   approx_cfa = approx_cfa;
	   ideal_cfa = ideal_cfa }
       in
       logf ~level:1 "Vars: %a" Show.format<string list> ctx.vars;
       let entry = (approx_entry, ideal_entry) in
       let tensor =
	 sync ctx (approx_cfa,approx_entry) (ideal_cfa,ideal_entry)
       in
       analyze ctx tensor entry
     end
  | _, _ -> print_endline usage_msg
