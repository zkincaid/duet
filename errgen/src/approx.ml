(*pp camlp4find deriving.syntax *)

open Ast
open Apak
open Ark
open ArkPervasives

include Log.Make(struct let name = "errgen" end)

let eps_mach = QQ.exp (QQ.of_int 2) (-53)
let eps_0 = QQ.exp (QQ.of_int 2) (-53)


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

  let recurrence_ineq_terms terms ctx =
    let post_sigma v = match V.lower v with
      | Some var ->
	(try M.find var ctx.loop.transform
	 with Not_found -> T.var v)
      | None -> assert false
    in
    let prime_sigma v = match V.lower v with
      | Some var ->
	if M.mem var ctx.loop.transform then T.var (V.mk_var (Var.prime var))
	else T.var v
      | None -> assert false
    in
    let prime_term t = T.subst prime_sigma t in
    let post_term t = T.subst post_sigma t in
    let deltas =
      let f t = T.sub (prime_term t) t in
      List.map f terms
    in
    let bounds = F.optimize deltas ctx.phi in
    let h tr (t, (lo, hi)) =
      let delta = T.sub (post_term t) t in
      let lower = match lo with
	| Some bound ->
	  F.leq (T.mul ctx.loop_counter (T.const bound)) delta
	| None -> F.top
      in
      let upper = match hi with
	| Some bound ->
	  F.leq delta (T.mul ctx.loop_counter (T.const bound))
	| None -> F.top
      in
      let lo_string = match lo with
	| Some lo -> (QQ.show lo) ^ " <= "
	| None -> ""
      in
      let hi_string = match hi with
	| Some hi -> " <= " ^ (QQ.show hi)
	| None -> ""
      in
      logf "Bounds for (%a): %s(%a)-(%a)%s"
	T.format t
	lo_string
	T.format (prime_term t)
	T.format t
	hi_string;
      { tr with guard = F.conj (F.conj lower upper) tr.guard }
    in
    let loop =
      BatEnum.fold h ctx.loop (BatEnum.combine (BatList.enum terms,
						BatList.enum bounds))
    in
    { ctx with loop = loop }

  let star tr =
    let mk_nondet v _ =
      T.var (V.mk_tmp ("nondet_" ^ (Var.show v)) (Var.typ v))
    in
    let loop_counter = T.var (V.mk_real_tmp "K") in
    let loop =
      { transform = M.mapi mk_nondet tr.transform;
	guard = F.leqz (T.neg loop_counter) }
    in
    let induction_vars =
      M.fold
	(fun v _ env -> Incr.Env.add v None env)
	tr.transform
	Incr.Env.empty
    in
    let ctx =
      { induction_vars = induction_vars;
	phi = F.linearize (fun () -> V.mk_real_tmp "nonlin") (to_formula tr);
	loop_counter = loop_counter;
	loop = loop }
    in
    let ctx = simple_induction_vars ctx in
    let context_transform ctx (do_transform, transform) =
      if do_transform then transform ctx else ctx
    in
    let ctx =
      List.fold_left context_transform ctx [
	(!opt_higher_recurrence, higher_induction_vars);
	(!opt_disjunctive_recurrence_eq, disj_induction_vars);
	(!opt_recurrence_ineq, recurrence_ineq);
	(!opt_higher_recurrence_ineq, higher_recurrence_ineq);
	(!opt_polyrec, polyrec);
      ]
    in

    (* Compute closed forms for induction variables *)
    let close v incr transform =
      match incr with
      | Some incr ->
	let t = Incr.to_term incr ctx.loop_counter in
	logf "Closed term for %a: %a"
	  Var.format v
	  T.format t;
	M.add v t transform
      | None -> transform
    in
    let transform = Incr.Env.fold close ctx.induction_vars ctx.loop.transform in
    let loop = { ctx.loop with transform = transform } in

    let ctx =
      let modified = VarSet.elements (modifies tr) in
      let is_primed v = v.[String.length v - 1] = ''' in
      let modified_floats =
	List.filter (fun v -> not (is_primed v)) modified
      in
      let diff =
	List.map (fun v ->
	  T.sub (T.var (V.mk_var v)) (T.var (V.mk_var (primify v)))
	) modified_floats
      in
      recurrence_ineq_terms
	((List.map (fun v -> T.var (V.mk_var v)) modified) @ diff)
	{ ctx with loop = loop }
    in
    let loop = ctx.loop in

    let loop =
      match !opt_loop_guard with
      | Some ex -> loop_guard ex { ctx with loop = loop }
      | None -> loop
    in
    let loop =
      if !opt_unroll_loop then add one (mul loop tr)
      else loop
    in
    logf ~level:3 "Loop summary: %a" format loop;
    loop

  let star tr =
    try
      star tr
    with
    | Unsat ->
      logf "Loop body is unsat";
      one
    | Undef ->
      let mk_nondet v _ =
	T.var (V.mk_tmp ("nondet_" ^ (Var.show v)) (Var.typ v))
      in
      Log.errorf "Gave up in loop computation";
      { guard = F.top;
	transform = M.mapi mk_nondet tr.transform }

  let split_star tr phi =
    let assume_phi = assume phi in
    let assume_not_phi = assume (F.negate phi) in

    let tr12 = mul assume_phi (mul tr assume_not_phi) in
    let tr21 = mul assume_not_phi (mul tr assume_phi) in

    logf ~attributes:[Log.Cyan] "@\nComputing loop summary assuming: %a"
      F.format phi;
    let str1 =
      Log.time "star1" star (mul assume_phi tr)
    in

    logf ~attributes:[Log.Cyan] "@\nComputing loop summary assuming: %a"
      F.format (F.negate phi);
    let str2 =
      Log.time "star2" star (mul assume_not_phi tr)
    in

    logf ~attributes:[Log.Cyan] "@\nComputing loop summary";
    BatList.reduce mul [
      str2;
      Log.time "star3" star (mul (mul str1 tr12) (mul str2 tr21));
      str1
    ]

  let star tr =
    (* todo: how do we handle multiple variables?  Right now, we just pick one
       to split on. *)
    let x = VarSet.choose (modified_floats tr) in
    let loop =
      split_star tr (F.leq (T.var (V.mk_var x)) (T.var (V.mk_var (primify x))))
    in
    logf ~level:3 "Loop summary: %a" format loop;
    loop
  let star tr = Log.time "star" star tr

  let simplify tr =
    let vars =
      VarSet.elements (formula_free_program_vars tr.guard)
    in
    let postify v =
      try M.find v tr.transform
      with Not_found -> T.var (V.mk_var v)
    in
    let rhs = BatList.of_enum (M.values tr.transform) in
    let post_diff = (* difference between pre-state and post-state vars *)
      List.map (fun (v, rhs) ->
	T.sub rhs (T.var (V.mk_var v))
      ) (BatList.of_enum (M.enum tr.transform))
    in
    let approx_diff = (* difference beween float & real vars *)
      let mk_var v = T.var (V.mk_var v) in
      let f x diffs =
	let pre = T.sub (mk_var x) (mk_var (primify x)) in
	let post = T.sub (postify x) (postify (primify x)) in
	[pre; post; T.sub post pre] @ diffs
      in
      VarSet.fold f (modified_floats tr) []
    in
    let templates =
      (List.map (fun v -> T.var (V.mk_var v)) vars)
      @ rhs
      @ post_diff
      @ approx_diff
    in
    let mk_box guard =
      F.conj (F.boxify templates (F.conj tr.guard guard)) guard
    in

    (* todo: how do we handle multiple variables?  Right now, we just pick one
       to split on. *)
    let guard =
      try
	let x = VarSet.choose (modified_floats tr) in
	let guard = F.leq (T.var (V.mk_var x)) (T.var (V.mk_var (primify x))) in
	let box1 = mk_box guard in
	let box2 = mk_box (F.negate guard) in
	F.disj box1 box2
      with Not_found -> mk_box F.top (* no modified floats *)
    in
    { tr with guard = F.nudge guard }
  let simplify tr = Log.time "simplify" simplify tr

  let star x = simplify (star x)
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

let float_weight cmd =
  match cmd with
  | Assign (v, rhs) ->
    let (rhs, rhs_err) = float_aexp rhs in
    { K.assign v rhs with K.guard = rhs_err }
  | Assume phi -> K.assume (float_bexp phi)
  | Skip -> K.one
  | Assert _ | Print _ -> K.one

let real_weight cmd =
  match primify_cmd cmd with
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
let analyze_sep (float,float_entry) (real,real_entry) =
  let man = Box.manager_of_box (Box.manager_alloc ()) in
  let analyze cfa entry =
    let vertex_tr v prop =
      if v = entry then Some (D.top man D.Env.empty) else prop
    in
    let tr e =
      AbstractDomain.lift
	(fun prop -> K.abstract_post man (Cfa.E.label e) prop)
    in
    let result =
      A.analyze_ldi vertex_tr ~edge_transfer:tr ~delay:3 ~max_decrease:2 cfa
    in
    A.output result
  in
  let float_annotation = analyze float float_entry in
  let real_annotation = analyze real real_entry in
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

let add_stuttering cfa =
  let g v cfa =
    if Cfa.mem_edge cfa v v then
      let k = Cfa.E.label (Cfa.find_edge cfa v v) in
      add_edge cfa v v (K.mul k k)
    else cfa
  in
  let f v cfa = add_edge cfa v v K.one in
  Cfa.fold_vertex f cfa (Cfa.fold_vertex g cfa cfa)

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

let greedy annotation vars float_tr real_tr real_succs =
  let open K in
  let open BatPervasives in

  let get_transform v tr =
    try M.find v tr.transform
    with Not_found -> T.var (V.mk_var v)
  in

(*
  let float_tr =
    { float_tr with guard = F.conj float_tr.guard annotation }
  in
  let float_tr = K.normalize float_tr in
*)

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

  (* Distance between the post-state of float_tr and real_succs *)
  let (other_dist, other_dist_cons) =
    let terms =
      let diff v =
	T.sub
	  (get_transform v float_tr)
	  (get_transform (primify v) real_succs)
      in
      BatEnum.map diff (BatList.enum vars)
    in
    let (other_dist, other_cons) = chebyshev terms in
    let guard =
      F.qe_lme
	(fun v -> V.equal other_dist v || not_tmp v)
	(F.big_conj (BatList.enum [
	  other_cons;
	  float_tr.guard;
	  real_succs.guard;
	  annotation;
	]))
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
    let lin_phi =
      linearize (F.conj annotation phi)
    in
    forall (not % (V.equal other_dist)) lin_phi
  in
  let guard =
    F.big_conj (BatList.enum [
      dist_guard;
      float_tr.guard;
      real_tr.guard;
      dist_cons;
      annotation
    ])
  in
  let add_transform v t tr = M.add v t tr in
  let res =
  { guard = guard;
    transform = M.fold add_transform float_tr.transform real_tr.transform }
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
    float_cfa : Cfa.t;
    real_cfa : Cfa.t }

let tensor_edge ctx e1 e2 =
  let open K in
  let src = (Cfa.E.src e1, Cfa.E.src e2) in
  let dst = (Cfa.E.dst e1, Cfa.E.dst e2) in
  let succs = ctx.tr_succs (Cfa.E.src e2) in
  let tr = greedy (ctx.annotation src) ctx.vars (Cfa.E.label e1) (Cfa.E.label e2) succs in
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
    let mk_edge (real_edge, float_edge) =
      tensor_edge ctx real_edge float_edge
    in
    BatEnum.map
      mk_edge
      (Putil.cartesian_product
	 (Cfa.enum_succ_e ctx.float_cfa u)
	 (Cfa.enum_succ_e ctx.real_cfa v))
  in
  let f (graph, phi, changed) e =
    let weight = TCfa.E.label e in
    let guard = F.subst sigma weight.K.guard in
    if F.is_sat (F.conj phi guard) then begin
      let dst = TCfa.E.dst e in
      let phi = F.conj phi (F.negate (F.qe_lme not_tmp guard)) in
      logf ~attributes:[Log.Green] "  Added an edge: %a -> %a"
	TCfa.VP.format (u, v)
	TCfa.VP.format dst;
      if TCfa.mem_vertex graph dst then
	(TCfa.add_edge_e graph e, phi, true)
      else
	(fst (expand ctx dst (K.mul pathexp weight)
		(TCfa.add_edge_e graph e, false)),
	 phi,
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
  let f v = T.sub (post v) (post (primify v)) in
  let g v bounds =
    let bound_str =
      match bounds with
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
(*
      let pathexp = pathexp (u, v) in
      expand ctx (u,v) pathexp (g, changed)
*)
      (g, changed)
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

(*********** Main function ****************
*******************************************)
let read_and_process infile =
  let lexbuf  = Lexing.from_channel infile in
  let Prog prog = Parser.main Lexer.token lexbuf in

  let (float_cfa, float_entry, float_exit) = build_cfa prog float_weight in
  let (real_cfa, real_entry, real_exit) = build_cfa prog real_weight in
  let real_cfa = reduce_cfa real_cfa real_entry real_exit in
  let float_cfa = reduce_cfa float_cfa float_entry float_exit in

  let annotation = analyze_sep (float_cfa,float_entry) (real_cfa,real_entry) in
  let real_cfa = add_stuttering real_cfa in
  let ctx =
    { annotation = annotation;
      tr_succs = tr_succs real_cfa;
      vars = collect_vars prog;
      float_cfa = float_cfa;
      real_cfa = real_cfa }
  in
  let entry = (float_entry, real_entry) in
  analyze ctx (sync ctx (float_cfa,float_entry) (real_cfa,real_entry)) entry

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

    F.opt_simplify_strategy := [guard_ex];
    ArkPervasives.opt_default_accuracy := 10;
    NumDomain.opt_max_coeff_size := None;
    K.opt_higher_recurrence := false;
    K.opt_disjunctive_recurrence_eq := false;
    K.opt_polyrec := false;
    K.opt_recurrence_ineq := false;
    K.opt_unroll_loop := false;
    K.opt_loop_guard := Some guard_ex;
    (try
       read_and_process infile
     with Apron.Manager.Error exc ->
       Log.errorf "Error: %a" Apron.Manager.print_exclog exc);
    close_in infile;
    Log.print_stats ()
