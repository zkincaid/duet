(*pp camlp4find deriving.syntax *)

open Apak
open ArkPervasives
open BatPervasives
open Hashcons

module type Var = sig
  include Putil.Ordered
  val prime : t -> t
  val to_smt : t -> Smt.ast
  val of_smt : Smt.symbol -> t
  val hash : t -> int
  val equal : t -> t -> bool
  val typ : t -> typ
  val tag : t -> int
end

module type Transition = sig
  include Sig.KA.Quantified.Ordered.S
  type term
  type formula
  val assign : var -> term -> t
  val assume : formula -> t
end

module Dioid (Var : Var) = struct
  open Term

  (* Max ID for temporary variables *)
  let max_id = ref 0

  (* Variables *)
  module V = struct
    module I = struct
      type t =
      | PVar of Var.t
      | TVar of int * typ * string
	  deriving (Compare)
      include Putil.MakeFmt(struct
	type a = t
	let format formatter = function
	  | PVar v -> Var.format formatter v
	  | TVar (id,_,name) -> Format.fprintf formatter "%s!%d" name id
      end)
      let format = Show_t.format
      let show = Show_t.show
      let tag = function
	| TVar (id, _, _) -> id lsl 1 + 1
	| PVar v -> Var.tag v lsl 1
    end
    include I
    module Map = Tagged.PTMap(I)

    let compare = Compare_t.compare
    let equal x y = compare x y = 0

    let hash = function
      | PVar v -> (Var.hash v) lsl 1
      | TVar (id,_,_) -> (Hashtbl.hash id) lsl 1 + 1
    let lower = function
      | PVar v -> Some v
      | TVar _ -> None
    let mk_tmp name typ =
      incr max_id;
      TVar (!max_id, typ, name)
    let mk_int_tmp name = mk_tmp name TyInt
    let mk_real_tmp name = mk_tmp name TyReal
    let mk_var v = PVar v
    let to_smt = function
      | PVar x -> Var.to_smt x
      | TVar (id,TyInt,name) ->
	Smt.int_var (name ^ "!" ^ (string_of_int id) ^ "!TyInt")
      | TVar (id,TyReal,name) ->
	Smt.real_var (name ^ "!" ^ (string_of_int id) ^ "!TyReal")

    let of_smt sym = match Smt.symbol_refine sym with
      | Z3.Symbol_string str -> begin
	try
	  let f name id typ = match typ with
	    | "TyReal" -> TVar (id,TyReal,name)
	    | "TyInt"  -> TVar (id,TyInt,name)
	    | _        -> raise (Scanf.Scan_failure "Invalid type identifier")
	  in
	  if BatString.exists str "!"
	  then Scanf.sscanf str "%[^!]!%d!%s" f
	  else PVar (Var.of_smt sym)
	with Scanf.Scan_failure _ -> PVar (Var.of_smt sym)
      end
      | Z3.Symbol_int _ -> PVar (Var.of_smt sym)

    let typ = function
      | TVar (_, typ, _) -> typ
      | PVar v           -> Var.typ v
  end

  module T = Term.Make(V)
  module F = Formula.Make(T)
  module M = Putil.MonoMap.Ordered.Make(Var)(T)
  module VarMemo = Memo.Make(Var)
  module VarSet = Putil.Set.Make(Var)
  module VSet = Putil.Set.Make(V)

  type t = 
    { transform: M.t;
      guard: F.t }
      deriving (Show,Compare)
  type var = Var.t

  let format = Show_t.format
  let show = Show_t.show
  let compare = Compare_t.compare
  let equal left right = compare left right = 0

  let mul left right =
    let sigma_tmp =
      Memo.memo (fun (_, typ, name) -> T.var (V.mk_tmp name typ))
    in
    let sigma v = match v with
      | V.PVar var -> begin
	try M.find var left.transform
	with Not_found -> T.var v
      end
      | V.TVar (id, typ, name) -> sigma_tmp (id, typ, name)
    in

    let transform = M.map (T.subst sigma) right.transform in

      (* Add bindings from left transform for variables that are not written
	 in right *)
    let f v term tr =
      if M.mem v tr then tr else M.add v term tr
    in
    let transform = M.fold f left.transform transform in

    let guard = F.conj left.guard (F.subst sigma right.guard) in
    { transform = transform;
      guard = guard }

  let add left right =
    let left_guard = ref left.guard in
    let right_guard = ref right.guard in
    let left_eq s t =
      left_guard := F.conj (!left_guard) (F.eq s t)
    in
    let right_eq s t =
      right_guard := F.conj (!right_guard) (F.eq s t)
    in
    let transform =
      let merge v x y =
	let varname = "phi_" ^ (Var.show v) in
	match x, y with
	| Some s, Some t ->
	  if T.equal s t then Some s else begin
	    let tmp = T.var (V.mk_tmp varname (Var.typ v)) in
	    left_eq tmp s;
	    right_eq tmp t;
	    Some tmp
	  end
	| Some s, None ->
	  let tmp = T.var (V.mk_tmp varname (Var.typ v)) in
	  left_eq tmp s;
	  right_eq tmp (T.var (V.mk_var v));
	  Some tmp
	| None, Some t ->
	  let tmp = T.var (V.mk_tmp varname (Var.typ v)) in
	  left_eq tmp (T.var (V.mk_var v));
	  right_eq tmp t;
	  Some tmp
	| None, None -> assert false
      in
      M.merge merge left.transform right.transform
    in
    { transform = transform;
      guard = F.disj (!left_guard) (!right_guard) }

  let one =
    { transform = M.empty;
      guard = F.top }

  let zero =
    { transform = M.empty;
      guard = F.bottom }

  (* Convert a transition into a formula over primed/unprimed variables *)
  let to_formula tr =
    let f var term phi =
      F.conj (F.eq (T.var (V.mk_var (Var.prime var))) term) phi
    in
    M.fold f tr.transform tr.guard

  let to_smt tr =
    let guard = F.to_smt tr.guard in
    let f var term phi =
      Smt.conj (Smt.mk_eq (Var.to_smt (Var.prime var)) (T.to_smt term)) phi
    in
    M.fold f tr.transform guard

  let assign var term =
    { transform = M.singleton var term;
      guard = F.top }

  let assume phi =
    { transform = M.empty;
      guard = phi }

  let term_free_program_vars term =
    let open Term in
    let f = function
      | OVar v -> begin match V.lower v with
	| Some v -> VarSet.singleton v
	| None -> VarSet.empty
      end
      | OConst _ -> VarSet.empty
      | OAdd (x,y) | OMul (x,y) | ODiv (x,y) -> VarSet.union x y
      | OFloor x -> x
    in
    T.eval f term

  let formula_free_program_vars phi =
    let open Formula in
    let f = function
      | OOr (x,y) | OAnd (x,y) -> VarSet.union x y
      | OAtom (LeqZ t) | OAtom (EqZ t) | OAtom (LtZ t) ->
	term_free_program_vars t
    in
    F.eval f phi

  let term_free_tmp_vars term =
    let open Term in
    let f = function
      | OVar v -> begin match V.lower v with
	| Some _ -> VSet.empty
	| None   -> VSet.singleton v
      end
      | OConst _ -> VSet.empty
      | OAdd (x,y) | OMul (x,y) | ODiv (x,y) -> VSet.union x y
      | OFloor x -> x
    in
    T.eval f term

  let formula_free_tmp_vars phi =
    let open Formula in
    let f = function
      | OOr (x,y) | OAnd (x,y) -> VSet.union x y
      | OAtom (LeqZ t) | OAtom (EqZ t) | OAtom (LtZ t) ->
	term_free_tmp_vars t
    in
    F.eval f phi

  let simplify tr =
    let f _ term free = VSet.diff free (term_free_tmp_vars term) in
    let guard = F.linearize (fun () -> V.mk_tmp "nonlin" TyInt) tr.guard in
    let free_tmp = M.fold f tr.transform (formula_free_tmp_vars guard) in
    { tr with guard = F.simplify (not % flip VSet.mem free_tmp) guard }

  let exists p tr =
    let transform = M.filter (fun k _ -> p k) tr.transform in
    let rename = VarMemo.memo (fun v -> V.mk_tmp (Var.show v) (Var.typ v)) in
    let sigma v = match V.lower v with
      | Some var -> T.var (if p var then v else rename var)
      | None -> T.var v
    in
    { transform = transform;
      guard = F.subst sigma tr.guard }

  let post_formula tr =
    let phi =
      F.linearize
	(fun () -> V.mk_tmp "nonlin" TyReal)
	(to_formula tr)
    in
    let var = T.var % V.mk_var in
    let unprime =
      M.of_enum (M.enum tr.transform /@ (fun (v,_) -> (Var.prime v, var v)))
    in
    let p v = match V.lower v with
      | Some v -> not (M.mem v tr.transform)
      | None -> false
    in
    let sigma v = match V.lower v with
      | Some v -> if M.mem v unprime then M.find v unprime else var v
      | None   -> assert false
    in
    F.subst sigma (F.exists p phi)
end

module Make (Var : Var) = struct
  include Dioid(Var)

  (* Iteration operator options *)
  let opt_higher_recurrence = ref true
  let opt_disjunctive_recurrence_eq = ref true
  let opt_recurrence_ineq = ref false
  let opt_higher_recurrence_ineq = ref false
  let opt_unroll_loop = ref true
  let opt_loop_guard = ref false

  (**************************************************************************)
  (* Implementation of iteration operator *)
  (**************************************************************************)
  module Incr = struct

    (* Polynomials with rational coefficients *)
    module P = Linear.Expr.MakePolynomial(QQ)
    module Gauss = Linear.GaussElim(QQ)(P)
    module Env = BatMap.Make(Var)

    let eval env =
      let open Term in
      let alg = function
	| OConst k -> Some (P.zero, T.const k)
	| OAdd (Some (px, cx), Some (py, cy)) ->
	  Some (P.add px py, T.add cx cy)
	| OAdd (_, _) ->
	  Log.log Log.info "Nonlinear add";
	  None
	| OMul (Some (px, cx), Some (py, cy)) ->
	  if P.equal px P.zero && T.get_const cx != None then begin
	    match T.get_const cx with
	    | Some k ->
	      Some (P.scalar_mul k py, T.mul (T.const k) cy)
	    | None -> None
	  end else if P.equal py P.zero then begin
	    match T.get_const cy with
	    | Some k ->
	      Some (P.scalar_mul k px, T.mul (T.const k) cx)
	    | None -> None
	  end else begin
	    Log.logf Log.info "Nonlinear mul: [%a] * [%a]"
	      P.format px
	      P.format py;
	    None
	  end
	| OVar x -> begin match V.lower x with
	  | None -> None
	  | Some v ->
	    if not (Env.mem v env) then
	      (* v not in env -> v satisfies the recurrence v_{k+1} = v_{k} *)
	      Some (P.zero, T.var x)
	    else begin
	      match Env.find v env with
	      | Some (px, cx) ->
		let x_minus_1 = P.add_term 1 QQ.one (P.negate P.one) in
		(* Polynomial p(X) gives closed form for the kth term in the
		   sequence of values for v.  Since recurrence is written in
		   terms of the value of v in the pre-state, we need to look at
		   the (k-1)th term, so we use p(X-1) *)
		Some (P.compose px x_minus_1, cx)
	      (*		  Some (px, cx)*)
	      | None -> None
	    end
	end
	| _ -> None
      in
      T.eval alg

    let eval env term =
      match eval env term with
      | Some (px, cx) ->
	Log.logf Log.info "Eval rhs: %a ~> %a" T.format term P.format px;
	Some (px, cx)
      | None ->
	Log.logf Log.info "Eval rhs: %a ~> _|_" T.format term;
	None

    (* Given a polynomial p, compute a polynomial q such that for any k, q(k)
       = p(0) + p(1) + ... + p(k-1) *)
    let summation : P.t -> P.t = fun p ->
      let open BatEnum in
      let order = (P.order p) + 1 in (* order of q is 1 + order of p *)

      (* Create a system of linear equalities:
	 c_n*0^n + ... + c_1*0 + c_0 = p(0)
	 c_n*1^n + ... + c_1*1 + c_0 = p(0) + p(1)
	 c_n*2^n + ... + c_1*2 + c_0 = p(0) + p(1) + p(2)
	 ...
	 c_n*n^n + ... + c_1*n + c_0 = p(0) + p(1) + ... + p(n)

	 We then solve for the c_i coefficients to get q
      *)
      let rec mk_sys k =
	if k = 0 then begin
	  let rhs = QQ.zero in
	  let lhs = P.var 0 in
	  (rhs, [(lhs,rhs)])
	end else begin
	  assert (k > 0);
	  let (prev, rest) = mk_sys (k - 1) in
	  let rhs = QQ.add prev (P.eval p (QQ.of_int k)) in
	  let vars = BatEnum.(---) 1 order in
	  let lhs =
	    let qq_k = QQ.of_int k in
	    let f (rx, last) ord =
	      let next = QQ.mul last qq_k in
	      (P.add_term ord next rx, next)
	    in
	    fst (BatEnum.fold f (P.one, QQ.one) vars)
	  in
	  (rhs, (lhs,rhs)::rest)
	end
      in

      let sys = snd (mk_sys order) in
      let soln = Gauss.solve sys in
      let vars = BatEnum.range ~until:order 0 in
      let add_order lin k = P.add_term k (soln k) lin in
      BatEnum.fold add_order P.zero vars

    (* Convert a polynomial into a term *)
    let to_real_term (px, cx) var =
      let open BatEnum in
      let to_term (order, cq) = T.mul (T.const cq) (T.exp var order) in
      let e = P.enum px /@ to_term in
      match BatEnum.peek e with
      | Some _ -> T.add cx (reduce T.add e)
      | None   -> cx

    (* Convert a polynomial into a term, using only integer division *)
    let to_int_term (px, cx) var =
      let e = P.enum px /@ (fun (order, cq) -> (T.exp var order, cq)) in
      T.add (T.qq_linterm e) cx

    let to_term (px, cx) var = function
      | TyInt -> to_int_term (px, cx) var
      | TyReal -> to_real_term (px, cx) var
  end

  module VarMap = BatMap.Make(Var)
  module FEq = Formula.MakeEq(F)

  (* Linear terms with rational efficients *)
  module QQTerm = Linear.Expr.Make(Var)(QQ)

  (* Iteration operator context.  The iteration operator is defined as a
     sequence of iteration context transformers. *)
  type iteration_context =
    { loop : t;  (* Transition representing the loop summary *)
      phi : F.t; (* Formula representing the loop body *)

      (* Induction variables are variables with exact recurrences (defined by
	 equalities of the form x' = x + p(y), where p(y) is a polynomial in
	 induction variables of lower strata) *)
      induction_vars : (Incr.P.t * T.t) option Incr.Env.t; 

      (* Variable term representing the loop iteration *)
      loop_counter : T.t }

  (* Hack to simplify control flow when a loop body is unsatisfiable.
     Should't be visible outside this module. *)
  exception Unsat

  (* Find recurrences of the form x' = x + c *)
  let simple_induction_vars ctx =
    let s = new Smt.solver in
    s#assrt (F.to_smt ctx.phi);
    let m = match s#check () with
      | Smt.Unsat -> raise Unsat
      | Smt.Undef -> assert false
      | Smt.Sat -> s#get_model ()
    in
    let induction_var v _ =
      let incr =
	QQ.sub
	  (m#eval_qq (Var.to_smt (Var.prime v)))
	  (m#eval_qq (Var.to_smt v))
      in
      let diff = Smt.sub (Var.to_smt (Var.prime v)) (Var.to_smt v) in
      s#push();
      s#assrt (Smt.mk_not (Smt.mk_eq diff (Smt.const_qq incr)));
      let res = match s#check () with
	| Smt.Unsat ->
	  Log.logf Log.info "Found recurrence: %a' = %a + %a"
	    Var.format v
	    Var.format v
	    QQ.format incr;
	  let px_closed = Incr.P.add_term 1 incr Incr.P.zero in
	  Some (px_closed, T.var (V.mk_var v))
 	| Smt.Sat | Smt.Undef ->
	  Log.logf Log.info "No recurrence for %a" Var.format v;
	  None
      in
      s#pop ();
      res
    in
    let induction_vars =
      Log.time
	"(Simple) induction variable detection"
	(Incr.Env.mapi induction_var)
	ctx.induction_vars
    in
    { ctx with induction_vars = induction_vars }

  (* Find "recurrences" of the form
     x' = x + c \/ x' = x + d
  *)
  let disj_induction_vars ctx =
    let vars =
      Incr.Env.fold
	(fun v recurrence vs -> match recurrence with
	| None -> v::vs
	| Some _ -> vs)
	ctx.induction_vars
	[]
    in
    let deltas =
      List.map
	(fun v -> T.sub (T.var (V.mk_var (Var.prime v))) (T.var (V.mk_var v)))
	vars
    in
    let cases = F.disj_optimize deltas ctx.phi in
    let case_vars = List.map (fun case -> T.var (V.mk_int_tmp "K")) cases in
    let f loop v cases =
      let g sum case_var (lo, hi) = match sum, lo, hi with
	| (Some sum, Some lo, Some hi) when QQ.equal lo hi ->
	  Some (T.add (T.mul case_var (T.const lo)) sum)
	| (_, _, _) -> None
      in
      match BatList.fold_left2 g (Some T.zero) case_vars cases with
      | Some sum ->
	{ loop with guard = F.conj loop.guard 
	    (F.eq (T.add (T.var (V.mk_var v)) (M.find v loop.transform)) sum) }
      | None -> loop
    in
    let loop = BatList.fold_left2 f ctx.loop vars (BatList.transpose cases) in

    let sum = List.fold_left T.add T.zero case_vars in
    let guard =
      List.fold_left
	F.conj
	(F.eq sum ctx.loop_counter)
	(List.map (fun v -> F.leqz (T.neg v)) case_vars)
    in
    let loop = { loop with guard = F.conj loop.guard guard } in
    { ctx with loop = loop }

  (* Higher induction variables *********************************************)
  (* There are two algorithms here: simple_higher_induction_vars, which uses
     the transform map to discover recurrence relations (which means that it
     generally misses induction variables when there are branches or nested
     loops within the loop body); and higher_induction_vars, which uses a more
     complicated scheme which is (hopefully) complete. *)

  let closed_form env loop_counter v rhs =
    match Incr.eval env rhs with
    | Some (px, cx) ->
      Log.logf Log.info "Polynomial for %a: %a"
	Var.format v
	Incr.P.format px;
      let px_closed = Incr.summation px in
      let cx_closed =
	T.add (T.mul loop_counter cx) (T.var (V.mk_var v))
      in
      Log.logf Log.info "Closed form for %a: %a"
	Var.format v
	Incr.P.format px_closed;
      Some (px_closed, cx_closed)
    | None -> None

  let simple_higher_induction_vars tr env loop_counter =
    let check v rhs =
      closed_form env loop_counter v (T.sub rhs (T.var (V.mk_var v)))
    in
    let g v rhs env =
      try begin match Incr.Env.find v env with
      | Some _ -> env
      | None -> begin
	match check v rhs with
	| Some incr -> Incr.Env.add v (Some incr) env
	| None -> env
      end end with Not_found -> assert false
    in
    M.fold g tr.transform env

  let farkas equations vars =
    let lambdas =
      List.map (fun _ -> AVar (V.mk_real_tmp "lambda")) equations
    in
    let open FEq in
    let s = new Smt.solver in
    let columns = AConst::(List.map (fun x -> AVar x) vars) in
    
    (* Build var -> smt var mappings -- we need to do this because just
       calling V.to_smt will produce integer-sorted variables and we need
       them to be rational-sorted. *)
    let column_smt =
      BatEnum.foldi
	(fun i c m -> AMap.add c (Smt.real_var ("c$" ^ (string_of_int i))) m)
	AMap.empty
	(BatList.enum columns)
    in
    let lambda_smt =
      let lambda_smt = function 
	| AVar v -> Smt.real_var (F.T.V.show v)
	| AConst -> Smt.real_var "k$"
      in
      List.fold_left
	(fun m lambda -> AMap.add lambda (lambda_smt lambda) m)
	AMap.empty
	lambdas
    in

    let assrt (v, sum) =
      let sum =
	F.T.Linterm.to_smt (fun x -> AMap.find x lambda_smt) Smt.const_qq sum
      in
      s#assrt (Smt.mk_eq (AMap.find v column_smt) sum)
    in
    let equations_tr = T.Linterm.transpose equations lambdas columns in
    BatEnum.iter assrt (BatEnum.combine
			  (BatList.enum columns, BatList.enum equations_tr));
    (s, column_smt)

  let higher_induction_vars ctx =
    let mk_avar v = AVar (V.mk_var v) in
    let primed_vars = VarSet.of_enum (M.keys ctx.loop.transform /@ Var.prime) in
    let vars =
      let free_vars = formula_free_program_vars ctx.phi in
      BatList.of_enum (VarSet.enum free_vars /@ V.mk_var)
    in
    let equalities = FEq.extract_equalities ctx.phi vars in
    Log.logf Log.info "Extracted equalities:@ %a"
      Show.format<T.Linterm.t list> equalities;
    let (s, coeffs) = farkas equalities vars in
    let get_coeff v = FEq.AMap.find (mk_avar v) coeffs in
    (* A variable has a coefficient iff it is involved in an equality. *)
    let has_coeff v = FEq.AMap.mem (mk_avar v) coeffs in

    let remove_coeff x coeffs = FEq.AMap.remove (AVar (V.mk_var x)) coeffs in
    let assert_zero_coeff v =
      try s#assrt (Smt.mk_eq (get_coeff v) (Smt.const_int 0))
      with Not_found ->
	(* No coefficient assigned to v => we may assume it's zero without
	   asserting anything *)
	()
    in
    let find_recurrence v =
      Log.logf Log.info "Is `%a' an induction variable?"
	Var.format v;
      s#push ();

      s#assrt (Smt.mk_eq (get_coeff v) (Smt.const_int 1));
      s#assrt (Smt.mk_eq (get_coeff (Var.prime v)) (Smt.const_int (-1)));

      (* The coefficient of a non-induction variable (other than v) must be
	 0 *)
      Incr.Env.iter (fun x rhs ->
	match rhs with
	| None -> assert_zero_coeff x
	| Some (_, _) -> ()
      ) (Incr.Env.remove v ctx.induction_vars);

      (* The coefficient of a primed variable (other than v') must be 0 *)
      VarSet.iter assert_zero_coeff (VarSet.remove (Var.prime v) primed_vars);

      match s#check () with
      | Smt.Unsat | Smt.Undef -> (s#pop (); None)
      | Smt.Sat ->
	let m = s#get_model () in
	let f v coeff ts =
	  match v with
	  | AVar v -> (T.var v, m#eval_qq coeff)::ts
	  | AConst -> (T.one, m#eval_qq coeff)::ts
	in
	(* Remove v & v' terms -- we want the term t such that v' = v + t,
	   and we already set the coefficients of v and v' appropriately *)
	let coeffs = remove_coeff v (remove_coeff (Var.prime v) coeffs) in
	s#pop ();
	Some (T.qq_linterm (BatList.enum (FEq.AMap.fold f coeffs [])))
    in
    let check v rhs =
      match rhs with
      | Some (px, cx) -> Some (px, cx)
      | None ->
	if has_coeff v then begin
	  match find_recurrence v with
	  | Some rhs -> closed_form ctx.induction_vars ctx.loop_counter v rhs
	  | None -> None
	end
	else
	  (* v isn't involved in any equalities => can't satisfy any
	     recurrences*)
	  None
    in
    { ctx with induction_vars = Incr.Env.mapi check ctx.induction_vars }

  (* Simple recurrence inequations.  E.g., x + 0 <= x' <= x + 1. *)
  let recurrence_ineq ctx =
    let non_induction =
      let f (v, r) = match r with
	| Some _ -> None
	| None   -> Some v
      in
      BatList.of_enum (BatEnum.filter_map f (VarMap.enum ctx.induction_vars))
    in
    let deltas =
      let f v =
	T.sub (T.var (V.mk_var (Var.prime v))) (T.var (V.mk_var v))
      in
      List.map f non_induction
    in
    let bounds = F.symbolic_abstract deltas ctx.phi in
    let h tr (v, (lo, hi)) =
      let delta =
	try T.sub (M.find v tr.transform) (T.var (V.mk_var v))
	with Not_found -> assert false
      in
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
      Log.logf Log.info "Bounds for %a: %s%a'-%a%s"
	Var.format v
	lo_string
	Var.format v
	Var.format v
	hi_string;
      { tr with guard = F.conj (F.conj lower upper) tr.guard }
    in
    let loop =
      BatEnum.fold h ctx.loop (BatEnum.combine (BatList.enum non_induction,
						BatList.enum bounds))
    in
    { ctx with loop = loop }

  let loop_guard ctx =
    let primed_vars = VarSet.of_enum (M.keys ctx.loop.transform /@ Var.prime) in
    let unprime =
      VarMap.of_enum (M.enum ctx.loop.transform
		      /@ (fun (v,_) -> (Var.prime v, v)))
    in
    let vars = formula_free_program_vars ctx.phi in
    let pre_vars =
      VarSet.filter (not % flip VarMap.mem unprime) vars
    in
    let post_vars =
      VarSet.union
	(VarSet.filter (not % flip M.mem ctx.loop.transform) pre_vars)
	primed_vars
    in
    let low f v = match V.lower v with
      | Some v -> f v
      | None   -> false
    in
    let pre_guard =
      F.exists (low (flip VarSet.mem pre_vars)) ctx.phi
    in
    let post_guard =
      F.exists (low (flip VarSet.mem post_vars)) ctx.phi
    in
    let sigma v = match V.lower v with
      | Some x ->
	if VarMap.mem x unprime
	then M.find (VarMap.find x unprime) ctx.loop.transform
	else T.var v
      | None -> assert false (* impossible *)
    in
    let post_guard = F.subst sigma post_guard in
    Log.logf Log.info "pre_guard:@\n%a" F.format pre_guard;
    Log.logf Log.info "post_guard:@\n%a" F.format post_guard;
    let plus_guard =
      F.conj
	(F.conj pre_guard post_guard)
	(F.geq ctx.loop_counter T.one)
    in
    let zero_guard =
      let eq (v, t) = F.eq (T.var (V.mk_var v)) t in
      F.conj
	(F.eqz ctx.loop_counter)
	(F.big_conj (BatEnum.map eq (M.enum ctx.loop.transform)))
    in
    let star_guard = F.disj plus_guard zero_guard in
    { ctx.loop with guard = F.conj ctx.loop.guard star_guard }

  (* Compute recurrence relations of the form
     x + ay + b <= x' <= x + cy + d
  *)
  let higher_recurrence_ineq ctx =
    let primed_vars = VarSet.of_enum (M.keys ctx.loop.transform /@ Var.prime) in
    let is_induction_var v = match V.lower v with
      | Some var ->
	begin
	  try (Incr.Env.find var ctx.induction_vars) != None
	  with Not_found ->
	      (* v is either a primed variable or was not updated in the loop
		 body *)
	    not (VarSet.mem var primed_vars)
	end
      | None     -> false
    in
    let rewrite =
      let sigma v = match V.lower v with
	| Some x ->
	  begin
	    try
	      match Incr.Env.find x ctx.induction_vars with
	      | Some incr ->
		Incr.to_term incr ctx.loop_counter (Var.typ x)
	      | None -> assert false
	    with Not_found ->
		(* We only fall into this case if v is not updated in the loop
		   body (v is not in the domain of tr.transform) *)
	      T.var v
	  end
	| None -> T.var v
      in
      T.subst sigma
    in
    let formula_of_bounds t bounds =
      let f (pred, bound) =
	let bound = T.mul ctx.loop_counter (rewrite bound) in
	match pred with
	| Plt  -> F.lt t bound
	| Pgt  -> F.gt t bound
	| Pleq -> F.leq t bound
	| Pgeq -> F.geq t bound
	| Peq  -> F.eq t bound
      in
      BatEnum.fold F.conj F.top (BatEnum.map f (BatList.enum bounds))
    in
    let g v incr tr =
      match incr with
      | Some _ -> tr
      | None ->
	Log.logf Log.info "Compute symbolic bounds for variable: %a"
	  Var.format v;
	let delta =
	  T.sub (T.var (V.mk_var (Var.prime v))) (T.var (V.mk_var v))
	in
	let bounds =
	  try F.symbolic_bounds is_induction_var ctx.phi delta
	  with Not_found -> assert false
	in
	let nondet =
	  T.var (V.mk_tmp ("nondet_" ^ (Var.show v)) (Var.typ v))
	in
	let bounds_formula = formula_of_bounds nondet bounds in
	Log.logf Log.info "Bounds: %a" F.format bounds_formula;
	{ transform = M.add v (T.add (T.var (V.mk_var v)) nondet) tr.transform;
	  guard = F.conj (formula_of_bounds nondet bounds) tr.guard }
    in
    let loop = Incr.Env.fold g ctx.induction_vars ctx.loop in
    { ctx with loop = loop }

  let star tr =
    Log.logf Log.fix "Loop body:@\n%a" format tr;
    let mk_nondet v _ =
      T.var (V.mk_tmp ("nondet_" ^ (Var.show v)) (Var.typ v))
    in
    let loop_counter = T.var (V.mk_int_tmp "K") in
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
      ]
    in

    (* Compute closed forms for induction variables *)
    let close v incr transform =
      match incr with
      | Some incr ->
	let t = Incr.to_term incr ctx.loop_counter (Var.typ v) in
	Log.logf Log.info "Closed term for %a: %a"
	  Var.format v
	  T.format t;
	M.add v t transform
      | None -> transform
    in
    let transform = Incr.Env.fold close ctx.induction_vars ctx.loop.transform in

    let loop = { ctx.loop with transform = transform } in

    let loop =
      if !opt_loop_guard then loop_guard { ctx with loop = loop }
      else loop
    in
    let loop =
      if !opt_unroll_loop then add one (mul loop tr)
      else loop
    in
    Log.logf Log.fix "Loop summary: %a" format loop;
    loop

  let star tr =
    try star tr
    with Unsat -> one
end
