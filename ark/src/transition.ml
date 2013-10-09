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

  module T = Term.MakeHashconsed(V)
  module F = Formula.MakeHashconsed(T)
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

  let exists p tr =
    let transform = M.filter (fun k _ -> p k) tr.transform in
    let rename = VarMemo.memo (fun v -> V.mk_tmp (Var.show v) (Var.typ v)) in
    let sigma v = match V.lower v with
      | Some var -> T.var (if p var then v else rename var)
      | None -> T.var v
    in
    { transform = transform;
      guard = F.subst sigma tr.guard }


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
      | OLeqZ t | OEqZ t | OLtZ t -> term_free_program_vars t
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
      | OLeqZ t | OEqZ t | OLtZ t -> term_free_tmp_vars t
    in
    F.eval f phi

  let simplify tr =
    let f _ term free = VSet.diff free (term_free_tmp_vars term) in
    let free_tmp = M.fold f tr.transform (formula_free_tmp_vars tr.guard) in
    { tr with guard = F.exists (not % flip VSet.mem free_tmp) tr.guard }
end

module Make (Var : Var) = struct
  include Dioid(Var)

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

  (* Is [v] a simple induction variable? *)
  let induction_var s m v =
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
	let px_closed = Incr.P.add_term 1 incr Incr.P.zero in
	Some (px_closed, T.var (V.mk_var v))
      | Smt.Sat | Smt.Undef -> None
    in
    s#pop ();
    res

  let select_disjunct m = F.select_disjunct (m#eval_qq % V.to_smt)

  let disj_induction_vars tr vars =
    let s = new Smt.solver in
    let ns = new Smt.solver in
    let get_offset =
      let f i v m =
	VarMap.add v (Smt.int_var ("c$" ^ (string_of_int i))) m
      in
      let m = BatEnum.foldi f VarMap.empty (BatList.enum vars) in
      fun v -> VarMap.find v m
    in
    let phi = to_formula tr in
    let smt_cases cases =
      let f case =
	Smt.big_conj
	  ((VarMap.enum case)
	   /@ (fun (v, offset) ->
	     Smt.mk_eq (get_offset v) (Smt.const_qq offset)))
      in
      Smt.big_disj (BatList.enum cases /@ f)
    in
    let rec go ind_vars cases =
      s#push ();
      s#assrt (Smt.mk_not (smt_cases cases));
      match s#check () with
      | Smt.Unsat -> (ind_vars, cases) (* found all the cases *)
      | Smt.Undef -> ([], []) (* give up *)
      | Smt.Sat ->
	(* new case *)
	let m = s#get_model () in
	let disjunct = match select_disjunct m phi with
	  | Some d -> d
	  | None ->
	    Log.errorf "Couldn't select a disjunct for:\n%a\nUsing model:\n%s"
	      F.format phi
	      (m#to_string ());
	    assert false
	in
	ns#push ();
	ns#assrt (F.to_smt disjunct);
	let f case v =
	  ns#push ();
	  let offset = get_offset v in
	  let incr = m#eval_qq offset in
	  ns#assrt (Smt.mk_not (Smt.mk_eq offset (Smt.const_qq incr)));
	  let res = match ns#check () with
	    | Smt.Unsat -> VarMap.add v incr case
	    | Smt.Sat | Smt.Undef -> case
	  in
	  ns#pop ();
	  res
	in
	let new_case = List.fold_left f VarMap.empty ind_vars in
	let new_ind_vars = BatList.of_enum (VarMap.keys new_case) in
	Log.logf Log.info "Found case: %a"
	  (Putil.format_enum (fun formatter (v,k) ->
	    Format.fprintf formatter "%a' = %a + %a"
	      Var.format v Var.format v QQ.format k)
	     ~left:"" ~sep:";" ~right:"")
	  (VarMap.enum new_case);
	s#pop ();
	ns#pop ();
	go new_ind_vars (new_case::cases)
    in
    let f v =
      let phi =
	Smt.mk_eq
	  (Var.to_smt (Var.prime v))
	  (Smt.add (Var.to_smt v) (get_offset v))
      in
      s#assrt phi;
      ns#assrt phi
    in
    s#assrt (to_smt tr);
    List.iter f vars;
    Log.log Log.info "Starting disjunctive IVD";
    Log.logf Log.info "-- candidates: %s" (Show.show<Var.t list> vars);
    go vars []

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
	T.add (T.mul (T.var loop_counter) cx) (T.var (V.mk_var v))
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
    let open FEq.A in
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
      List.fold_left
	(fun m lambda -> AMap.add lambda (Smt.real_var (show lambda)) m)
	AMap.empty
	lambdas
    in

    let assrt (v, sum) =
      let sum =
	AffineTerm.to_smt (fun x -> AMap.find x lambda_smt) Smt.const_qq sum
      in
      s#assrt (Smt.mk_eq (AMap.find v column_smt) sum)
    in
    let equations_tr = AffineTerm.transpose equations lambdas columns in
    BatEnum.iter assrt (BatEnum.combine
			  (BatList.enum columns, BatList.enum equations_tr));
    (s, column_smt)

  let higher_induction_vars tr env loop_counter =
    let open FEq.A in
    let phi_tr = to_formula tr in
    let mk_avar v = AVar (V.mk_var v) in
    let primed_vars = VarSet.of_enum (M.keys tr.transform /@ Var.prime) in
    let vars =
      let free_vars = formula_free_program_vars phi_tr in
      BatList.of_enum (VarSet.enum free_vars /@ V.mk_var)
    in
    let equalities = FEq.extract_equalities phi_tr vars in
    Log.logf Log.info "Extracted equalities:@ %a"
      Show.format<FEq.AffineTerm.t list> equalities;
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
      ) (Incr.Env.remove v env);

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
	  | Some rhs -> closed_form env loop_counter v rhs
	  | None -> None
	end
	else
	  (* v isn't involved in any equalities => can't satisfy any
	     recurrences*)
	  None
    in
    Incr.Env.mapi check env

  let star tr =
    Log.logf Log.info "Loop body:@\n%a" format tr;
    let s = new Smt.solver in
    let loop_counter = V.mk_int_tmp "K" in
    s#push ();
    s#assrt (to_smt tr);

    match s#check () with
    | Smt.Unsat -> one
    | Smt.Undef -> assert false
    | Smt.Sat ->
      let m = s#get_model () in

      let f v _ env = Incr.Env.add v (induction_var s m v) env in
      let induction_vars =
	Log.time
	  "(Simple) induction variable detection"
	  (M.fold f tr.transform)
	  Incr.Env.empty
      in
      let induction_vars =
	Log.time
	  "Higher induction variable detection"
	  (higher_induction_vars tr induction_vars)
	  loop_counter
      in
      let non_induction =
	let f v incr vs =
	  match incr with
	  | Some _ -> vs
	  | None -> v::vs
	in
	Incr.Env.fold f induction_vars []
      in
      let (disj_vars, cases) =
	Log.time
	  "Disjunctive induction variable detection"
	  (disj_induction_vars tr)
	  non_induction
      in
      let cases =
	List.map (fun case -> (case, T.var (V.mk_int_tmp "K"))) cases
      in
      let g v incr tr =
	match incr with
	| Some incr ->
	  let t = Incr.to_term incr (T.var loop_counter) (Var.typ v) in
	  Log.logf Log.info "Closed term for %a: %a"
	    Var.format v
	    T.format t;
	  M.add v t tr
	| None ->
	  if not (List.mem v disj_vars) then begin
	    Log.logf Log.info "Not an induction variable: %a" Var.format v;
	    M.add v (T.var (V.mk_tmp ("nondet_"^(Var.show v)) (Var.typ v))) tr
	  end else tr
      in
      let transform = Incr.Env.fold g induction_vars M.empty in
      let transform =
	let add_var tr v =
	  let f (case, counter) =
	    T.mul (T.const (VarMap.find v case)) counter
	  in
	  let sum = List.fold_left T.add T.zero (List.map f cases) in
	  M.add v (T.add (T.var (V.mk_var v)) sum) tr
	in
	List.fold_left add_var transform disj_vars
      in
      let nonnegative x = F.leqz (T.neg x) in
      let guard =
	let f acc (_, counter) = T.add acc counter in
	let sum = List.fold_left f T.zero cases in
	let guard =
	  F.conj
	    (F.eq sum (T.var loop_counter))
	    (nonnegative (T.var loop_counter))
	in
	let f acc (_, counter) = F.conj acc (nonnegative counter) in
	List.fold_left f guard cases
      in
      let res = { transform = transform;
		  guard = guard }
      in
      Log.logf Log.info "Loop summary:@\n%a" format res;
      add one (mul res tr)
end
