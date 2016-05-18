open Apak
open ArkPervasives
open BatPervasives
open Hashcons

include Log.Make(struct let name = "ark.transition" end)

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

(* Max ID for temporary variables *)
let max_id = ref 0

module Dioid (Var : Var) = struct
  open Term

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
      | Smt.Symbol_string str -> begin
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
      | Smt.Symbol_int _ -> PVar (Var.of_smt sym)

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
      deriving (Compare)
  type var = Var.t

  let compare = Compare_t.compare

  include Putil.MakeFmt(struct
      type a = t
      let format formatter tr =
        Format.fprintf formatter
          "{@[<v 0>transform:@;  @[<v 0>%a@]@;guard:@;  @[<v 0>%a@]@]}"
          (ApakEnum.pp_print_enum_nobox
             ~pp_sep:(fun formatter () -> Format.pp_print_break formatter 0 0)
             (fun formatter (lhs, rhs) ->
                Format.fprintf formatter "%a := %a"
                  Var.format lhs
                  T.format rhs))
          (M.enum tr.transform)

          F.format tr.guard
    end)

  let modifies x =
    M.fold (fun v _ set -> VarSet.add v set) x.transform VarSet.empty

  let term_free_program_vars term =
    let open Term in
    let f = function
      | OVar v -> begin match V.lower v with
          | Some v -> VarSet.singleton v
          | None -> VarSet.empty
        end
      | OConst _ -> VarSet.empty
      | OAdd (x,y) | OMul (x,y) | ODiv (x,y) | OMod (x,y) -> VarSet.union x y
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
      | OAdd (x,y) | OMul (x,y) | ODiv (x,y) | OMod (x,y) -> VSet.union x y
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

  (* alpha equivalence - only works for normalized transitions! *)
  let equiv x y =
    let sigma =
      let f v rhs m =
        match T.to_var rhs, T.to_var (M.find v y.transform) with
        | Some a, Some b -> V.Map.add a b m
        | _, _ -> assert false
      in
      let map = M.fold f x.transform V.Map.empty in
      fun v ->
        try T.var (V.Map.find v map)
        with Not_found -> T.var v
    in
    let x_guard = F.subst sigma x.guard in
    F.equiv x_guard y.guard

  exception Not_normal (* Not externally visible *)
  let is_normal x =
    let add_rhs _ rhs set = match T.to_var rhs with
      | Some v ->
        if VSet.mem v set || V.lower v != None then raise Not_normal
        else VSet.add v set
      | None -> raise Not_normal
    in
    try
      let allowed_vars = M.fold add_rhs x.transform VSet.empty in
      VSet.subset (formula_free_tmp_vars x.guard) allowed_vars
    with Not_normal -> false

  let equal x y =
    compare x y = 0
    || (VarSet.equal (modifies x) (modifies y)
        && is_normal x && is_normal y
        && equiv x y)

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

    (* Add bindings from left transform for variables that are not written in
       right *)
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

  let simplify tr =
    let f _ term free = VSet.union free (term_free_tmp_vars term) in
    let guard = tr.guard in
    let rhs_vars = M.fold f tr.transform VSet.empty in
    let p x = match V.lower x with
      | Some _ -> true
      | None -> VSet.mem x rhs_vars
    in
    { tr with guard = F.simplify p guard }

  let simplify tr = Log.time "Transition simplification" simplify tr

  let exists p tr =
    let transform = M.filter (fun k _ -> p k) tr.transform in
    let rename = VarMemo.memo (fun v -> V.mk_tmp (Var.show v) (Var.typ v)) in
    let sigma v = match V.lower v with
      | Some var -> T.var (if p var then v else rename var)
      | None -> T.var v
    in
    { transform = transform;
      guard = F.subst sigma tr.guard }

  (* Overapproximate a transition with a transition such that each the right
     hand side of every transformation is a unique variable, and the only free
     temporary variables in the guard are on the right hand side of a
     transformation.  *)
  let normalize tr =
    let fresh v =
      T.var (V.mk_tmp ("normal_" ^ (Var.show v)) (Var.typ v))
    in
    let transform = M.mapi (fun v _ -> fresh v) tr.transform in
    let f (v, t) = F.eq (M.find v tr.transform) t in
    let eqs = F.big_conj (BatEnum.map f (M.enum transform)) in
    let guard =
      F.linearize
        (fun () -> V.mk_tmp "nonlin" TyReal)
        (F.conj tr.guard eqs)
    in
    simplify { guard = guard; transform = transform }

  let normalize tr =
    try
      normalize tr
    with Formula.Timeout ->
      (Log.errorf "Timeout in transition normalization.";
       raise Formula.Timeout)


  let widen_man = ref (NumDomain.polka_loose_manager ())
  let widen x y =
    let phi = to_formula (normalize x) in
    let psi = to_formula (normalize y) in
    let p v = match V.lower v with
      | Some _ -> true
      | None   -> false
    in
    let phi_abstract = F.abstract ~exists:(Some p) (!widen_man) phi in
    let psi_abstract = F.abstract ~exists:(Some p) (!widen_man) psi in
    let widen = F.of_abstract (F.T.D.widen phi_abstract psi_abstract) in
    let fresh v = T.var (V.mk_tmp (Var.show v) (Var.typ v)) in
    let unprime =
      M.of_enum (M.enum y.transform /@ (fun (v,_) -> (Var.prime v, fresh v)))
    in
    let transform =
      M.mapi (fun v _ -> M.find (Var.prime v) unprime) y.transform
    in

    let sigma v = match V.lower v with
      | Some var ->
        begin
          try M.find var unprime
          with Not_found -> T.var v
        end
      | None -> T.var v
    in
    { guard = F.subst sigma widen;
      transform = transform }

  let widen x y =
    try
      if VarSet.equal (modifies x) (modifies y) then widen x y
      else y
    with Formula.Timeout ->
      (Log.errorf "Timeout in widening.";
       raise Formula.Timeout)

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

  let abstract_post man tr prop =
    let phi =
      F.conj
        (F.linearize
           (fun () -> V.mk_tmp "nonlin" TyReal)
           (to_formula tr))
        (F.of_abstract prop)
    in
    let unprime =
      M.enum tr.transform
      /@ (fun (v,_) -> (Var.prime v, T.var (V.mk_var v)))
      |> M.of_enum
    in
    let old =
      VarMemo.memo
        (fun v -> T.var (V.mk_tmp ((Var.show v) ^ "_old") (Var.typ v)))
    in
    let sigma x = match V.lower x with
      | Some v ->
        if M.mem v unprime then M.find v unprime
        else if M.mem v tr.transform then old v
        else T.var x
      | None -> T.var x
    in
    let phi = F.subst sigma phi in
    let phi =
      if Box.manager_is_box man then
        let fv =
          List.map (T.var % V.mk_var)
            (VarSet.elements (formula_free_program_vars phi))
        in
        F.boxify fv phi
      else phi
    in

    let p x = V.lower x != None in
    F.abstract ~exists:(Some p) man phi
end

module Make (Var : Var) = struct
  include Dioid(Var)

  let convex_hull p phi =
    let man = NumDomain.polka_strict_manager () in
    F.of_abstract (F.abstract ~exists:(Some p) man phi)

  (* Iteration operator options *)
  let opt_higher_recurrence = ref true
  let opt_disjunctive_recurrence_eq = ref false
  let opt_recurrence_ineq = ref false
  let opt_higher_recurrence_ineq = ref false
  let opt_unroll_loop = ref false
  let opt_loop_guard = ref (Some convex_hull)
  let opt_polyrec = ref true

  (**************************************************************************)
  (* Implementation of iteration operator *)
  (**************************************************************************)
  module Incr = struct

    (* Polynomials with rational coefficients *)
    module P = Linear.Expr.MakePolynomial(QQ)
    module Gauss = Linear.GaussElim(QQ)(P)
    module Env = Putil.Map.Make(Var)

    (* Closed forms *)
    module Cf = Linear.Affine.LiftMap(Var)(Env)(P)

    let cf_compose cf p =
      let f (dim, coeff) = (dim, P.compose coeff p) in
      Cf.of_enum (BatEnum.map f (Cf.enum cf))
    let k_minus_1 = P.add_term 1 QQ.one (P.const (QQ.negate QQ.one))

    let eval env t =
      match T.to_linterm t with
      | None -> None
      | Some lt ->
        let f (dim, coeff) =
          match dim with
          | AConst -> Cf.const (P.const coeff)
          | AVar (V.TVar _) -> raise Not_found
          | AVar (V.PVar v) ->
            if Env.mem v env then begin
              match Env.find v env with
              | Some cf ->
                Cf.scalar_mul (P.const coeff) (cf_compose cf k_minus_1)
              | None -> raise Not_found
            end else begin
              (* if v isn't in env, it isn't in the domain of the
                 transformation, and so hasn't been modified along the path *)
              Cf.term (AVar v) (P.const coeff)
            end
        in
        try
          Some (Cf.sum (BatEnum.map f (T.Linterm.enum lt)))
        with Not_found -> begin
            logf "Failed to evaluate closed form for %a"
              T.format t;
            logf "Environment: %a"
              (Env.format Show.format<Cf.t option>) env;
            None
          end

    (* Given a polynomial p, compute a polynomial q such that for any k, q(k)
       = p(0) + p(1) + ... + p(k-1) *)
    let polynomial_summation : P.t -> P.t = fun p ->
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

    let summation cf =
      let f (x, p) = (x, polynomial_summation p) in
      Cf.of_enum (BatEnum.map f (Cf.enum cf))

    (* Convert a closed form into a term by instantiating the variable in the
       polynomial coefficients of the closed form *)
    let to_term cf var =
      let open BatEnum in
      let polynomial_term px =
        let to_term (order, cq) = T.mul (T.const cq) (T.exp var order) in
        T.sum (BatEnum.map to_term (P.enum px))
      in
      let to_term (dim, px) = match dim with
        | AVar v -> T.mul (polynomial_term px) (T.var (V.mk_var v))
        | AConst -> polynomial_term px
      in
      T.sum (BatEnum.map to_term (Cf.enum cf))
  end

  module VarMap = Incr.Env

  (* Linear terms with rational efficients *)
  module QQTerm = Linear.Expr.Make(Var)(QQ)

  (* Iteration operator context.  The iteration operator is defined as a
     sequence of iteration context transformers. *)
  type iteration_context =
    { loop : t;  (* Transition representing the loop summary *)
      phi : F.t; (* Formula representing the loop body *)

      (* Induction variables are variables with exact recurrences (defined by
         equalities of the form x' = x + p(y), where p(y) is a
         polynomial in induction variables of lower strata) *)
      induction_vars : Incr.Cf.t option Incr.Env.t;

      (* Variable term representing the loop iteration *)
      loop_counter : T.t }

  (* Hack to simplify control flow when a loop body is unsatisfiable.
     Should't be visible outside this module. *)
  exception Unsat
  exception Undef

  (* Find recurrences of the form x' = x + c *)
  let simple_induction_vars ctx =
    let open Incr in
    let s = new Smt.solver in
    s#assrt (F.to_smt ctx.phi);
    let m = match s#check () with
      | Smt.Unsat -> raise Unsat
      | Smt.Undef -> raise Undef
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
          logf "Found recurrence: %a' = %a + %a"
            Var.format v
            Var.format v
            QQ.format incr;
          let increment = Cf.const (P.add_term 1 incr P.zero) in
          let cf = Cf.add_term (AVar v) P.one increment in
          logf "Closed form: %a" Cf.format cf;
          Some (Cf.add_term (AVar v) P.one increment)
        | Smt.Sat ->
          logf "No recurrence for %a" Var.format v;
          None
        | Smt.Undef ->
          Log.errorf "Timeout in simple induction variable detection!";
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
      let g sum case_var ivl = match sum, Interval.const_of ivl with
        | (Some sum, Some k_ivl) ->
          Some (T.add (T.mul case_var (T.const k_ivl)) sum)
        | (_, _) -> None
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
    | Some rhs_closed ->
      let cf =
        Incr.Cf.add_term (AVar v) Incr.P.one (Incr.summation rhs_closed)
      in
      logf "Closed form for %a: %a"
        Var.format v
        Incr.Cf.format cf;
      Some cf
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

  module AMap = BatMap.Make(Linear.AffineVar(V))
  let farkas equations vars =
    let lambdas =
      List.map (fun _ -> AVar (V.mk_real_tmp "lambda")) equations
    in
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
    let equalities = F.affine_hull ctx.phi vars in
    logf "Extracted equalities:@ %a"
      Show.format<T.Linterm.t list> equalities;
    let (s, coeffs) = farkas equalities vars in
    let get_coeff v = AMap.find (mk_avar v) coeffs in
    (* A variable has a coefficient iff it is involved in an equality. *)
    let has_coeff v = AMap.mem (mk_avar v) coeffs in

    let remove_coeff x coeffs = AMap.remove (AVar (V.mk_var x)) coeffs in
    let assert_zero_coeff v =
      try s#assrt (Smt.mk_eq (get_coeff v) (Smt.const_int 0))
      with Not_found ->
        (* No coefficient assigned to v => we may assume it's zero without
           	   asserting anything *)
        ()
    in
    let find_recurrence v =
      s#push ();

      s#assrt (Smt.mk_eq (get_coeff v) (Smt.const_int 1));
      s#assrt (Smt.mk_eq (get_coeff (Var.prime v)) (Smt.const_int (-1)));

      (* The coefficient of a non-induction variable (other than v) must be
         	 0 *)
      Incr.Env.iter (fun x rhs ->
          match rhs with
          | None -> assert_zero_coeff x
          | Some _ -> ()
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
        (* Remove v & v' terms -- we want the term t such that v' = v + t, and
           we already set the coefficients of v and v'
           appropriately *)
        let coeffs = remove_coeff v (remove_coeff (Var.prime v) coeffs) in
        s#pop ();
        let incr = T.qq_linterm (BatList.enum (AMap.fold f coeffs [])) in
        logf "Found recurrence: %a' = %a + %a"
          Var.format v
          Var.format v
          T.format incr;
        Some incr
    in
    let found_recurrence = ref false in
    let check v rhs =
      match rhs with
      | Some cf -> Some cf
      | None ->
        if has_coeff v && has_coeff (Var.prime v) then begin
          match find_recurrence v with
          | Some rhs ->
            found_recurrence := true;
            closed_form ctx.induction_vars ctx.loop_counter v rhs
          | None -> None
        end
        else
          (* v isn't involved in any equalities => can't satisfy any
             recurrences*)
          None
    in
    let rec fix iv =
      let iv = Incr.Env.mapi check iv in
      if !found_recurrence then begin
        found_recurrence := false;
        fix iv
      end else iv
    in
    { ctx with induction_vars = fix ctx.induction_vars }

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
    let bounds = F.optimize deltas ctx.phi in
    let h tr (v, ivl) =
      let delta =
        try T.sub (M.find v tr.transform) (T.var (V.mk_var v))
        with Not_found -> assert false
      in
      let lower = match Interval.lower ivl with
        | Some bound ->
          F.leq (T.mul ctx.loop_counter (T.const bound)) delta
        | None -> F.top
      in
      let upper = match Interval.upper ivl with
        | Some bound ->
          F.leq delta (T.mul ctx.loop_counter (T.const bound))
        | None -> F.top
      in
      let lo_string = match Interval.lower ivl with
        | Some lo -> (QQ.show lo) ^ " <= "
        | None -> ""
      in
      let hi_string = match Interval.upper ivl with
        | Some hi -> " <= " ^ (QQ.show hi)
        | None -> ""
      in
      logf "Bounds for %a: %s%a'-%a%s"
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

  (* Polyhedral recurrences *)
  let polyrec ctx =
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
    let fresh v = V.mk_tmp ("delta_" ^ (Var.show v)) (Var.typ v) in
    let delta_vars = List.map fresh non_induction in
    let phi =
      List.fold_left2
        (fun v dv d -> F.conj v (F.eq (T.var dv) d))
        ctx.phi
        delta_vars
        deltas
    in
    let delta_map =
      let add m dv v =
        V.Map.add
          dv
          (T.sub (M.find v ctx.loop.transform) (T.var (V.mk_var v)))
          m
      in
      List.fold_left2 add V.Map.empty delta_vars non_induction
    in
    let man = NumDomain.polka_strict_manager () in
    let poly =
      let delta_var_set = VSet.of_enum (BatList.enum delta_vars) in
      let is_induction_var v = match V.lower v with
        | Some var ->
          begin
            try (Incr.Env.find var ctx.induction_vars) != None
            with Not_found -> false
          end
        | None -> false
      in
      let p v =
        VSet.mem v delta_var_set || is_induction_var v
      in
      F.abstract ~exists:(Some p) man phi
    in
    logf "Polyhedron: %a" F.T.D.format poly;
    let recur tcons =
      let open Apron in
      let open Tcons0 in
      let open T.D in
      let t = T.of_apron poly.env tcons.texpr0 in
      match T.to_linterm t with
      | None -> F.top
      | Some lt -> begin
          let p (x,_) = V.Map.mem x delta_map in
          let (deltas, nondeltas) =
            BatEnum.partition p (T.Linterm.var_bindings lt)
          in
          let lhs =
            let f lhs (dv, coeff) =
              T.add lhs (T.mul (T.const coeff) (V.Map.find dv delta_map))
            in
            BatEnum.fold f T.zero deltas
          in
          let rhs =
            let f rhs (v, coeff) = T.add rhs (T.mul (T.const coeff) (T.var v)) in
            let rhs_term =
              BatEnum.fold f (T.const (T.Linterm.const_coeff lt)) nondeltas
            in
            match Incr.eval ctx.induction_vars rhs_term with
            | Some cf -> Incr.to_term (Incr.summation cf) ctx.loop_counter
            | None -> assert false
          in
          let res =
            match tcons.typ with
            | EQ      -> F.eqz (T.add lhs rhs)
            | SUPEQ   -> F.leqz (T.neg (T.add lhs rhs))
            | SUP     -> F.ltz (T.neg (T.add lhs rhs))
            | DISEQ   -> assert false (* impossible *)
            | EQMOD _ -> assert false (* todo *)
          in
          if T.equal lhs T.zero then F.top else begin
            logf "Polyhedral recurrence: %a" F.format res;
            res
          end
        end
    in
    let tcons =
      BatArray.enum (Apron.Abstract0.to_tcons_array man poly.T.D.prop)
    in
    let loop =
      { ctx.loop with guard =
                        F.conj ctx.loop.guard (F.big_conj (BatEnum.map recur tcons)) }
    in
    { ctx with loop = loop }
  let polyrec ctx = Log.time "polyrec" polyrec ctx

  let loop_guard exists ctx =
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
      F.nudge (exists (low (flip VarSet.mem pre_vars)) ctx.phi)
    in
    let post_guard =
      F.nudge (exists (low (flip VarSet.mem post_vars)) ctx.phi)
    in
    let sigma v = match V.lower v with
      | Some x ->
        if VarMap.mem x unprime
        then M.find (VarMap.find x unprime) ctx.loop.transform
        else T.var v
      | None -> assert false (* impossible *)
    in
    let post_guard = F.subst sigma post_guard in
    let penultimate_guard =
      let loop_counter = match T.to_var ctx.loop_counter with
        | Some v -> v
        | None -> assert false
      in
      let p v = V.equal v loop_counter || V.lower v != None in
      let phi = mul ctx.loop (assume pre_guard) in
      let sigma v =
        if V.equal v loop_counter then T.sub (T.var v) T.one
        else T.var v
      in
      logf "penultimate_guard_phi:@\n%a" F.format phi.guard;
      F.subst sigma (exists p (F.linearize (fun () -> V.mk_real_tmp "nonlin")
                                 phi.guard))
    in
    logf "pre_guard:@\n%a" F.format pre_guard;
    logf "post_guard:@\n%a" F.format post_guard;
    logf "penultimate_guard:@\n%a" F.format penultimate_guard;
    let plus_guard =
      F.big_conj (BatList.enum [
          pre_guard;
          post_guard;
          penultimate_guard;
          (F.geq ctx.loop_counter T.one)])
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
              | Some incr -> Incr.to_term incr ctx.loop_counter
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
        logf "Compute symbolic bounds for variable: %a"
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
        logf "Bounds: %a" F.format bounds_formula;
        { transform = M.add v (T.add (T.var (V.mk_var v)) nondet) tr.transform;
          guard = F.conj (formula_of_bounds nondet bounds) tr.guard }
    in
    let loop = Incr.Env.fold g ctx.induction_vars ctx.loop in
    { ctx with loop = loop }


  let star tr =
    logf "Loop body:@\n%a" format tr;
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
    let linear_body =
      F.linearize (fun () -> V.mk_real_tmp "nonlin") (to_formula tr)
    in
    let ctx =
      { induction_vars = induction_vars;
        phi = linear_body;
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

    let loop =
      match !opt_loop_guard with
      | Some ex -> loop_guard ex { ctx with loop = loop }
      | None -> loop
    in
    let loop =
      if !opt_unroll_loop then add one (mul loop tr)
      else loop
    in
    logf "Loop summary: %a" format loop;
    loop

  let star tr =
    try
      star tr
    with
    | Unsat -> one
    | Undef ->
      let mk_nondet v _ =
        T.var (V.mk_tmp ("nondet_" ^ (Var.show v)) (Var.typ v))
      in
      Log.errorf "Gave up in loop computation";
      { guard = F.top;
        transform = M.mapi mk_nondet tr.transform }

  let format_robust formatter tr =
    Format.fprintf formatter
      "{@[<v 0>transform:@;  @[<v 0>%a@]@;guard:@;  @[<v 0>%a@]@]}"
      (ApakEnum.pp_print_enum_nobox
         ~pp_sep:(fun formatter () -> Format.pp_print_break formatter 0 0)
         (fun formatter (lhs, rhs) ->
            Format.fprintf formatter "%a := %a"
              Var.format lhs
              T.format rhs))
      (M.enum tr.transform)
      F.format_robust tr.guard
end
