open Core
open Apak
open Ark
open ArkPervasives
open BatPervasives

include Log.Make(struct let name = "newton" end)

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

module type NewtonDomain = sig
  type t
  type abstract
  val one : t
  val zero : t
  val mul : t -> t -> t
  val add : t -> t -> t
  val equal : t -> t -> t
  val alpha : t -> abstract
  val abstract_star : abstract -> t
  val abstract_equal : t -> t -> t
  val abstract_widen : abstract -> abstract -> abstract
end

module RecurrenceAnalysis (Var : Var) = struct
  include Transition.Make(Var)

  let _ =
    let simplify_dillig =
      F.simplify_dillig_nonlinear (fun () -> V.mk_tmp "nonlin" TyInt)
    in
    F.opt_simplify_strategy := [F.qe_partial; simplify_dillig]

  let get_manager =
    let man = ref None in
    fun () -> match !man with
      | Some m -> m
      | None -> begin
          let m = NumDomain.polka_loose_manager () in
          man := Some m;
          m
        end

  module Base = struct
    type abstract =
      { precondition : F.Synthetic.t;
        postcondition : F.Synthetic.t;
        modified : VarSet.t;
        stratified : (Var.t * T.t) list;
        inequations : (T.t * [ `Leq | `Eq ] * T.t) list;
      }

    let format_abstract formatter abstract =
      Format.fprintf formatter
        "{@[<v 0>mod:@;  @[<v 0>%a@]@;pre:@;  @[<v 0>%a@]@;post:@;  @[<v 0>%a@]@;"
        VarSet.format abstract.modified
        F.Synthetic.pp abstract.precondition
        F.Synthetic.pp abstract.postcondition;
      Format.fprintf formatter
        "recurrences:@;  @[<v 0>%a@;%a@]@;"
        (ApakEnum.pp_print_enum_nobox
           ~pp_sep:(fun formatter () -> Format.pp_print_break formatter 0 0)
           (fun formatter (lhs, rhs) ->
              Format.fprintf formatter "%a' = %a + %a"
                Var.format lhs
                Var.format lhs
                T.format rhs))
        (BatList.enum abstract.stratified)
        (ApakEnum.pp_print_enum_nobox
           ~pp_sep:(fun formatter () -> Format.pp_print_break formatter 0 0)
           (fun formatter (lhs, op, rhs) ->
              Format.fprintf formatter "(%a)' %s (%a) + %a"
                T.format lhs
                (match op with
                 | `Eq -> "="
                 | `Leq -> "<=")
                T.format lhs
                T.format rhs))
        (BatList.enum abstract.inequations)

    let abstract_star ?guard:(guard=F.top) abstract =
      let loop_counter = T.var (V.mk_int_tmp "K") in
      (* In a recurrence environment, absence of a binding for a variable
         indicates that the variable is not modified (i.e., the variable
         satisfies the recurrence x' = x + 0).  We initialize the environment
         to bind None to each modified variable. *)
      let induction_vars =
        VarSet.fold
          (fun v env -> VarMap.add v None env)
          abstract.modified
          VarMap.empty
      in
      let close_sum induction_vars rhs =
        let rec env v =
          match V.lower v with
          | Some var ->
            if VarMap.mem var induction_vars then
              VarMap.find var induction_vars
            else
              Some (Incr.Cf.term (AVar (T.var v)) (Incr.P.const QQ.one))
          | None -> assert false
        in

        (* Substitute closed forms for lower induction vars into the
           right-hand-side *)
        match Incr.eval env rhs with
        | Some rhs_closed -> Some (Incr.summation rhs_closed)
        | None -> None
      in

      (* Close all stratified recurrence equations *)
      let (env, transform) =
        List.fold_left (fun (env, transform) (var, rhs) ->
            match close_sum env rhs with
            | None -> (env, transform)
            | Some close_rhs ->
              let cf =
                Incr.Cf.add_term
                  (AVar (T.var (V.mk_var var)))
                  Incr.P.one
                  close_rhs
              in
              logf "@[Closed form for %a: %a@]"
                Var.format var
                Incr.Cf.format cf;
              let env = VarMap.add var (Some cf) env in
              let transform =
                M.add var (Incr.to_term cf loop_counter) transform
              in
              (env, transform))
          (induction_vars, M.empty)
          abstract.stratified
      in
      (* Non-induction variables get assigned a Skolem constant *)
      let transform =
        VarSet.fold (fun var transform ->
            if M.mem var transform then
              transform
            else
              let nondet =
                V.mk_tmp ("nondet_" ^ (Var.show var)) (Var.typ var)
              in
              M.add var (T.var nondet) transform)
          abstract.modified
          transform
      in
      (* Substitution that replaces every modified variable x with (x' - x) *)
      let delta_subst v = match V.lower v with
        | Some pv -> begin
            try T.sub (M.find pv transform) (T.var v)
            with Not_found -> T.var v
          end
        | _ -> assert false
      in
      (* Close all linear recurrence inequations *)
      let ineqs =
        abstract.inequations |> List.map (fun (lhs, op, rhs) ->
            match close_sum env rhs with
            | None -> F.top
            | Some close_rhs ->
              let cf = Incr.to_term close_rhs loop_counter in
              let lhs_delta = T.subst delta_subst lhs in
              match op with
              | `Leq -> F.leq lhs_delta cf
              | `Eq -> F.eq lhs_delta cf)
        |> BatList.enum |> F.big_conj
      in
      let postcondition =
        let sigma v = match V.lower v with
          | Some var ->
            begin
              try M.find var transform
              with Not_found -> T.var v
            end
          | _ -> assert false
        in
        F.formula_of_synthetic abstract.postcondition |> F.subst sigma
      in
      (* The next-to-last iterate must satisfy the pre-condition of the loop *)
      let penultimate_guard =
        let prev_counter = T.sub loop_counter T.one in
        (* maps each variable to a term representing its value in the
           penultimate iteration *)
        let prev_map =
          VarMap.fold (fun var rhs prev_map ->
              match rhs with
              | Some cf -> M.add var (Incr.to_term cf prev_counter) prev_map
              | None ->
                let nondet =
                  V.mk_tmp ("nondet_" ^ (Var.show var)) (Var.typ var)
                in
                M.add var (T.var nondet) prev_map)
            env
            M.empty
        in
        let rec prev v =
          match V.lower v with
          | Some var ->
            (try M.find var prev_map
             with Not_found -> T.var v)
          | None -> assert false
        in
        let delta_prev_subst v = match V.lower v with
          | Some pv -> begin
              try T.sub (M.find pv prev_map) (T.var v)
              with Not_found -> T.var v
            end
          | _ -> assert false
        in
        (* Close all linear recurrence inequations to get constraints on the
           next-to-last iterate. *)
        let ineqs =
          abstract.inequations |> List.map (fun (lhs, op, rhs) ->
            match close_sum env rhs with
            | None -> F.top
            | Some close_rhs ->
              let cf = Incr.to_term close_rhs prev_counter in
              let lhs_delta = T.subst delta_prev_subst lhs in
              match op with
              | `Leq -> F.leq lhs_delta cf
              | `Eq -> F.eq lhs_delta cf)
          |> BatList.enum |> F.big_conj
        in
        let prev_precondition =
          abstract.precondition
          |> F.Synthetic.project (fun v -> V.lower v != None)
          |> F.formula_of_synthetic
          |> F.subst prev
        in
        F.conj ineqs prev_precondition
      in
      let precondition =
        F.formula_of_synthetic abstract.precondition
      in
      let plus_guard =
        F.big_conj (BatList.enum [
            ineqs;
            precondition;
            guard;
            postcondition;
            penultimate_guard;
            (F.geq loop_counter T.one)])
      in
      let zero_guard =
        let eq (v, t) = F.eq (T.var (V.mk_var v)) t in
        F.conj
          (F.eqz loop_counter)
          (F.big_conj (BatEnum.map eq (M.enum transform)))
      in
      { transform = transform;
        guard = F.disj plus_guard zero_guard }

    let stratified_recurrence_equations modified body =
      let mk_avar v = AVar (V.mk_var v) in
      let primed_vars = VarSet.map Var.prime modified in
      (* remove constant dimensions *)
      (*
      let body =
        T.D.exists
          man
          (fun v ->
             let ivl =
               Apron.Abstract0.bound_texpr
                 man
                 body.T.D.prop
                 (T.to_apron body.T.D.env (T.var v))
               |> Interval.of_apron
             in
             Interval.const_of ivl = None)
          body
      in
*)

      let vars = BatList.of_enum (F.Synthetic.symbols body) in
      let equalities = F.Synthetic.affine_hull body in
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
      let find_recurrence v non_induction =
        s#push ();

        s#assrt (Smt.mk_eq (get_coeff v) (Smt.const_int 1));
        s#assrt (Smt.mk_eq (get_coeff (Var.prime v)) (Smt.const_int (-1)));

        (* The coefficient of a non-induction variable (other than v) must be
           0 *)
        non_induction |> VarSet.iter (fun x ->
            if not (Var.equal x v) then
              assert_zero_coeff x);

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
      let rec fix equations vars =
        let found_recurrence = ref false in
        let non_induction = ref vars in
        let equations =
          VarSet.fold (fun v equations ->
              if has_coeff v && has_coeff (Var.prime v) then
                match find_recurrence v vars with
                | None -> equations
                | Some rhs ->
                  found_recurrence := true;
                  non_induction := VarSet.remove v (!non_induction);
                  (v, rhs)::equations
              else
                equations)
            vars
            equations
        in
        if !found_recurrence then fix equations (!non_induction)
        else equations
      in
      List.rev (fix [] modified)

    let linear_recurrence_inequations induction_vars non_induction_vars body =
      let prime_vars =
        VSet.fold
          (fun v set -> match V.lower v with
             | Some v -> VarSet.add (Var.prime v) set
             | None -> assert false)
          induction_vars
          (VarSet.map Var.prime non_induction_vars)
      in

      (* each non-induction variable x is associated with a delta variable,
         defined to be the difference between x' and x *)
      let delta_vars =
        VarSet.fold (fun v map ->
            VarMap.add v (V.mk_tmp ("delta_" ^ (Var.show v)) (Var.typ v)) map)
          non_induction_vars
          VarMap.empty
      in
      let rev_delta_vars = (* reverse mapping of delta_vars *)
        VarMap.fold
          (fun var delta rev -> V.Map.add delta var rev)
          delta_vars
          V.Map.empty
      in

      (* For every non-induction var x, substitute x -> x' - delta(x) in the
         loop body.  This produces a formula equivalent to
            phi /\ { delta(y) = y'-y : y is a non-induction var }
         but with pre-state variables projected out.
      *)
      let phi =
        let delta_subst v = match v with
          | V.PVar pv when VarMap.mem pv delta_vars ->
            T.sub
              (T.var (V.mk_var (Var.prime pv)))
              (T.var (VarMap.find pv delta_vars))
          | _ -> T.var v
        in
        let rewrite = F.subst delta_subst in
        F.atoms_of_synthetic body
        |> List.map rewrite
        |> F.synthetic_of_atoms
      in
      let hull =
        let is_induction_var v = VSet.mem v induction_vars in
        (* Project all variables except the delta vars & induction vars *)
        let p v =
          match V.lower v with
          | Some v -> not (VarSet.mem v prime_vars)
          | None -> true
        in
        F.Synthetic.project p phi
      in
      let recur phi =
        let alg = function
          | OVar v ->
            if V.Map.mem v rev_delta_vars then
              Some (T.var (V.mk_var (V.Map.find v rev_delta_vars)), T.zero)
            else
              Some (T.zero, T.var v)
          | OConst k -> Some (T.zero, T.const k)
          | OAdd (Some (lhs,rhs), Some (lhs',rhs')) ->
            Some (T.add lhs lhs', T.add rhs rhs')
          | OMul (Some (lhs,rhs), Some (lhs',rhs')) ->
            begin
              match T.to_const lhs, T.to_const lhs'  with
              | Some lhs, Some lhs' when QQ.equal lhs QQ.zero
                                      && QQ.equal lhs' QQ.zero ->
                Some (T.zero, T.mul rhs rhs')
              | Some lhs, _ when QQ.equal lhs QQ.zero ->
                begin match T.to_const rhs with
                  | Some _ -> Some (T.mul rhs lhs', T.mul rhs rhs')
                  | None -> None
                end
              | (_, Some lhs') when QQ.equal lhs' QQ.zero ->
                begin match T.to_const rhs' with
                  | Some _ -> Some (T.mul rhs' lhs, T.mul rhs' rhs)
                  | None -> None
                end
              | (_, _) -> None
            end
          | ODiv (Some (lhs,rhs), Some (lhs',rhs')) ->
            begin
              match T.to_const lhs, T.to_const lhs'  with
              | Some lhs, Some lhs' when QQ.equal lhs QQ.zero
                                      && QQ.equal lhs' QQ.zero ->
                Some (T.zero, T.div rhs rhs')
              | (_, Some klhs') when QQ.equal klhs' QQ.zero ->
                begin match T.to_const rhs' with
                  | Some _ -> Some (T.div lhs lhs', T.div rhs rhs')
                  | None -> None
                end
              | (_, _) -> None
            end
          | OMod (Some (lhs,rhs), Some (lhs',rhs')) ->
            begin
              match T.to_const lhs, T.to_const lhs'  with
              | Some lhs, Some lhs' when QQ.equal lhs QQ.zero
                                      && QQ.equal lhs' QQ.zero ->
                Some (T.zero, T.modulo rhs rhs')
              | (_, _) -> None
            end
          | _ -> None
        in

        let (`Comparison (cmp, s, t)) = F.destruct_atom phi in
        match T.eval alg (T.sub s t) with
        | Some (lhs, rhs) when T.to_const lhs = None ->
          let cmp = match cmp with
            | `Eq -> `Eq
            | `Leq | `Lt -> `Leq
          in
          Some (lhs, cmp, T.neg rhs)
        | _ -> None
      in
      BatList.filter_map recur (F.atoms_of_synthetic hull)

    let alpha_polyhedron abstract_body modified =
      let unprime =
        VarMap.of_enum (VarSet.enum modified /@ (fun v -> (Var.prime v, v)))
      in
      let pre_guard =
        let pre_vars =
          F.formula_of_synthetic abstract_body
          |> formula_free_vars
          |> VSet.filter (fun v -> match V.lower v with
              | Some v -> not (VarMap.mem v unprime)
              | None -> assert false)
        in
        F.Synthetic.project (flip VSet.mem pre_vars) abstract_body
      in
      let post_guard =
        abstract_body
        |> F.Synthetic.project (fun v -> match V.lower v with
            | Some v ->
              (* either post-var or unmodified pre-var *)
              not (VarSet.mem v modified)
            | None -> assert false)
        |> F.Synthetic.rename (fun v ->
            match V.lower v with
            | Some v ->
              if VarMap.mem v unprime then
                V.mk_var (VarMap.find v unprime)
              else
                V.mk_var v
            | None -> assert false)
      in
      let stratified =
        stratified_recurrence_equations
          modified
          abstract_body
      in
      let induction_vars =
        List.fold_left
          (fun set (iv, _) -> VSet.add (V.mk_var iv) set)
          VSet.empty
          stratified
      in
      let non_induction_vars =
        List.fold_left
          (fun niv (iv, _) -> VarSet.remove iv niv)
          modified
          stratified
      in
      let inequations =
        linear_recurrence_inequations
          induction_vars
          non_induction_vars
          abstract_body
      in
      { precondition = pre_guard;
        postcondition = post_guard;
        modified = modified;
        stratified = stratified;
        inequations = inequations }

    let alpha_formula body modified =
      let abstract_body =
        F.abstract_synthetic
          V.mk_tmp
          ~exists:(fun v -> V.lower v != None)
          body
      in
      alpha_polyhedron abstract_body modified

    let alpha tr =
      let modified = VarSet.of_enum (M.keys tr.transform) in
      alpha_formula (to_formula tr) modified

    let abstract_vars abstract =
      VarSet.union
        (formula_free_program_vars (F.formula_of_synthetic abstract.precondition))
        (formula_free_program_vars (F.formula_of_synthetic abstract.postcondition))
      |> VarSet.union (VarSet.map Var.prime abstract.modified)
      |> List.fold_right (fun (v, rhs) vars ->
          VarSet.union (VarSet.add v vars) (term_free_program_vars rhs))
        abstract.stratified
      |> List.fold_right (fun (lhs, _, rhs) vars ->
          VarSet.union
            (term_free_program_vars lhs)
            (VarSet.union (term_free_program_vars rhs) vars))
        abstract.inequations

    let hull_of_abstract abstract =
      let prime = Var.prime in
      let eq_constraints =
        abstract.stratified |> List.map (fun (v, rhs) ->
            F.eq
              (T.var (V.mk_var (prime v)))
              (T.add (T.var (V.mk_var v)) rhs))
      in
      let ineq_constraints =
        let primify v = match V.lower v with
          | Some pv -> T.var (V.mk_var (prime pv))
          | None -> assert false
        in
        abstract.inequations |> List.map (fun (lhs, op, rhs) ->
            match op with
            | `Eq -> F.eq (T.subst primify lhs) (T.add lhs rhs)
            | `Leq -> F.leq (T.subst primify lhs) (T.add lhs rhs))
      in
      let postcondition =
        let postify v = match V.lower v with
          | Some pv ->
            if VarSet.mem pv abstract.modified then
              T.var (V.mk_var (prime pv))
            else
              T.var v
          | None -> assert false
        in
        List.map (F.subst postify) (F.atoms_of_synthetic abstract.postcondition)
      in
      let precondition = F.atoms_of_synthetic abstract.precondition in
      F.synthetic_of_atoms
        (eq_constraints@ineq_constraints@postcondition@precondition)

    module TMap = Putil.Map.Make(T)

    let abstract_equal x y =
      F.Synthetic.equal (hull_of_abstract x) (hull_of_abstract y)

    let abstract_widen x y =
      let body = F.Synthetic.widen (hull_of_abstract x) (hull_of_abstract y) in
      let modified = VarSet.union x.modified y.modified in
      alpha_polyhedron body modified

    let abstract_join x y =
      let body =
        F.Synthetic.simple_join (hull_of_abstract x) (hull_of_abstract y)
      in
      let modified = VarSet.union x.modified y.modified in
      alpha_polyhedron body modified
  end

  module Split = struct
    type abstract =
      | Split of (F.t * abstract * abstract) list
      | Leaf of Base.abstract

    let rec format_abstract formatter abstract =
      let pp_split formatter (predicate, first, second) =
        Format.fprintf formatter "@[<v 2>Split %a@;%a@;%a@]"
          F.format predicate
          format_abstract first
          format_abstract second
      in
      match abstract with
      | Leaf base -> Base.format_abstract formatter base
      | Split [split] -> pp_split formatter split
      | Split xs ->
        Format.fprintf formatter "@[<v 2>And %a@]"
          (ApakEnum.pp_print_enum
             ~pp_sep:(fun formatter () -> Format.pp_print_break formatter 0 0)
             pp_split)
          (BatList.enum xs)

    let tr_of_body body modified =
      let transform =
        let nondet v =
          T.var (V.mk_tmp ("nondet_" ^ (Var.show v)) (Var.typ v))
        in
        VarSet.fold
          (fun v transform -> M.add v (nondet v) transform)
          modified
          M.empty
      in
      let prime_map =
        VarSet.fold (fun v prime_map ->
            M.add (Var.prime v) (M.find v transform) prime_map)
          modified
          M.empty
      in
      let sigma v = match V.lower v with
        | Some pv ->
          begin
            try M.find pv prime_map
            with Not_found -> T.var v
          end
        | None -> assert false
      in
      { guard = F.subst sigma body;
        transform = transform }

    let rec split_modified = function
      | Leaf abstract -> abstract.Base.modified
      | Split [] -> assert false
      | Split ((_, first, _)::_) -> split_modified first

    module FormulaSet = Putil.Set.Make(F)

    let alpha_formula_split body modified predicates =
      let lin_body =
        F.linearize_trivial (fun () -> V.mk_real_tmp "nonlin") body
      in
      let postify =
        F.subst (fun v -> match V.lower v with
            | Some pv ->
              if VarSet.mem pv modified then
                T.var (V.mk_var (Var.prime pv))
              else
                T.var v
            | None -> assert false)
      in
      let s = new Smt.solver in
      s#assrt (F.to_smt lin_body);
      let sat_modulo_tr phi =
        s#push ();
        s#assrt (F.to_smt phi);
        let res = s#check () in
        s#pop ();
        res
      in
      let is_split_predicate phi =
        (sat_modulo_tr phi = Smt.Sat)
        && (sat_modulo_tr (F.negate phi) = Smt.Sat)
      in

      let split =
        predicates |> BatList.filter_map (fun phi ->
            if is_split_predicate phi then
              let not_phi = F.negate phi in
              let post_phi = postify phi in
              let post_not_phi = postify not_phi in
              let phi_body = F.conj phi body in
              let not_phi_body = F.conj not_phi body in
              if sat_modulo_tr (F.conj phi post_not_phi) = Smt.Unsat then
                (* {phi} tr {phi} -> tr* = ([not phi]tr)*([phi]tr)* *)
                let left_abstract =
                  Base.alpha_formula not_phi_body modified
                in
                let right_abstract =
                  Base.alpha_formula phi_body modified
                in
                Some (not_phi, Leaf left_abstract, Leaf right_abstract)
              else if sat_modulo_tr (F.conj not_phi post_phi) = Smt.Unsat then
                (* {not phi} tr {not phi} -> tr* = ([phi]tr)*([not phi]tr)* *)
                let left_abstract =
                  Base.alpha_formula phi_body modified
                in
                let right_abstract =
                  Base.alpha_formula not_phi_body modified
                in
                Some (phi, Leaf left_abstract, Leaf right_abstract)
              else
                None
            else
              None)
      in
      match split with
      | [] -> Leaf (Base.alpha_formula body modified)
      | xs -> Split xs

  (* tree-style split predicates *)
(*
      let rec go predicates body =
        let s = new Smt.solver in
        let sat_modulo_tr phi =
          s#push ();
          s#assrt (F.to_smt phi);
          let res = s#check () in
          s#pop ();
          res
        in
        s#assrt (F.to_smt body);
        match predicates with
        | [] -> Leaf (Base.alpha_formula body modified)
        | (phi::predicates) ->
          let not_phi = F.negate phi in
          if (sat_modulo_tr phi = Smt.Sat) && (sat_modulo_tr not_phi = Smt.Sat)
          then begin
            logf "Splitting on predicate: %a" F.format phi;
            let post_phi = postify phi in
            let post_not_phi = postify not_phi in
            let phi_body = F.conj phi body in
            let not_phi_body = F.conj not_phi body in
            if sat_modulo_tr (F.conj phi post_not_phi) = Smt.Unsat then
              (* {phi} tr {phi} -> tr* = ([not phi]tr)*([phi]tr)* *)
              let left_abstract = go predicates not_phi_body in
              let right_abstract = go predicates phi_body in
              Split [(phi, left_abstract, right_abstract)]
            else if sat_modulo_tr (F.conj not_phi post_phi) = Smt.Unsat then
              (* {not phi} tr {not phi} -> tr* = ([phi]tr)*([not phi]tr)* *)
              let left_abstract = go predicates phi_body in
              let right_abstract = go predicates not_phi_body in
              Split [(not_phi, left_abstract, right_abstract)]
            else
              go predicates body
          end else
            go predicates body
      in
      go predicates body
*)

    let rec abstract_star ?guard:(guard=F.top) abstract =
      let abstract_star_split (predicate, first, second) =
        mul
          (abstract_star ~guard:(F.conj guard predicate) first)
          (abstract_star ~guard:(F.conj guard (F.negate predicate)) second)
      in
      match abstract with
      | Leaf base -> Base.abstract_star ~guard base
      | Split [] -> assert false
      | Split (x::xs) ->
        List.fold_left
          meet
          (abstract_star_split x)
          (List.map abstract_star_split xs)

    let alpha tr =
      let modified = VarSet.of_enum (M.keys tr.transform) in
      let prime_modified = VarSet.map Var.prime modified in
      let body = to_formula tr in
      let alg = function
        | OAnd (xs, ys) | OOr (xs, ys) -> FormulaSet.union xs ys
        | OAtom atom ->
          let pre_state_linear_term t =
            VSet.is_empty (term_free_tmp_vars t)
            && not (VarSet.exists
                      (flip VarSet.mem prime_modified)
                      (term_free_program_vars t))
            && (T.to_linterm t != None)
          in
          begin match atom with
            | LeqZ t when pre_state_linear_term t ->
              FormulaSet.singleton (F.leqz t)
            | LtZ t when pre_state_linear_term t ->
              FormulaSet.singleton (F.ltz t)
            | EqZ t when pre_state_linear_term t ->
              FormulaSet.singleton (F.eqz t)
            | _ -> FormulaSet.empty
          end
      in
      let predicates =
        FormulaSet.fold (fun phi predicates ->
            if FormulaSet.mem (F.negate phi) predicates then
              predicates
            else
              FormulaSet.add phi predicates)
          (F.eval alg body)
          FormulaSet.empty
        |> FormulaSet.elements
      in
      alpha_formula_split body modified predicates

    let rec abstract_equal x y =
      match x, y with
      | Leaf x, Leaf y -> Base.abstract_equal x y
      | Split xs, Split ys ->
        let rec split_equal (px, lx, rx) (py, ly, ry) =
          F.equal px py
          && abstract_equal lx ly
          && abstract_equal rx ry
        in
        begin
          try
            BatList.for_all2 split_equal xs ys
          with Invalid_argument _ -> false
        end
      | _, _ -> false

    let rec abstract_join x y =
      let cons x abstract = match abstract with
        | Split xs -> Split (x::xs)
        | Leaf _ -> Split [x]
      in
      match x, y with
      | Leaf x, Leaf y -> Leaf (Base.abstract_join x y)
      | Split xs, Split ys ->
        let rec go xs ys = match xs, ys with
          | (px, lx, rx)::xs, (py, ly, ry)::ys when F.compare px py = 0 ->
            cons (px, abstract_join lx ly, abstract_join rx ry) (go xs ys)
          | (px, lx, rx)::xs, (py, ly, ry)::ys when F.compare px py < 0 ->
            begin
              match abstract_join lx rx with
              | Split xs' -> go (xs'@xs) ys
              | Leaf x when BatList.is_empty xs ->
                abstract_join (Leaf x) (abstract_join ly ry)
              | Leaf x -> go xs ((py, ly, ry)::ys)
            end
          | (px, lx, rx)::xs, (py, ly, ry)::ys ->
            begin
              match abstract_join ly ry with
              | Split ys' -> go xs (ys'@ys)
              | Leaf y when BatList.is_empty ys ->
                abstract_join (abstract_join lx rx) (Leaf y)
              | Leaf y -> go ((px, lx, rx)::xs) ys
            end
          | [], _ | _, [] -> assert false
        in
        go xs ys
      | Leaf x, Split ((_,ly,ry)::ys) ->
        abstract_join (Leaf x) (abstract_join ly ry)
      | Split ((_,lx,rx)::ys), Leaf y->
        abstract_join (abstract_join lx rx) (Leaf y)
      | Split [], Leaf _ | Leaf _, Split [] -> assert false

    let rec abstract_widen x y =
      match x, y with
      | Leaf x, Leaf y -> Leaf (Base.abstract_widen x y)
      | Split xs, Split ys ->
        let rec go xs ys = match xs, ys with
          | (px, lx, rx)::xs, (py, ly, ry)::ys when F.compare px py = 0 ->
            (px, abstract_widen lx ly, abstract_widen rx ry)::(go xs ys)
          | (px, lx, rx)::xs, (py, ly, ry)::ys when F.compare px py < 0 ->
            go xs ((py, ly, ry)::ys)
          | (px, lx, rx)::xs, (py, ly, ry)::ys ->
            go ((px, lx, rx)::xs) ys
          | [], _ | _, [] -> []
        in
        begin
          match go xs ys with
          | [] -> begin match xs, ys with
              | (px, lx, rx)::_, (py, ly, ry)::_ ->
                abstract_widen (abstract_join lx rx) (abstract_join ly ry)
              | _ -> assert false
            end
          | cases -> Split cases
        end
      | Leaf x, Split ((_,ly,ry)::ys) ->
        abstract_widen (Leaf x) (abstract_join ly ry)
      | Split ((_,lx,rx)::ys), Leaf y->
        abstract_join (abstract_join lx rx) (Leaf y)
      | Split [], Leaf _ | Leaf _, Split [] -> assert false
  end

  let abstract_star = Split.abstract_star

  let alpha tr =
    if !Cra.K.opt_split_loops then
      Split.alpha tr
    else
      Split.Leaf (Base.alpha tr)

  let format_abstract = Split.format_abstract

  let abstract_widen = Split.abstract_widen

  let abstract_equal = Split.abstract_equal

  let star x =
    let abstract = alpha x in
    let res = abstract_star abstract in
    logf "Body:@\n @[%a@]" format x;
    logf "Abstract:@\n @[%a@]" Split.format_abstract abstract;
    logf "Result:@\n @[%a@]" format res;
    res

  (* Compute the post-condition of a transition *)
  let range tr =
    (* replace modified pre-state variables with skolem constants *)
    let havoc_pre v = match V.lower v with
      | Some pv ->
        if M.mem pv tr.transform then
          T.var (V.mk_tmp ("fresh_" ^ (Var.show pv)) (Var.typ pv))
        else
          T.var v
      | None -> T.var v
    in
    M.fold (fun lhs rhs range ->
        F.conj (F.eq (T.var (V.mk_var lhs)) (T.subst havoc_pre rhs)) range)
      tr.transform
      (F.subst havoc_pre tr.guard)

  let range_hull tr =
    F.abstract
      ~exists:(Some (fun v -> V.lower v != None))
      (get_manager ())
      (range tr)

  let domain_hull tr =
    F.abstract
      ~exists:(Some (fun v -> V.lower v != None))
      (get_manager ())
      tr.guard

  let opt_star_lc_rec = ref true
  let star_lc left_context tr =
    if !opt_star_lc_rec then
      let alpha_left left =
        alpha { tr with guard = F.conj tr.guard (range left) }
      in
      let rec fix body =
        let loop = abstract_star body in
        let next_body = alpha_left (mul left_context loop) in
        if abstract_equal body next_body then
          loop
        else
          fix (abstract_widen body next_body)
      in
      fix (alpha_left left_context)
    else
      let rec fix pre =
        let body =
          alpha { tr with guard = F.conj tr.guard (F.of_abstract pre) }
        in
        let loop = abstract_star body in
        let post = range_hull (mul left_context loop) in
        if T.D.equal pre post then
          loop
        else
          fix (T.D.widen pre post)
      in
      fix (range_hull left_context)

  let star_rc right_context tr =
    let sigma_tmp =
      Memo.memo (fun (_, typ, name) -> T.var (V.mk_tmp name typ))
    in
    let sigma v = match v with
      | V.PVar var -> begin
          try M.find var tr.transform
          with Not_found -> T.var v
        end
      | V.TVar (id, typ, name) -> sigma_tmp (id, typ, name)
    in
    if !opt_star_lc_rec then
      let alpha_right right =
        alpha { tr with guard = F.conj tr.guard (F.subst sigma right.guard) }
      in
      let rec fix body =
        let loop = abstract_star body in
        let next_body = alpha_right (mul loop right_context) in
        if abstract_equal body next_body then
          loop
        else
          fix (abstract_widen body next_body)
      in
      fix (alpha_right right_context)
    else
      let rec fix pre =
        let body =
          alpha { tr with
                  guard = F.conj tr.guard (F.subst sigma (F.of_abstract pre)) }
        in
        let loop = abstract_star body in
        let post = domain_hull (mul loop right_context) in
        if T.D.equal pre post then
          loop
        else
          fix (T.D.widen pre post)
      in
      fix (domain_hull right_context)
end

(*******************************************************************************
 * Newtonian Program Analysis via Tensor product
 ******************************************************************************)
type value = Cra.value =
  | VVal of Var.t
  | VPos of Var.t
  | VWidth of Var.t

module K = struct
  module Voc = Cra.V
  include RecurrenceAnalysis(Voc)

  let project tr =
    let is_global v = Var.is_global (Cra.var_of_value v) in
    exists is_global tr

  (* Transpose a transition formula (intuitively, swap the primed and unprimed
     variables). *)
  let transpose tr =
    (* The transform of the transpose is obtained by mapping each variable in
       tr's transform to a fresh Skolem constant, which will represent the
       value of that variable in the pre-state.  (After the transform, a
       variable which appears in the RHS of a transform or a guard refers to
       the post-state). *)
    let transform =
      let fresh_skolem v =
        T.var (V.mk_tmp ("fresh_" ^ (Voc.show v)) (Voc.typ v))
      in
      M.fold
        (fun v _ transform -> M.add v (fresh_skolem v) transform)
        tr.transform
        M.empty
    in

    (* Replace every variable in tr's transform with its Skolem constant *)
    let substitution = function
      | V.PVar v when M.mem v transform -> M.find v transform
      | v -> T.var v
    in

    (* Apply substitution to the guard & conjoin with equations from tr's
       transform *)
    let guard =
      let transform_equations =
        M.enum tr.transform
        /@ (fun (v, rhs) ->
            F.eq (T.var (V.mk_var v)) (T.subst substitution rhs))
        |> F.big_conj
      in
      F.conj transform_equations (F.subst substitution tr.guard)
    in
    { transform; guard }

  let top_local block =
    let open CfgIr in
    let file = get_gfile () in
    let func = lookup_function block file in
    (BatEnum.append
       (BatEnum.append (BatList.enum func.formals) (BatList.enum func.locals))
       (BatList.enum file.vars))
    /@ (fun vi ->
        let v = VVal (Var.mk vi) in
        assign v (T.var (V.mk_tmp "havoc" (Voc.typ v))))
    |> BatEnum.reduce mul
end

let var_of_value = function
  | VVal v | VPos v | VWidth v -> v
let map_value f = function
  | VVal v -> VVal (f v)
  | VPos v -> VPos (f v)
  | VWidth v -> VWidth (f v)

type ptr_term =
  { ptr_val : K.T.t;
    ptr_pos : K.T.t;
    ptr_width : K.T.t }

type term =
  | TInt of K.T.t
  | TPointer of ptr_term

let tr_typ = Cra.tr_typ

let int_binop op left right =
  let open K in
  match op with
  | Add -> T.add left right
  | Minus -> T.sub left right
  | Mult -> T.mul left right
  | Div -> T.idiv left right
  | Mod -> T.modulo left right
  | _ -> T.var (V.mk_tmp "havoc" TyInt)

let term_binop op left right = match left, op, right with
  | (TInt left, op, TInt right) ->
    TInt (int_binop op left right)
  | (TPointer ptr, Add, TInt offset)
  | (TInt offset, Add, TPointer ptr) ->
    let p =
      { ptr_val = int_binop Add ptr.ptr_val offset;
        ptr_pos = int_binop Add ptr.ptr_pos offset;
        ptr_width = ptr.ptr_width }
    in
    TPointer p
  | (TPointer ptr, Minus, TInt offset) ->
    let p =
      { ptr_val = int_binop Minus ptr.ptr_val offset;
        ptr_pos = int_binop Minus ptr.ptr_pos offset;
        ptr_width = ptr.ptr_width }
    in
    TPointer p
  | (TInt offset, Minus, TPointer ptr) ->
    let p =
      { ptr_val = int_binop Minus offset ptr.ptr_val;
        ptr_pos = int_binop Minus offset ptr.ptr_pos;
        ptr_width = ptr.ptr_width }
    in
    TPointer p
  | (TPointer left, op, TInt right) ->
    TInt (int_binop op left.ptr_val right)
  | (TInt left, op, TPointer right) ->
    TInt (int_binop op left right.ptr_val)
  | (TPointer left, op, TPointer right) ->
    TInt (int_binop op left.ptr_val right.ptr_val)

let typ_has_offsets typ = is_pointer_type typ || typ = Concrete Dynamic

let tr_expr expr =
  let open K in
  let alg = function
    | OHavoc typ -> TInt (T.var (V.mk_tmp "havoc" (tr_typ typ)))
    | OConstant (CInt (k, _)) -> TInt (T.int (ZZ.of_int k))
    | OConstant (CFloat (k, _)) -> TInt (T.const (QQ.of_float k))
    | OConstant (CString str) ->
      TPointer { ptr_val = T.var (V.mk_tmp "tr" TyInt);
                 ptr_width = T.int (ZZ.of_int (String.length str));
                 ptr_pos = T.zero }
    | OCast (_, expr) -> expr
    | OBinaryOp (a, op, b, _) -> term_binop op a b

    | OUnaryOp (Neg, TInt a, _) -> TInt (T.neg a)
    | OUnaryOp (Neg, TPointer a, _) -> TInt (T.neg a.ptr_val)
    | OAccessPath (Variable v) ->
      if typ_has_offsets (Var.get_type v) then
        TPointer { ptr_val = T.var (V.mk_var (VVal v));
                   ptr_width = T.var (V.mk_var (VWidth v));
                   ptr_pos = T.var (V.mk_var (VPos v)) }
      else TInt (T.var (V.mk_var (VVal v)))

    | OAddrOf _ ->
      (* Todo: width and pos aren't correct. *)
      TPointer { ptr_val = T.var (V.mk_tmp "tr" TyInt);
                 ptr_width = T.one;
                 ptr_pos = T.zero }

    (* No real translations for anything else -- just return a free var "tr"
       (which just acts like a havoc). *)
    | OUnaryOp (_, _, typ) -> TInt (T.var (V.mk_tmp "tr" (tr_typ typ)))
    | OBoolExpr _ -> TInt (T.var (V.mk_int_tmp "tr"))
    | OAccessPath ap -> TInt (T.var (V.mk_tmp "tr" (tr_typ (AP.get_type ap))))
    | OConstant _ -> TInt (T.var (V.mk_int_tmp "tr"))
  in
  Expr.fold alg expr

let tr_expr_val expr = match tr_expr expr with
  | TInt x -> x
  | TPointer x -> x.ptr_val

let tr_bexpr bexpr =
  let open K in
  let alg = function
    | Core.OAnd (a, b) -> F.conj a b
    | Core.OOr (a, b) -> F.disj a b
    | Core.OAtom (pred, x, y) ->
      let x = tr_expr_val x in
      let y = tr_expr_val y in
      begin
        match pred with
        | Lt -> F.lt x y
        | Le -> F.leq x y
        | Eq -> F.eq x y
        | Ne -> F.disj (F.lt x y) (F.gt x y)
      end
  in
  Bexpr.fold alg bexpr

let weight def =
  let open K in
  match def.dkind with
  | Assume phi -> assume (tr_bexpr phi)
  | Assign (lhs, rhs) ->
    if typ_has_offsets (Var.get_type lhs) then begin
      match tr_expr rhs with
      | TPointer rhs ->
        BatList.reduce mul [
          assign (VVal lhs) rhs.ptr_val;
          assign (VPos lhs) rhs.ptr_pos;
          assign (VWidth lhs) rhs.ptr_width;
        ]
      | TInt tint -> begin
          (match Var.get_type lhs, rhs with
           | (_, Havoc _) | (Concrete Dynamic, _) -> ()
           | _ -> Log.errorf "Ill-typed pointer assignment: %a" Def.format def);
          BatList.reduce mul [
            assign (VVal lhs) tint;
            assign (VPos lhs) (T.var (V.mk_tmp "type_err" TyInt));
            assign (VWidth lhs) (T.var (V.mk_tmp "type_err" TyInt))
          ]
        end
    end else assign (VVal lhs) (tr_expr_val rhs)
  | Store (lhs, _) ->
    (* Havoc all the variables lhs could point to *)
    let open Pa in
    let add_target memloc tr = match memloc with
      | (MAddr v, offset) ->
        if typ_has_offsets (Var.get_type (v,offset)) then begin
          BatList.reduce mul [
            tr;
            assign (VVal (v,offset)) (T.var (V.mk_tmp "store" TyInt));
            assign (VPos (v,offset)) (T.var (V.mk_tmp "store" TyInt));
            assign (VWidth (v,offset)) (T.var (V.mk_tmp "store" TyInt))
          ]
        end else begin
          mul tr (assign (VVal (v,offset)) (T.var (V.mk_tmp "store" TyInt)))
        end
      | _, _ -> tr
    in
    MemLoc.Set.fold add_target (resolve_ap lhs) one
  | Builtin Exit -> zero
  | Builtin (Alloc (v, size, _)) ->
    BatList.reduce mul [
      assign (VVal v) (T.var (V.mk_tmp "alloc" TyInt));
      assign (VWidth v) (tr_expr_val size);
      assign (VPos v) T.zero
    ]
  | Builtin AtomicBegin | Builtin AtomicEnd
  | Builtin (Acquire _) | Builtin (Release _)
  | Builtin (Free _)
  | Initial | Assert (_, _) | AssertMemSafe (_, _) | Return None -> one
  | _ ->
    Log.errorf "No translation for definition: %a" Def.format def;
    assert false

module V = Cra.V

(* Tensored vocabulary *)
type vv = Left of V.t | Right of V.t
              deriving (Show, Compare)

module VV = struct
  module I = struct
    type t = vv deriving (Show, Compare)
    let compare = Compare_t.compare
    let show = Show_t.show
    let format = Show_t.format
    let equal x y = compare x y = 0

    let hash = function
      | Left v -> Hashtbl.hash (v, 0)
      | Right v -> Hashtbl.hash (v, 1)
  end
  include I

  let lower = function
    | Left v -> v
    | Right v -> v

  let left v = Left v
  let right v = Right v

  let prime = function
    | Left v -> Left (V.prime v)
    | Right v -> Right (V.prime v)

  module E = Enumeration.Make(I)
  let enum = E.empty ()
  let of_smt sym = match Smt.symbol_refine sym with
    | Smt.Symbol_int id -> E.from_int enum id
    | Smt.Symbol_string _ -> assert false
  let typ v = V.typ (lower v)
  let to_smt v =
    let id = E.to_int enum v in
    match typ v with
    | TyInt -> Smt.mk_int_const (Smt.mk_int_symbol id)
    | TyReal -> Smt.mk_real_const (Smt.mk_int_symbol id)
  let tag = E.to_int enum
end

(* Tensored transition formula *)
module KK = struct
  module Voc = V
  module VocMap = Map.Make(Voc)
  include RecurrenceAnalysis(VV)

  (* Detensor-transpose local variables and remove them from the footprint *)
  let project tr =
    (* For every *local* variable v, identify Left v (representing the
       post-state of the left) and Right v (representing the pre-state of the
       right) by substituting [Left v -> Right v] *)
    let substitution = function
      | V.PVar (Left v) when not (Var.is_global (Cra.var_of_value v)) ->
        T.var (V.mk_var (Right v))
      | v -> T.var v
    in
    { transform = M.map (T.subst substitution) tr.transform;
      guard = F.subst substitution tr.guard }

    (* Remove local variables from the footprint *)
    |> exists (Var.is_global % Cra.var_of_value % VV.lower)

  let top_local block =
    let open CfgIr in
    let file = get_gfile () in
    let func = lookup_function block file in
    (BatEnum.append
       (BatEnum.append (BatList.enum func.formals) (BatList.enum func.locals))
       (BatList.enum file.vars))
    /@ (fun vi ->
        let vl = Left (Cra.VVal (Var.mk vi)) in
        let vr = Right (Cra.VVal (Var.mk vi)) in
        mul
          (assign vl (T.var (V.mk_tmp "havoc" (VV.typ vl))))
          (assign vr (T.var (V.mk_tmp "havoc" (VV.typ vr)))))
    |> BatEnum.reduce mul
end

(* Inject terms from the untensored vocabulary to the tensored vocabulary.
   [inject_term VV.left] performs left injection and [inject_term VV.right]
   performs right injection. *)
let inject_term inject term =
  let alg = function
    | OFloor x -> KK.T.floor x
    | OAdd (x, y) -> KK.T.add x y
    | OMul (x, y) -> KK.T.mul x y
    | ODiv (x, y) -> KK.T.div x y
    | OMod (x, y) -> KK.T.modulo x y
    | OVar (K.V.PVar v) -> KK.T.var (KK.V.mk_var (inject v))
    | OVar (K.V.TVar (id, typ, name)) ->
      (* Identifiers for temporary variables remain unchanged.  This may be
         something we need to be careful about. *)
      KK.T.var (KK.V.TVar (id, typ, name))
    | OConst k -> KK.T.const k
  in
  K.T.eval alg term

(* See inject_term *)
let inject_formula inject phi =
  let alg = function
    | OOr (phi, psi) -> KK.F.disj phi psi
    | OAnd (phi, psi) -> KK.F.conj phi psi
    | OAtom (LeqZ x) -> KK.F.leqz (inject_term inject x)
    | OAtom (EqZ x) -> KK.F.eqz (inject_term inject x)
    | OAtom (LtZ x) -> KK.F.ltz (inject_term inject x)
  in
  K.F.eval alg phi

let tensor tr_left tr_right =
  let left_transform =
    BatEnum.fold (fun transform (k, term) ->
        KK.M.add (Left k) (inject_term VV.left term) transform)
      KK.M.empty
      (K.M.enum tr_left.K.transform);
  in
  (* Combined left & right transform *)
  let left_right_transform =
    BatEnum.fold (fun transform (k, term) ->
        KK.M.add (Right k) (inject_term VV.right term) transform)
      left_transform
      (K.M.enum tr_right.K.transform);
  in
  { KK.transform = left_right_transform;
    KK.guard =
      KK.F.conj
        (inject_formula VV.left tr_left.K.guard)
        (inject_formula VV.right tr_right.K.guard) }

(* Lower terms from the tensored vocabulary to the untensored vocabulary. *)
let lower_term substitution term =
  let alg = function
    | OFloor x -> K.T.floor x
    | OAdd (x, y) -> K.T.add x y
    | OMul (x, y) -> K.T.mul x y
    | ODiv (x, y) -> K.T.div x y
    | OMod (x, y) -> K.T.modulo x y
    | OVar v -> substitution v
    | OConst k -> K.T.const k
  in
  KK.T.eval alg term

let lower_formula substitution phi =
  let alg = function
    | OOr (phi, psi) -> K.F.disj phi psi
    | OAnd (phi, psi) -> K.F.conj phi psi
    | OAtom (LeqZ x) -> K.F.leqz (lower_term substitution x)
    | OAtom (EqZ x) -> K.F.eqz (lower_term substitution x)
    | OAtom (LtZ x) -> K.F.ltz (lower_term substitution x)
  in
  KK.F.eval alg phi

let detensor_transpose tensored_tr =
  let lower_temporary =
    Memo.memo (fun (id, typ, name) -> K.V.mk_tmp name typ)
  in
  (* For [Left v -> rhs] in tensor_tr's transform, create a fresh Skolem
     constant skolem_v.  Store the mapping [v -> skolem_v] in substitution_map,
     and store the pair (v, rhs) in the list pre_state_eqs. *)
  let (substitution_map, pre_state_eqs) =
    let fresh_skolem v =
      K.T.var (K.V.mk_tmp ("fresh_" ^ (V.show v)) (V.typ v))
    in
    KK.M.fold
      (fun v rhs (substitution_map, pre_state_eqs) ->
         match v with
         | Right _ -> (substitution_map, pre_state_eqs)
         | Left v ->
           let skolem_v = fresh_skolem v in
           let substitution_map = K.M.add v skolem_v substitution_map in
           (substitution_map, (K.T.var (K.V.mk_var v), rhs)::pre_state_eqs))
      tensored_tr.KK.transform
      (K.M.empty, [])
  in

  (* For every variable v, identify Left v (representing the post-state of the
     left) and Right v (representing the pre-state of the right) by
     substituting the same term term_v for both Left v and Right v.  term_v is
     defined to be v if v was not written on the left, and skolem_v if it
     was. *)
  let substitution = function
    | KK.V.PVar (Left v) | KK.V.PVar (Right v) ->
      (try
         K.M.find v substitution_map
       with Not_found -> K.T.var (K.V.mk_var v))
    | KK.V.TVar (id, typ, name) -> K.T.var (lower_temporary (id, typ, name))
  in

  (* substitution_map already has all the assignments that come from the left.
     Add to substition map all the right assignments, possibly overwriting the
     left assignments. *)
  let transform =
    KK.M.fold
      (fun v rhs transform ->
         match v with
         | Left _ -> transform
         | Right v -> K.M.add v (lower_term substitution rhs) transform)
      tensored_tr.KK.transform
      substitution_map
  in

  (* Lower the guard into the untensored vocabulary and conjoin the equations
     for the Skolem constants. *)
  let guard =
    List.fold_left
      (fun guard (v, term) ->
         K.F.conj
           guard
           (K.F.eq v (lower_term substitution term)))
      (lower_formula substitution tensored_tr.KK.guard)
      pre_state_eqs
  in
  { K.transform = transform;
    K.guard = guard }

let tensor_qe_lme_pvars f = 
   (* Remove temporary variables (TVars) by quantifier elimination,
        leaving only program variables (PVars). *)
   (KK.F.qe_lme (fun v -> KK.V.lower v != None) f)

let qe_lme_pvars f = 
   (* Remove temporary variables (TVars) by quantifier elimination,
        leaving only program variables (PVars). *)
   (K.F.qe_lme (fun v -> K.V.lower v != None) f)

(* Linearization as a simplifier *)
let linearize _ = K.F.linearize (fun () -> K.V.mk_tmp "nonlin" TyInt)

module VMemo = Memo.Make(V)

let left_context tr =
  let lower_temporary =
    Memo.memo (fun (id, typ, name) -> K.V.mk_tmp name typ)
  in
  let fresh_skolem =
    VMemo.memo (fun v -> K.T.var (K.V.mk_tmp ("fresh_" ^ (V.show v)) (V.typ v)))
  in
  let substitution = function
    | KK.V.PVar (Left v) -> K.T.var (K.V.mk_var v)
    | KK.V.PVar (Right v) -> fresh_skolem v
    | KK.V.TVar (id, typ, name) -> K.T.var (lower_temporary (id, typ, name))
  in
  let guard = lower_formula substitution tr.KK.guard in
  let transform =
    KK.M.fold
      (fun v rhs transform ->
         match v with
         | Left v -> K.M.add v (lower_term substitution rhs) transform
         | Right v -> transform)
      tr.KK.transform
      K.M.empty
  in
  { K.guard = guard;
    K.transform = transform }

let right_context tr =
  let lower_temporary =
    Memo.memo (fun (id, typ, name) -> K.V.mk_tmp name typ)
  in
  let fresh_skolem =
    VMemo.memo (fun v -> K.T.var (K.V.mk_tmp ("fresh_" ^ (V.show v)) (V.typ v)))
  in
  let substitution = function
    | KK.V.PVar (Left v) -> fresh_skolem v
    | KK.V.PVar (Right v) -> K.T.var (K.V.mk_var v)
    | KK.V.TVar (id, typ, name) -> K.T.var (lower_temporary (id, typ, name))
  in
  let guard = lower_formula substitution tr.KK.guard in
  let transform =
    KK.M.fold
      (fun v rhs transform ->
         match v with
         | Left _ -> transform
         | Right v -> K.M.add v (lower_term substitution rhs) transform)
      tr.KK.transform
      K.M.empty
  in
  { K.guard = guard;
    K.transform = transform }

let print_var_bounds formatter tick_var tr =
  let sigma v =
    match K.V.lower v with
    | Some pv ->
      if V.equal pv tick_var then K.T.zero else K.T.var v
    | None -> K.T.var v
  in
  let phi =
    K.F.conj
      (K.F.subst sigma tr.K.guard)
      (K.F.eq
         (K.T.var (K.V.mk_var tick_var))
         (K.T.subst sigma (K.M.find tick_var tr.K.transform)))
  in

  let (bounds, nl_map) =
    let is_global v = match K.V.lower v with
      | Some (VVal v) | Some (VPos v) | Some (VWidth v) -> Var.is_global v
      | None -> false
    in
    K.F.var_bounds_nonlinear
      K.V.mk_tmp
      is_global
      (K.V.mk_var tick_var)
      phi
  in

  let nl_rewrite x =
    try K.T.V.Map.find x nl_map with Not_found -> K.T.var x
  in

  let tick_dim = AVar (K.V.mk_var tick_var) in
  let print_tcons tcons =
    let open Apron in
    let open Tcons0 in
    match K.T.to_linterm (K.T.of_apron bounds.K.T.D.env tcons.texpr0) with
    | None -> ()
    | Some t ->
      let (a, t) = K.T.Linterm.pivot tick_dim t in
      if QQ.equal a QQ.zero then
        ()
      else begin
        let bound =
          K.T.Linterm.scalar_mul (QQ.negate (QQ.inverse a)) t
          |> K.T.of_linterm
          |> K.T.subst nl_rewrite
        in
        match tcons.typ with
        | EQ ->
          Format.fprintf formatter "%a = %a@;"
            V.format tick_var
            K.T.format bound
        | SUPEQ when QQ.lt QQ.zero a ->
          Format.fprintf formatter "%a >= %a@;"
            V.format tick_var
            K.T.format bound
        | SUPEQ when QQ.lt a QQ.zero ->
          Format.fprintf formatter "%a <= %a@;"
            V.format tick_var
            K.T.format bound
        | _ -> ()
      end
  in
  let man = K.F.T.D.manager bounds in
  BatArray.iter
    print_tcons
    (Apron.Abstract0.to_tcons_array man bounds.K.F.T.D.prop)

let () =
  CmdLine.register_config
    ("-cra-star-lc-hull",
     Arg.Clear K.opt_star_lc_rec,
     " Widen in convex hulls for left context star");
  CmdLine.register_config
    ("-cra-disable-simplify",
     Arg.Unit (fun () ->
         K.F.opt_simplify_strategy := [];
         KK.F.opt_simplify_strategy := []),
     " Disable formula simplification in CRA");
  CmdLine.register_config
    ("-cra-abstract-limit",
     Arg.Int (fun k ->
         K.F.opt_abstract_limit := k;
         KK.F.opt_abstract_limit := k),
     " Set max number of rounds for symbolic abstraction")

module KVMemo = Memo.Make(K.V)

let () =
  Callback.register "compose_callback" K.mul;
  Callback.register "union_callback" K.add;
  Callback.register "one_callback" (fun () -> K.one);
  Callback.register "zero_callback" (fun () -> K.zero);
  Callback.register "star_callback" K.star;
  Callback.register "print_callback" K.show;
  Callback.register "tensoredPrint_callback" KK.show;
  Callback.register "eq_callback" (fun x y -> K.compare x y = 0);
  Callback.register "equiv_callback" K.equiv;
  Callback.register "normalize_callback" K.normalize;
  Callback.register "transpose_callback" K.transpose;
  Callback.register "tensor_callback" tensor;
  Callback.register "merge_callback" K.project;
  Callback.register "tensorMerge_callback" KK.project;
  Callback.register "detensorTranspose_callback" detensor_transpose;
  Callback.register "tensorCompose_callback" KK.mul;
  Callback.register "tensorUnion_callback" KK.add;
  Callback.register "tensorStar_callback" KK.star;
  Callback.register "tensorZero_callback" (fun () -> KK.zero);
  Callback.register "tensorOne_callback" (fun () -> KK.one);

  Callback.register "alpha_hat_callback" K.alpha;
  Callback.register "tensor_alpha_hat_callback" KK.alpha;

  Callback.register "abstract_equiv_callback" K.abstract_equal;
  Callback.register "tensor_abstract_equiv_callback" KK.abstract_equal;

  Callback.register "abstract_widen_callback" K.abstract_widen;
  Callback.register "tensor_abstract_widen_callback" KK.abstract_widen;

  Callback.register "widen_callback" K.widen;
  Callback.register "tensor_widen_callback" KK.widen;

  (* Don't eta reduce - abstract_star has an optional parameter *)
  Callback.register "abstract_star_callback"
    (fun tr -> K.abstract_star tr);
  Callback.register "tensor_abstract_star_callback"
    (fun tr -> KK.abstract_star tr);

  Callback.register "print_abstract_callback" (fun indent abstract ->
     Putil.pp_string (fun formatter abstract ->
          Format.pp_open_vbox formatter indent;
          Format.pp_print_break formatter 0 0;
          Format.fprintf formatter "%a" K.format_abstract abstract;
          Format.pp_close_box formatter ())
       abstract);
  Callback.register "tensor_print_abstract_callback" (fun indent abstract ->
     Putil.pp_string (fun formatter abstract ->
          Format.pp_open_vbox formatter indent;
          Format.pp_print_break formatter 0 0;
          Format.fprintf formatter "%a" KK.format_abstract abstract;
          Format.pp_close_box formatter ())
       abstract);

  Callback.register "tensorEquiv_callback" KK.F.equiv;
  Callback.register "equiv_callback" K.F.equiv;
  Callback.register "simplify_callback" K.simplify;
  Callback.register "tensorSimplify_callback" KK.simplify;
  Callback.register "tensorQELME_callback" tensor_qe_lme_pvars;
  Callback.register "QELME_callback" qe_lme_pvars;
  Callback.register "print_formula_callback" K.F.show;
  Callback.register "tensor_print_formula_callback" KK.F.show;
  Callback.register "tensor_print_robust_callback" (fun indent tr ->
     Putil.pp_string (fun formatter tr ->
     Format.pp_open_vbox formatter indent;
     Format.pp_print_break formatter 0 0;
     Format.fprintf formatter "%a" KK.format_robust tr;
     Format.pp_close_box formatter ()) tr);
  Callback.register "print_robust_callback" (fun indent tr ->
     Putil.pp_string (fun formatter tr ->
     Format.pp_open_vbox formatter indent;
     Format.pp_print_break formatter 0 0;
     Format.fprintf formatter "%a" K.format_robust tr;
     Format.pp_close_box formatter ()) tr);
  Callback.register "tensor_print_indent_callback" (fun indent tr ->
     Putil.pp_string (fun formatter tr ->
     Format.pp_open_vbox formatter indent;
     Format.pp_print_break formatter 0 0;
     Format.fprintf formatter "%a" KK.format tr;
     Format.pp_close_box formatter ()) tr);
  Callback.register "print_indent_callback" (fun indent tr ->
     Putil.pp_string (fun formatter tr ->
     Format.pp_open_vbox formatter indent;
     Format.pp_print_break formatter 0 0;
     Format.fprintf formatter "%a" K.format tr;
     Format.pp_close_box formatter ()) tr);
  Callback.register "is_sat_callback" (fun tr ->
      K.F.is_sat_nonlinear K.V.mk_tmp tr.K.guard != Smt.Unsat);
  Callback.register "is_sat_linear_callback" (fun tr ->
      K.F.is_sat (linearize () tr.K.guard));
  Callback.register "print_stats_callback" Log.print_stats;
  Callback.register "top_callback" (fun () ->
      let open K in
      let open CfgIr in
      let file = (get_gfile()) in
      (BatList.enum file.vars)
      /@ (fun vi ->
          let v = Cra.VVal (Var.mk vi) in
          assign v (T.var (V.mk_tmp "havoc" (Voc.typ v))))
      |> BatEnum.reduce mul);
  Callback.register "star_lc" K.star_lc;
  Callback.register "tensor_star_lc" KK.star_lc;
  Callback.register "star_rc" K.star_rc;
  Callback.register "tensor_star_rc" KK.star_rc;
  Callback.register "left_context_callback" left_context;
  Callback.register "right_context_callback" right_context;
  Callback.register "domain_hull" K.domain_hull;
  Callback.register "range_hull" K.range_hull;
  Callback.register "tensor_domain_hull" KK.domain_hull;
  Callback.register "tensor_range_hull" KK.range_hull;
  Callback.register "domain" (fun tr -> { K.one with K.guard = tr.K.guard });
  Callback.register "range" K.range_hull;
  Callback.register "tensor_domain" (fun tr ->
      { KK.one with KK.guard = tr.KK.guard });
  Callback.register "tensor_range" KK.range;
  Callback.register "print_var_bounds_callback" (fun indent varid tr ->
        let tick_var =
          let p = function
            | VVal v -> (Var.get_id v) = varid
            | _ -> false
          in
          try
            Some (BatEnum.find p (K.M.keys tr.K.transform))
          with Not_found -> None
        in
        match tick_var with
        | None -> "No bounds"
        | Some tick_var ->
          Putil.pp_string (fun formatter (tick_var, tr) ->
              Format.pp_open_vbox formatter indent;
              Format.pp_print_break formatter 0 0;
              print_var_bounds formatter tick_var tr;
              Format.pp_close_box formatter ()) (tick_var, tr));
  Callback.register "print_smtlib" (K.F.to_smtlib2 % K.to_formula);
  Callback.register "tensor_print_smtlib" (KK.F.to_smtlib2 % KK.to_formula)
