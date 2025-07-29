open Syntax
open BatPervasives
open Interpolant 

include Log.Make(struct let name = "srk.newtonInterpolant" end)

module NewtonBackwards : Interpolant = functor (C: sig 
        type t 
        val context : t context 
    end)
    (V: sig
        type t
        val show : t -> string
        val typ : t -> [ `TyInt | `TyReal ]
        val compare : t -> t -> int
        val symbol_of : t -> symbol
        val of_symbol : symbol -> t option
        val is_global : t -> bool
    end)
    (T: sig 
        type t
        type var = V.t
        val equal : t -> t -> bool
        val compare : t -> t -> int

        (** Guarded parallel assignment *)
        val construct : C.t formula -> (var * C.t arith_term) list -> t

        val create : C.t formula -> (var * C.t arith_term) BatEnum.t -> t 
        (** [exists ex tr] removes the variables that do not satisfy the predicate
            [ex] from the footprint of a transition.  For example, projecting a
            variable [x] out of a transition [tr] is logically equivalent to
            [(exists x. tr) && x' = x]. *)
        val exists : (var -> bool) -> t -> t

        (** (Needed by interpolation) *)
        val destruct_and : (C.t context) -> (C.t formula) -> (C.t formula) list

        (** Enumerate the variables and values assigned in a transition. *)
        val transform : t -> (var * C.t arith_term) BatEnum.t

        val defines : t -> var list

        (** Variables used by a a transition, including non-Skolem symbols in both the guard and the transform. *)
        val uses : t -> var list

        (** The condition under which a transition may be executed. *)
        val guard : t -> C.t formula

        val state_vocabulary : t -> (var * Syntax.symbol) list 
  end) -> struct
  
    let srk = C.context
    module M = BatMap.Make(V)

    (* The helper functions below implement the live-variables analysis described in:

        Daniel Dietsch, Matthias Heizmann, Betim Musa, Alexander Nutz, and Andreas Podelski. 
          Craig vs. Newton in software model checking. ESEC/FSE 2017.
       
       For a sequence of transition formulas [trs]:
    
       Def 1 (future-live variable). We call a variable [x] future-live in [trs] at position i if there is
        a transition tr_j in [trs] with j > i, such that
          - tr_j reads x, and 
          - for all k with i < k < j the transition tr_k neither writes nor havocs [x].
          
       Def 2 (past-live variable).We call a variable [x] past-live in [trs] at i if there is a transition tr_j in [trs] with
        j <= i, such that 
          - tr_j writes x or reads x, and 
          - for all k with j < k <= i the transition tr_k does not havoc x. 
    *)

    (** test whether a variable [x] of type [var] is future-live in future transitions [trs]. *)

    let is_future_live x trs =
      if trs = [] then false else begin 
        (* In srk, havocs are writes, so suffices to detect writes only.
           Logic: Scan the transitions from right-to-left,
            - if tr_j reads x, then switch to verify that all transitions left of tr_j does not write to x.
            - if some tr_k writes to x, then we need to re-find some j<k that reads x, or x is marked as not live.
        *)
        let state = List.fold_left (fun (has_been_read, has_been_written) tr -> 
          if has_been_read then begin 
            if has_been_written then begin  
              if List.mem x (T.uses tr) && (not (List.mem x (T.defines tr))) then (has_been_read, false)
              else (has_been_read, has_been_written)
            end else (has_been_read, List.mem x (T.defines tr))
          end else begin
            (List.mem x (T.uses tr) && not(List.mem x (T.defines tr)), false)
          end
          ) (false, false) (List.rev trs) in 
          match state with 
          (* a variable is future-live if it's used in the future and not modified between current point and point-of-use. *)
          | (true, false) -> true
          | _ -> false 
      end

    (** For a list of transitions [trs], compute the set of future-live variables for each transition's vocabulary.
        Returns a list of type [var Set.t] where the i-th set is the set of non-live variables at transition i. *)    
    let future_live_analysis trs = 
      let live_vars, _ = 
        List.fold_left (fun (acc, trs') tr -> 
          let vars = List.map (fun (x, _) -> x) (T.state_vocabulary tr) in 
          (List.filter (fun x -> is_future_live x trs') vars :: acc, tr :: trs') 
        ) ([], []) (List.rev trs) in 
        live_vars
    
    (** figure out set of variables with non-deterministic right-hand-side expressions in [tr]. *)
    let havoc_vars tr = 
      let transform = T.transform tr in 
      BatEnum.fold (fun curr (v, term) -> 
        if (Syntax.symbols term 
        |> Symbol.Set.filter (fun x -> V.of_symbol x = None) (* every skolem symbol is non-deterministic. *)
        |> Symbol.Set.cardinal) > 0 then 
          curr (* variable v is deterministically assigned *) 
        else 
          v :: curr (* variable v is assigned a non-det expression *)
        ) [] transform


    (** test whether a variable [x] is past-live w.r.t. past transitions [trs]. *)
    let is_past_live x trs = 
      let used x tr = List.mem x (T.uses tr) || List.mem x (T.defines tr) in 
      let havoced x tr = List.mem x (havoc_vars tr) in 
      if trs = [] then false else begin
        (* A simpler definition of past-variable is if a variable x is 
          (1) used and (2) never havoc'ed beyond some point j in [trs].
        *)
        let state = List.fold_left (fun (been_used, been_havoced) tr ->
          if been_used then begin 
              if been_havoced then begin
                if (used x tr) && not(havoced x tr) then (been_used, false)
                else (been_used, been_havoced)
              end else 
                (been_used, havoced x tr)
          end else begin 
            (used x tr, false)
          end
          ) (false, false) trs in 
          match state with 
          | (true, false) -> true 
          | _ -> false 
      end


    let interpolate trs post =
      (* The following step ensures all Skolem constants in [trs] are unique. *)
      let trs =
        trs |> List.map (fun tr ->
                  let fresh_skolem =
                    (* If sym is a non-skolem (i.e. stored in V), return the same symbol. Otherwise, create a fresh Skolem symbol. *)
                    Memo.memo (fun sym ->
                        match V.of_symbol sym with
                        | Some _ -> mk_const srk sym
                        | None ->
                            let name = show_symbol srk sym in
                            let typ = typ_symbol srk sym in
                            mk_const srk (mk_symbol srk ~name typ))
                  in
                    let transform = M.map (substitute_const srk fresh_skolem) (M.of_enum @@ T.transform tr) in 
                    let guard = substitute_const srk fresh_skolem (T.guard tr) in 
                      T.create guard @@ M.enum transform)
      in
      (* Take the list of guards for each transition in the sequence.
         Break guards into a list of conjunctions, and associate each conjunct with 
         an indicator variable that is true iff the conjunct is included in the final UNSAT core. *)
      let guards =
        List.map (fun tr ->
            List.map
              (fun phi -> (mk_symbol srk `TyBool, phi))
              (T.destruct_and srk (T.guard tr)))
          trs
      in
      let indicators =
        List.concat_map (List.map (fun (s, _) -> mk_const srk s)) guards
      in
      let subscript_tbl = Hashtbl.create 991 in
      let subscript sym =
        try
          Hashtbl.find subscript_tbl sym
        with Not_found -> mk_const srk sym
      in
      (* Convert tr into a formula, and simultaneously update the subscript
        table *)
      let to_ss_formula tr guards =
        let ss_guards =
          List.map (fun (indicator, guard) ->
              mk_if srk
                (mk_const srk indicator)
                (substitute_const srk subscript guard))
            guards
        in
        let (ss, phis) =
          M.fold (fun var term (ss, phis) ->
              let var_sym = V.symbol_of var in
              let var_ss_sym = mk_symbol srk (V.typ var :> typ) in
              let var_ss_term = mk_const srk var_ss_sym in
              let term_ss = substitute_const srk subscript term in
              ((var_sym, var_ss_term)::ss,
              mk_eq srk var_ss_term term_ss::phis))
            (M.of_enum (T.transform tr))
            ([], ss_guards)
        in
        List.iter (fun (k, v) -> Hashtbl.add subscript_tbl k v) ss;
        mk_and srk phis
      in
      let module Solver = Smt.StdSolver in
      let solver = Solver.make srk in
      List.iter2 (fun tr guard ->
          Solver.add solver [to_ss_formula tr guard])
        trs
        guards;
      Solver.add solver [substitute_const srk subscript (mk_not srk post)];
      match Solver.get_unsat_core solver indicators with
      | `Sat -> `Invalid
      | `Unknown -> `Unknown
      | `Unsat core ->
        let core_symbols =
          List.fold_left (fun core phi ->
              match Formula.destruct srk phi with
              | (`Proposition (`App (s, []))) -> Symbol.Set.add s core
              | _ -> assert false)
            Symbol.Set.empty
            core
        in
        let (itp, _) =
          List.fold_right2 (fun tr guard (itp, post) ->
              let subst sym =
                match V.of_symbol sym with
                | Some var ->
                    if M.mem var (M.of_enum (T.transform tr)) then
                      M.find var (M.of_enum (T.transform tr))
                    else
                      mk_const srk sym
                | None -> mk_const srk sym
              in
              let post' = substitute_const srk subst post in
              let reduced_guard =
                List.filter_map (fun (indicator, guard) ->
                    if Symbol.Set.mem indicator core_symbols then
                      Some (mk_not srk guard)
                    else
                      None)
                  guard
              in
              let wp =
                (mk_not srk (mk_or srk (post'::reduced_guard)))
                |> Quantifier.mbp srk (fun s -> V.of_symbol s != None)
                |> mk_not srk
              in
              (wp::itp, wp))
            trs
            guards
            ([
              mk_not srk post 
              |> Quantifier.mbp srk (fun x -> V.of_symbol x <> None)
              |> mk_not srk 
            ], post)
        in
        `Valid (List.tl itp)


    (* helper method for interpolate/extrapolate procedures. creates fresh copies of skolem variables in tr *)
    let rename_skolems tr =
      let fresh_skolem =
        Memo.memo (fun sym ->
            match V.of_symbol sym with
            | Some _ -> mk_const srk sym
            | None ->
                let name = show_symbol srk sym in
                let typ = typ_symbol srk sym in
                mk_const srk (mk_symbol srk ~name typ))
      in
        let transform = M.map (substitute_const srk fresh_skolem) (M.of_enum @@ T.transform tr) in 
        let guard = substitute_const srk fresh_skolem (T.guard tr) in 
          T.create guard (M.enum transform) 

    let interpolate_unsat_core trs post guards core =
      let core_symbols =
        List.fold_left (fun core phi ->
            match Formula.destruct srk phi with
            | (`Proposition (`App (s, []))) -> Symbol.Set.add s core
            | _ -> assert false)
          Symbol.Set.empty
          core
      in
      let (itp, _) =
        List.fold_right2 (fun tr guard (itp, post) ->
            let subst sym =
              match V.of_symbol sym with
              | Some var ->
                if M.mem var (M.of_enum @@ T.transform tr) then
                  M.find var (M.of_enum @@ T.transform tr)
                else
                  mk_const srk sym
              | None -> mk_const srk sym
            in
            let post' = substitute_const srk subst post in
            let reduced_guard =
              List.filter_map (fun (indicator, guard) ->
                  if Symbol.Set.mem indicator core_symbols then
                    Some (mk_not srk guard)
                  else
                    None)
                guard
            in
            let wp =
              (mk_not srk (mk_or srk (post'::reduced_guard)))
              |> Quantifier.mbp srk (fun s -> V.of_symbol s != None)
              |> mk_not srk
            in
            (wp::itp, wp))
          trs
          guards
            ([
              mk_not srk post 
              |> Quantifier.mbp srk (fun x -> V.of_symbol x <> None)
              |> mk_not srk 
            ], post)
      in `Valid (List.tl itp)  


    let interpolate_query trs post sat_callback unsat_callback =
      let solver = Smt.StdSolver.make C.context in
      (* Break guards into conjunctions, associate each conjunct with an indicator *)
      let guards =
        List.map (fun tr ->
            List.map
              (fun phi -> (mk_symbol srk `TyBool, phi))
              (T.destruct_and srk @@ T.guard tr))
          trs in
      let indicators, indicator_symbols =
        List.concat_map (List.map (fun (s, _) -> mk_const srk s)) guards,
        List.concat_map (List.map fst) guards |> Symbol.Set.of_list
      in
      let subscript_tbl = Hashtbl.create 991 in
      let ss_inv = Hashtbl.create 991 in
      let sst = Hashtbl.create 991 in
      let subscript sym =
        try
          Hashtbl.find subscript_tbl sym
        with Not_found -> mk_const srk sym
      in
      (* Convert tr into a formula, and simultaneously update the subscript
        table *)
      let to_ss_formula tr guards =
        let ss_guards =
          List.map (fun (indicator, guard) ->
              mk_if srk
                (mk_const srk indicator)
                (substitute_const srk subscript guard))
            guards
        in
        let (ss, phis) =
          M.fold (fun var term (ss, phis) ->
              let var_sym = V.symbol_of var in
              let var_ss_sym = mk_symbol srk (V.typ var :> typ) in
              let var_ss_term = mk_const srk var_ss_sym in
              let term_ss = substitute_const srk subscript term in
              ((var_sym, var_ss_sym, var_ss_term)::ss,
              mk_eq srk var_ss_term term_ss::phis))
            (M.of_enum @@ T.transform tr)
            ([], ss_guards)
        in
        List.iter (fun (k, l, v) ->
          Hashtbl.add subscript_tbl k v;
          Hashtbl.add ss_inv l k;
          Hashtbl.add sst k l) ss;
        mk_and srk phis
      in
      (* gather all symbols into a list, while adding formulas to the solver object *)
      let symbols, added_formulas = List.fold_left
        (fun (symbols, added_formulas) (tr, guard) ->
          let f = to_ss_formula tr guard in
            Smt.StdSolver.add solver [f];
            (Syntax.symbols f) :: symbols, f::added_formulas)
          ([], []) (List.combine trs guards) in
      let _ = List.iter (fun f ->
        let f = substitute_const srk
          (fun v ->
            match Hashtbl.find_opt ss_inv v with
            | None -> Syntax.mk_const srk v
            | Some v' -> Syntax.mk_const srk v') f
          in logf "added formula: %a\n" (Syntax.pp_expr srk) f) added_formulas
      (* subscript the symbols in the `post` formula, as well *) in
      let target = substitute_const srk subscript (mk_not srk post) in
      let symbols = (Syntax.symbols target) :: symbols
        |> List.rev
        |> List.map (fun ss -> Symbol.Set.diff ss indicator_symbols) in
        Smt.StdSolver.add solver [target];
        logf "-----------------------------interpolation---\n";
        List.iter (fun f ->
          let f = substitute_const srk
            (fun v ->
              match Hashtbl.find_opt ss_inv v with
              | None -> Syntax.mk_const srk v
              | Some v' -> Syntax.mk_const srk v') f
            in logf "indicator formula: %a\n" (Syntax.pp_expr srk) f) indicators;
            logf "-------------------interpolation end---\n";
        logf "--- indicator length %d\n" @@ List.length indicators;
        logf "\ntarget formula: %a\n" (Syntax.pp_expr srk) target;
        match Smt.StdSolver.get_unsat_core_or_model solver indicators with
          | `Sat m ->
            (sat_callback m symbols sst ss_inv)
          | `Unsat core -> (unsat_callback trs post guards core)
          | `Unknown -> `Unknown


  (* let interpolate trs post =
      let trs = List.map rename_skolems trs in
      interpolate_query trs post (fun _ _ _ _ -> `Invalid) @@ interpolate_unsat_core
  *)
    let interpolate_or_concrete_model trs post =
      (* subst_model: rename skolem constants back to their appropriate names using reverse subscript table *)
      let trs = List.map rename_skolems trs in
      let sat_model model (symbols: Symbol.Set.t list) ss ss_inv =
          let m =
            List.fold_left (fun m' symbols ->
              Symbol.Set.fold (fun s m ->
                (* the provided model is over both subscripted vocabulary and original vocabulary *)
                begin match Hashtbl.find_opt ss_inv s with
                | Some s' -> (* subscripted variable *)
                  Interpretation.add s' (Interpretation.value model s) m
                |  None -> (* non-subscripted; query directly *)
                  Interpretation.add s (Interpretation.value model s)  m
                end) symbols m'
            ) (Interpretation.wrap srk (fun s ->
                match Hashtbl.find_opt ss s with
                | Some sss -> Interpretation.value model sss
                | None -> `Real (Q.of_int 47))) (*(Interpretation.wrap srk (fun s ->
                  match Hashtbl.find_opt ss s with
                  | Some sss -> Interpretation.value model sss
                  | None -> Interpretation.value model s))*) (*(Interpretation.empty srk)*) symbols in
            logf "hashtable length: %d\n" (Hashtbl.length ss_inv);
            logf "%a" Interpretation.pp m;
            Format.print_flush ();
        (* symbols is a list of subscripted symbols arranged in left-to-right order.
          folding over this in left-to-right order amounts to forward concrete execution. *)
        `Invalid (m
          |> Interpretation.restrict
            (fun s ->
              match V.of_symbol s with
              | Some _ -> true
              | None -> false))
      in interpolate_query trs post sat_model @@ interpolate_unsat_core



  end
