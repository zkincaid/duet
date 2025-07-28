open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.interpolate" end)

module StdInterpolate
    (C: sig 
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

        (** The condition under which a transition may be executed. *)
        val guard : t -> C.t formula
  end) = 
  struct
  
    let srk = C.context
    module M = BatMap.Make(V)

    let interpolate trs post =
      let trs =
        trs |> List.map (fun tr ->
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
                      T.create guard @@ M.enum transform)
      in
      (* Break guards into conjunctions, associate each conjunct with an indicator *)
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
