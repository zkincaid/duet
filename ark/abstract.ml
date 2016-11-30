open Syntax
open Linear
open BatPervasives
open Apak
open Polyhedron

include Log.Make(struct let name = "ark.abstract" end)

module V = Linear.QQVector
module VS = Putil.Set.Make(Linear.QQVector)
module VM = Putil.Map.Make(Linear.QQVector)

let opt_abstract_limit = ref (-1)

(* Counter-example based extraction of the affine hull of a formula.  This
   works by repeatedly posing new (linearly independent) equations; each
   equation is either implied by the formula (and gets added to the affine
   hull) or there is a counter-example point which shows that it is not.
   Counter-example points are collecting in a system of linear equations where
   the variables are the coefficients of candidate equations. *)
let affine_hull ark phi constants =
  let solver = Smt.mk_solver ark in
  solver#add [phi];
  let next_row =
    let n = ref (-1) in
    fun () -> incr n; (!n)
  in
  let vec_one = QQVector.of_term QQ.one 0 in
  let rec go equalities mat = function
    | [] -> equalities
    | (k::ks) ->
      let dim = dim_of_sym k in
      let row_num = next_row () in
      (* Find a candidate equation which is satisfied by all previously
         sampled points, and where the coefficient of k is 1 *)
      let mat' = QQMatrix.add_row row_num (QQVector.of_term QQ.one dim) mat in
      match Linear.solve mat' (QQVector.of_term QQ.one row_num) with
      | None -> go equalities mat ks
      | Some candidate ->
        solver#push ();
        let candidate_term =
          QQVector.enum candidate
          /@ (fun (coeff, dim) ->
              match sym_of_dim dim with
              | Some const -> mk_mul ark [mk_real ark coeff; mk_const ark const]
              | None -> mk_real ark coeff)
          |> BatList.of_enum
          |> mk_add ark
        in
        solver#add [
          mk_not ark (mk_eq ark candidate_term (mk_real ark QQ.zero))
        ];
        match solver#get_model () with
        | `Unknown -> (* give up; return the equalities we have so far *)
          logf ~level:`warn
            "Affine hull timed out (%d equations)"
            (List.length equalities);
          equalities
        | `Unsat -> (* candidate equality is implied by phi *)
          solver#pop 1;
          (* We never choose the same candidate equation again, because the
             system of equations mat' x = 0 implies that the coefficient of k is
             zero *)
          go (candidate_term::equalities) mat' ks
        | `Sat point -> (* candidate equality is not implied by phi *)
          solver#pop 1;
          let point_row =
            List.fold_left (fun row k ->
                QQVector.add_term
                  (point#eval_real (mk_const ark k))
                  (dim_of_sym k)
                  row)
              vec_one
              constants
          in
          let mat' = QQMatrix.add_row row_num point_row mat in
          (* We never choose the same candidate equation again, because the
             only solutions to the system of equations mat' x = 0 are
             equations which are satisfied by the sampled point *)
          go equalities mat' (k::ks)
  in
  go [] QQMatrix.zero constants

let boxify ark phi terms =
  let mk_box t ivl =
    let lower =
      match Interval.lower ivl with
      | Some lo -> [mk_leq ark (mk_real ark lo) t]
      | None -> []
    in
    let upper =
      match Interval.upper ivl with
      | Some hi -> [mk_leq ark t (mk_real ark hi)]
      | None -> []
    in
    lower@upper
  in
  match ArkZ3.optimize_box ark phi terms with
  | `Sat intervals ->
    mk_and ark (List.concat (List.map2 mk_box terms intervals))
  | `Unsat -> mk_false ark
  | `Unknown -> assert false

let abstract ?exists:(p=fun x -> true) ark man phi =
  let solver = Smt.mk_solver ark in
  let phi_symbols = symbols phi in
  let projected_symbols = Symbol.Set.filter (not % p) phi_symbols in
  let symbol_list = Symbol.Set.elements phi_symbols in
  let env_proj = ArkApron.Env.of_set ark (Symbol.Set.filter p phi_symbols) in

  let disjuncts = ref 0 in
  let rec go prop =
    solver#push ();
    solver#add [mk_not ark (ArkApron.formula_of_property prop)];
    match Log.time "lazy_dnf/sat" solver#get_model () with
    | `Unsat ->
      solver#pop 1;
      prop
    | `Unknown ->
      begin
        logf ~level:`warn "abstraction timed out (%d disjuncts); returning top"
          (!disjuncts);
        solver#pop 1;
        ArkApron.top man env_proj
      end
    | `Sat model -> begin
        let interp = Interpretation.of_model ark model symbol_list in
        let valuation = model#eval_real % (mk_const ark) in
        solver#pop 1;
        incr disjuncts;
        logf "[%d] abstract lazy_dnf" (!disjuncts);
        if (!disjuncts) = (!opt_abstract_limit) then begin
          logf ~level:`warn "Met symbolic abstraction limit; returning top";
          ArkApron.top man env_proj
        end else begin
          let disjunct =
            match Interpretation.select_implicant interp phi with
            | Some d -> Polyhedron.polyhedron_of_implicant ark d
            | None -> begin
                assert (model#sat phi);
                assert false
              end
          in
          let projected_disjunct =
            Polyhedron.local_project valuation projected_symbols disjunct
            |> Polyhedron.to_apron env_proj man
          in
          go (ArkApron.join prop projected_disjunct)
        end
      end
  in
  solver#add [phi];
  Log.time "Abstraction" go (ArkApron.bottom man env_proj)

(* Symbolic intervals *)
module SymInterval = struct
  type 'a t = { ark : 'a context;
                upper : 'a term list;
                lower : 'a term list;
                interval : Interval.t }

  let cartesian ark f xs ys =
    ApakEnum.cartesian_product (BatList.enum xs) (BatList.enum ys)
    /@ (fun (x,y) -> f ark [x;y])
    |> BatList.of_enum

  let add x y =
    let ark = x.ark in
    { ark = ark;
      upper = cartesian ark mk_add x.upper y.lower;
      lower = cartesian ark mk_add x.lower y.lower;
      interval = Interval.add x.interval y.interval }

  let of_interval ark ivl =
    { ark = ark;
      upper = [];
      lower = [];
      interval = ivl }

  let zero ark = of_interval ark Interval.zero
  let bottom ark = of_interval ark Interval.bottom
  let top ark = of_interval ark Interval.top

  let mul_interval ivl x =
    let ark = x.ark in
    if Interval.is_nonnegative ivl then
      let upper = match Interval.upper ivl with
        | Some k -> List.map (fun x -> mk_mul ark [mk_real ark k; x]) x.upper
        | None -> []
      in
      let lower = match Interval.lower ivl with
        | Some k -> List.map (fun x -> mk_mul ark [mk_real ark k; x]) x.lower
        | None -> []
      in
      { ark = ark;
        upper = upper;
        lower = lower;
        interval = Interval.mul ivl x.interval }
    else if Interval.is_nonpositive ivl then
      let upper = match Interval.upper ivl with
        | Some k -> List.map (fun x -> mk_mul ark [mk_real ark k; x]) x.lower
        | None -> []
      in
      let lower = match Interval.lower ivl with
        | Some k -> List.map (fun x -> mk_mul ark [mk_real ark k; x]) x.upper
        | None -> []
      in
      { ark = ark;
        upper = upper;
        lower = lower;
        interval = Interval.mul ivl x.interval }
    else
      { ark = ark;
        upper = [];
        lower = [];
        interval = Interval.mul ivl x.interval }

  let meet x y =
    { ark = x.ark;
      upper = x.upper @ y.upper;
      lower = x.lower @ y.lower;
      interval = Interval.meet x.interval y.interval }

  let mul x y = meet (mul_interval x.interval y) (mul_interval y.interval x)

  let negate x =
    { ark = x.ark;
      interval = Interval.negate x.interval;
      upper = List.map (mk_neg x.ark) x.lower;
      lower = List.map (mk_neg x.ark) x.upper }

  let div x y =
    let ark = x.ark in
    match Interval.lower y.interval, Interval.upper y.interval with
    | Some a, Some b ->
      if Interval.elem QQ.zero y.interval then top ark
      else if QQ.equal a b then begin
        if QQ.lt QQ.zero a then
          { ark = ark;
            lower = List.map (fun x -> mk_div ark x (mk_real ark a)) x.lower;
            upper = List.map (fun x -> mk_div ark x (mk_real ark a)) x.upper;
            interval = Interval.div x.interval y.interval }
        else
          { ark = ark;
            lower = List.map (fun x -> mk_div ark x (mk_real ark a)) x.upper;
            upper = List.map (fun x -> mk_div ark x (mk_real ark a)) x.lower;
            interval = Interval.div x.interval y.interval }
      end else of_interval ark (Interval.div x.interval y.interval) (* todo *)
    | _, _ -> of_interval ark (Interval.div x.interval y.interval)

  let modulo x y =
    let ark = x.ark in
    let ivl = Interval.modulo x.interval y.interval in
    if Interval.equal ivl Interval.bottom then bottom ark
    else if Interval.elem QQ.zero y.interval then top ark
    else
      (* y is either strictly positive or strictly negative.  mod y is the
         same as mod |y| *)
      let y =
        if Interval.is_positive y.interval then y
        else negate y
      in
      let one_minus x = mk_sub ark (mk_real ark QQ.one) x in
      let minus_one x = mk_sub ark x (mk_real ark QQ.one) in
      if Interval.is_nonnegative x.interval then
        { ark = ark;
          interval = ivl;
          lower = [];
          upper = x.upper@(List.map minus_one y.upper) }
      else if Interval.is_nonpositive x.interval then
        { ark = ark;
          interval = ivl;
          lower = x.lower@(List.map one_minus y.upper);
          upper = [] }
      else
        { ark = ark;
          interval = ivl;
          lower = List.map one_minus y.upper;
          upper = List.map minus_one y.upper }

  let make ark lower upper interval =
    { ark = ark; lower = lower; upper = upper; interval = interval }
  let lower x = x.lower
  let upper x = x.upper
  let interval x = x.interval
  let floor x = make x.ark [] [] (Interval.floor x.interval)
end

(* Check if mul, div, and mod are registered, and register them if not *)
let ensure_nonlinear_symbols ark =
  List.iter
    (fun (name, typ) ->
       if not (is_registered_name ark name) then
         register_named_symbol ark name typ)
    [("mul", `TyFun ([`TyReal; `TyReal], `TyReal));
     ("div", `TyFun ([`TyReal; `TyReal], `TyReal));
     ("mod", `TyFun ([`TyReal; `TyReal], `TyReal))]

let nonlinear_uninterpreted_rewriter ark =
  ensure_nonlinear_symbols ark;
  let mul = get_named_symbol ark "mul" in
  let div = get_named_symbol ark "div" in
  let modulo = get_named_symbol ark "mod" in
  fun expr ->
    match destruct ark expr with
    | `Binop (`Div, x, y) ->
      begin match Term.destruct ark y with
        | `Real k when not (QQ.equal k QQ.zero) ->
          (mk_mul ark [mk_real ark (QQ.inverse k); x] :> ('a,typ_fo) expr)
        | _ -> mk_app ark div [x; y]
      end
    | `Binop (`Mod, x, y) ->
      begin match Term.destruct ark y with
        | `Real k when not (QQ.equal k QQ.zero) -> expr
        | _ -> mk_app ark modulo [x; y]
      end
    | `Mul (x::xs) ->
      let term =
        List.fold_left (fun x y ->
            match Term.destruct ark x, Term.destruct ark y with
            | `Real x, `Real y -> mk_real ark (QQ.mul x y)
            | `Real _, _ | _, `Real _ -> mk_mul ark [x; y]
            | _, _ -> mk_app ark mul [x; y])
          x
          xs
      in
      (term :> ('a,typ_fo) expr)
    | _ -> expr

let nonlinear_uninterpreted ark expr =
  rewrite ark ~up:(nonlinear_uninterpreted_rewriter ark) expr

let purify_rewriter ark table =
  fun expr ->
    match destruct ark expr with
    | `Quantify (_, _, _, _) -> invalid_arg "purify: free variable"
    | `App (func, args) ->
      let sym =
        try
          ExprHT.find table expr
        with Not_found ->
          let sym = mk_symbol ark ~name:"uninterp" (expr_typ ark expr) in
          ExprHT.add table expr sym;
          sym
      in
      mk_const ark sym
    | _ -> expr

let purify ark expr =
  let table = ExprHT.create 991 in
  let expr' = rewrite ark ~up:(purify_rewriter ark table) expr in
  let map =
    BatEnum.fold
      (fun map (term, sym) -> Symbol.Map.add sym term map)
      Symbol.Map.empty
      (ExprHT.enum table)
  in
  (expr', map)

let linearize ark phi =
  let uninterp_phi = nonlinear_uninterpreted ark phi in
  let (lin_phi, nonlinear) = purify ark uninterp_phi in
  if Symbol.Map.is_empty nonlinear then phi else begin
    (* Symbols that appear in nonlinear terms *)
    let symbol_list =
      Symbol.Map.fold
        (fun _ expr set ->
           symbols expr
           |> Symbol.Set.filter (fun sym ->
               let typ = typ_symbol ark sym in
               typ = `TyInt || typ = `TyReal)
           |> Symbol.Set.union set)
        nonlinear
        Symbol.Set.empty
      |> Symbol.Set.elements
    in
    let objectives = List.map (mk_const ark) symbol_list in
    match ArkZ3.optimize_box ark lin_phi objectives with
    | `Sat intervals ->
      let env =
        List.fold_left2
          (fun map sym ivl ->
             let t = mk_const ark sym in
             Symbol.Map.add sym (SymInterval.make ark [t] [t] ivl) map)
          Symbol.Map.empty
          symbol_list
          intervals
      in
      let linbound_zero =
        SymInterval.of_interval ark (Interval.const QQ.zero)
      in
      let linbound_one = SymInterval.of_interval ark (Interval.const QQ.one) in
      let linbound_minus_one =
        SymInterval.of_interval ark (Interval.const (QQ.negate QQ.one))
      in
      (* compute a symbolic interval for a term *)
      let rec linearize_term term =
        match Term.destruct ark term with
        | `Const sym ->
          (try Symbol.Map.find sym env
           with Not_found -> assert false)
        | `Real k -> SymInterval.of_interval ark (Interval.const k)
        | `Add sum ->
          List.fold_left
            (fun linbound t -> SymInterval.add linbound (linearize_term t))
            linbound_zero
            sum
        | `Mul prod ->
          List.fold_left
            (fun linbound t -> SymInterval.mul linbound (linearize_term t))
            linbound_one
            prod
        | `Binop (`Div, x, y) ->
          SymInterval.div (linearize_term x) (linearize_term y)
        | `Binop (`Mod, x, y) ->
          SymInterval.modulo (linearize_term x) (linearize_term y)
        | `Unop (`Floor, x) -> SymInterval.floor (linearize_term x)
        | `Unop (`Neg, x) ->
          SymInterval.mul linbound_minus_one (linearize_term x)
        | `App (func, args) ->
          begin match symbol_name ark func, List.map (refine ark) args with
            | (Some "mul", [`Term x; `Term y]) ->
              SymInterval.mul (linearize_term x) (linearize_term y)
            | (Some "div", [`Term x; `Term y]) ->
              SymInterval.div (linearize_term x) (linearize_term y)
            | (Some "mod", [`Term x; `Term y]) ->
              SymInterval.modulo (linearize_term x) (linearize_term y)
            | _ -> SymInterval.top ark
          end
        | `Var (_, _) | `Ite (_, _, _) -> assert false
      in
      (* conjoin symbolic intervals for all non-linear terms *)
      let bounds =
        (Symbol.Map.enum nonlinear)
        /@ (fun (symbol, expr) ->
            match refine ark expr with
            | `Formula _ -> mk_true ark
            | `Term term ->
              let bounds = linearize_term term in
              let const = mk_const ark symbol in
              let lower =
                let terms =
                  match Interval.lower (SymInterval.interval bounds) with
                  | Some k -> (mk_real ark k)::(SymInterval.lower bounds)
                  | None -> (SymInterval.lower bounds)
                in
                List.map (fun lo -> mk_leq ark lo const) terms
                |> mk_and ark
              in
              let upper =
                let terms =
                  match Interval.upper (SymInterval.interval bounds) with
                  | Some k -> (mk_real ark k)::(SymInterval.upper bounds)
                  | None -> (SymInterval.upper bounds)
                in
                List.map (fun hi -> mk_leq ark const hi) terms
                |> mk_and ark
              in
              mk_and ark [lower; upper])
        |> BatList.of_enum
        |> mk_and ark
      in
      (* Implied equations over non-linear terms *)
      let nonlinear_eqs =
        let nonlinear_defs =
          Symbol.Map.enum nonlinear
          /@ (fun (symbol, expr) ->
              match refine ark expr with
              | `Term t -> mk_eq ark (mk_const ark symbol) t
              | `Formula phi -> mk_iff ark (mk_const ark symbol) phi)
          |> BatList.of_enum
          |> mk_and ark
        in
        let hull =
          affine_hull
            ark
            (mk_and ark [lin_phi; nonlinear_defs])
            (Symbol.Map.keys nonlinear |> BatList.of_enum)
        in
        List.map (mk_eq ark (mk_real ark QQ.zero)) hull |> mk_and ark
      in
      mk_and ark [lin_phi; bounds; nonlinear_eqs]
    | `Unsat -> mk_false ark
    | `Unknown ->
      logf ~level:`warn "linearize: optimization failed";
      lin_phi
  end
