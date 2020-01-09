
include Srk.Log.Make(struct let name = "smt" end)

open Z3
open BatPervasives
    
let opts = ref [ ("timeout", "5000");
                 ("model", "true") ]

let bool_val x =
  match Boolean.get_bool_value x with
  | Z3enums.L_TRUE -> true
  | Z3enums.L_FALSE -> false
  | Z3enums.L_UNDEF -> invalid_arg "bool_val: not a Boolean"

module F = PaFormula

class ['a] ctx opts = object(self)
  val z3 = mk_context opts
  val ht_arity : ('a,int) Hashtbl.t = Hashtbl.create 991
  val ht_sym_of_rel = Hashtbl.create 991
  val of_sym = BatDynArray.make 128
  val mutable next_sym = 0
  val mutable universe = Obj.magic ()
  initializer
    universe <- Symbol.mk_string self#z3 "universe"
  method z3 = z3
  method int_sort = Arithmetic.Integer.mk_sort z3
  method bool_sort = Boolean.mk_sort z3
  method sym_of_rel =
    try Hashtbl.find ht_sym_of_rel
    with Not_found -> invalid_arg "Unregistered predicate"
  method decl_of_rel rel =
    let sym = self#sym_of_rel rel in
    let int = self#int_sort in
    FuncDecl.mk_func_decl
      z3
      sym
      (BatList.of_enum ((1 -- self#arity rel) /@ (const int)))
      self#bool_sort
  method arity =
    try Hashtbl.find ht_arity
    with Not_found -> invalid_arg "Unregistered predicate"
  method register_rel rel arity =
    if not (Hashtbl.mem ht_arity rel) then begin
      Hashtbl.add ht_sym_of_rel rel (Z3.Symbol.mk_int self#z3 next_sym);
      Hashtbl.add ht_arity rel arity;
      BatDynArray.add of_sym (`Rel rel);
      next_sym <- next_sym + 1
    end
  method rel_of_sym sym =
    if not (Symbol.is_int_symbol sym) then
      invalid_arg "rel_of_sym: Not an integer symbol";
    let id = Symbol.get_int sym in
    if not (id <= BatDynArray.length of_sym) then
      invalid_arg "rel_of_sym: Symbol out of bounds";
    match BatDynArray.get of_sym id with
    | `Rel rel -> rel
    | `Const _ -> invalid_arg "rel_of_sym: Symbol is not a relation";
  method const_universe =
    Arithmetic.Integer.mk_const z3 universe
end

let of_formula ctx phi =
  let of_term = function
    | F.Var i -> Quantifier.mk_bound ctx#z3 i ctx#int_sort
    | F.Const k -> Arithmetic.Integer.mk_numeral_i ctx#z3 k
  in
  let symbol_of_hint = function
    | Some name -> Symbol.mk_string ctx#z3 name
    | None -> Symbol.mk_string ctx#z3 "anon"
  in
  let relativize hints =
    (0 -- (List.length hints - 1))
    /@ (fun v ->
        let bv = Quantifier.mk_bound ctx#z3 v ctx#int_sort in
        Boolean.mk_and ctx#z3 [
          Arithmetic.mk_le ctx#z3 (Arithmetic.Integer.mk_numeral_i ctx#z3 1) bv;
          Arithmetic.mk_le ctx#z3 bv ctx#const_universe;
        ])
    |> BatList.of_enum
    |> Boolean.mk_and ctx#z3
  in    
  let rec go phi = match F.destruct_flatten phi with
    | `And conjuncts -> Boolean.mk_and ctx#z3 (List.map go conjuncts)
    | `Or disjuncts -> Boolean.mk_or ctx#z3 (List.map go disjuncts)
    | `T -> Boolean.mk_true ctx#z3
    | `F -> Boolean.mk_false ctx#z3
    | `Atom (p, args) ->
      Expr.mk_app ctx#z3 (ctx#decl_of_rel p) (List.map of_term args)
    | `Neq (x, y) ->
      Boolean.mk_not ctx#z3 (Boolean.mk_eq ctx#z3 (of_term x) (of_term y))
    | `Eq (x, y) -> Boolean.mk_eq ctx#z3 (of_term x) (of_term y)
    | `Forall (hints, phi) ->
      Quantifier.mk_forall
        ctx#z3
        (List.map (fun _ -> ctx#int_sort) hints)
        (List.map symbol_of_hint hints)
        (Boolean.mk_implies ctx#z3 (relativize hints) (go phi))
        None
        []
        []
        None
        None
      |> Quantifier.expr_of_quantifier
    | `Exists (hints, phi) ->
      Quantifier.mk_exists
        ctx#z3
        (List.map (fun _ -> ctx#int_sort) hints)
        (List.map symbol_of_hint hints)
        (Boolean.mk_and ctx#z3 [relativize hints; go phi])
        None
        []
        []
        None
        None
      |> Quantifier.expr_of_quantifier
  in
  go phi

class ['a] model (ctx : 'a ctx) m = object(self)
  method eval_int term =
    match Model.eval m term true with
    | Some x -> Arithmetic.Integer.get_big_int x
    | None -> assert false
  method sat phi =
    match Model.eval m (of_formula ctx phi) true with
    | Some x -> bool_val x
    | None -> assert false
  method to_string () =
    Model.to_string m
  method get_func_interp rel =
    try Model.get_func_interp m (ctx#decl_of_rel rel)
    with Z3.Error _ ->
      (* Sometimes get_func_interp raises "invalid argument" -- possible bug
         in Z3 API? *)
      None
  method get_bool_interp rel =
    try
      match Model.get_const_interp m (ctx#decl_of_rel rel) with
      | Some x -> Some (bool_val x)
      | None -> invalid_arg "No interpretation"
    with Z3.Error _ -> None

end

class ['a] solver (ctx : 'a ctx) = object(self)
  val z3 = Solver.mk_simple_solver ctx#z3
  method z3 = z3
  method ctx = ctx
  method push () = Solver.push z3
  method pop () = Solver.pop z3 1
  method add phi =
    Solver.add z3 [of_formula ctx phi]
  method add_not phi =
    Solver.add z3 [Boolean.mk_not ctx#z3 (of_formula ctx phi)]
  method check () =
    match Solver.check z3 [] with
    | Solver.SATISFIABLE -> `Sat
    | Solver.UNSATISFIABLE -> `Unsat
    | Solver.UNKNOWN -> `Unknown
  method get_model : unit -> [`Sat of 'a model | `Unknown | `Unsat ]  = fun () ->
    match self#check () with
    | `Sat ->
      begin match Solver.get_model z3 with
        | Some m -> `Sat (new model ctx m)
        | None -> `Unknown
      end
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
end

(* (Backwards) linear search for a model with smallest possible universe *)
let get_min_model_linear_backward s =
  s#push ();
  Solver.add s#z3
    [Arithmetic.mk_gt
       s#ctx#z3
       s#ctx#const_universe
       (Arithmetic.Integer.mk_numeral_i s#ctx#z3 1)];
  let rec minimize m =
    let size = m#eval_int s#ctx#const_universe in
    logf "Minimizing model.  Size: %d" size;
    Solver.add s#z3
      [Arithmetic.mk_lt
         s#ctx#z3
         s#ctx#const_universe
         (Arithmetic.Integer.mk_numeral_i s#ctx#z3 size)];
    match s#get_model () with
    | `Sat m -> minimize m
    | _ -> (m, size)
  in
  let result =
    match s#get_model () with
    | `Sat m -> `Sat (minimize m)
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
  in
  s#pop ();
  result

let get_min_model_linear_forward s =
  s#push ();
  Solver.add s#z3
    [Arithmetic.mk_gt
       s#ctx#z3
       s#ctx#const_universe
       (Arithmetic.Integer.mk_numeral_i s#ctx#z3 1)];
  let rec search size =
    logf "Searching for model of size: %d" size;
    Solver.add s#z3
      [Boolean.mk_eq
         s#ctx#z3
         s#ctx#const_universe
         (Arithmetic.Integer.mk_numeral_i s#ctx#z3 size)];
    match s#get_model () with
    | `Sat m -> m
    | _ -> search (size + 1)
  in
  let result =
    match s#get_model () with
    | `Sat m -> `Sat (search 1)
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
  in
  s#pop ();
  result

let get_min_model s =
  s#push ();
  Solver.add s#z3
    [Arithmetic.mk_gt
       s#ctx#z3
       s#ctx#const_universe
       (Arithmetic.Integer.mk_numeral_i s#ctx#z3 1)];
  let rec minimize m lo hi =
    if lo = hi then m
    else
      let mid = lo + ((hi - lo) / 2) in
      (*      logf "Minimizing model.  Size: %d" hi;*)
      s#push ();
      Solver.add s#z3
        [Arithmetic.mk_le
           s#ctx#z3
           s#ctx#const_universe
           (Arithmetic.Integer.mk_numeral_i s#ctx#z3 mid)];
      match s#get_model () with
      | `Sat m -> (s#pop (); minimize m lo (m#eval_int s#ctx#const_universe))
      | `Unsat -> (s#pop (); minimize m (mid + 1) hi)
      | _ -> m
  in
  let result =
    match s#get_model () with
    | `Sat m ->
      let m = minimize m 1 (m#eval_int s#ctx#const_universe) in
      `Sat (m, m#eval_int s#ctx#const_universe)
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
  in
  s#pop ();
  result

let rec simplify_children add_star s children =
  let equal x y = x = y in
  let changed = ref false in
  let rec go simplified = function
    | [] -> simplified
    | (phi::phis) ->
      s#push ();
      List.iter add_star simplified;
      List.iter add_star phis;
      let simple_phi = simplify_dillig_impl phi s in
      s#pop ();
      if not (equal phi simple_phi) then changed := true;
      go (simple_phi::simplified) phis
  in
  (*
  let rec fix children =
    let simplified = go [] children in
    if !changed then begin
      changed := false;
      fix simplified
    end else simplified
  in
  fix children*)
  go [] (go [] children)

and simplify_dillig_impl phi s =
  match F.destruct_flatten phi with
  | `T -> F.mk_true
  | `F -> F.mk_false
  | `Atom (_, _) ->
    s#push ();
    s#add phi;
    let simplified =
      match s#check () with
      | `Unknown -> phi
      | `Unsat -> F.mk_false
      | `Sat ->
        s#pop ();
        s#push ();
        s#add_not phi;
        match s#check () with
        | `Unknown -> phi
        | `Unsat -> F.mk_true
        | `Sat -> phi
    in
    (*    logf "Solver: %s" (Solver.to_string s#z3);*)
    s#pop ();
    (*
    logf "Simplified: %a -> %a"
      (format Format.pp_print_string Format.pp_print_int) phi
      (format Format.pp_print_string Format.pp_print_int) simplified;
*)
    simplified
  | `Or xs -> F.big_disj (BatList.enum (simplify_children s#add_not s xs))
  | `And xs -> F.big_conj (BatList.enum (simplify_children s#add s xs))
  | `Forall (_,_) | `Exists (_,_) -> invalid_arg "quantifier-free"
  | `Eq (_,_) | `Neq(_,_) -> invalid_arg "equality-free"

let simplify_dillig ctx phi = simplify_dillig_impl phi (new solver ctx)
