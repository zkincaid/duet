open Apak
open BatPervasives

module type Sigma = sig
  include Putil.Hashed.S
end

module type Predicate = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val format : Format.formatter -> t -> unit
end

include Log.Make(struct let name = "ipa" end)

module Make (A : Sigma) (P : Predicate) = struct

  module HT = BatHashtbl.Make(struct
      type t = P.t * A.t
      let equal (p, a) (q, b) = P.equal p q && A.equal a b
      let hash (p, a) = Hashtbl.hash (P.hash p, A.hash a)
    end)

  type predicate = P.t
  module Show_predicate = Deriving_Show.Defaults(struct
      type a = predicate
      let format = P.format
  end)
  module Compare_predicate = Deriving_Compare.Defaults(struct
      type a = predicate
      let compare = P.compare
  end)

  type formula =
    | And of formula * formula
    | Or of formula * formula
    | Atom of predicate * int list
    | True
    | False
    | Eq of int * int
    | Neq of int * int
               deriving (Show)

  type atom = predicate * int list
                deriving (Show,Compare)

  type t =
    { delta : formula HT.t;
      mutable sigma : A.t list;
      mutable accepting : P.t -> bool;
      mutable initial : formula; }

  (* A configuration is a finite structure over the vocabulary of the PA.  A
     configuration is identified with the set of propositions which hold in
     it. *)
  module Config = struct
    module E = Putil.Set.Make(struct
        type t = atom
            deriving (Show, Compare)
        let compare = Compare_t.compare
        let format = Show_t.format
        let show = Show_t.show
      end)
    include E

    let hash config =
      Hashtbl.hash (List.map
                      (fun (p, args) -> (P.hash p, args))
                      (elements config))

    (* Sets of configurations correspond to the DNF of some formula *)
    module Set = Putil.Set.Make(E)

    let conj x y =
      BatEnum.map
        (fun (x,y) -> E.union x y)
        (ApakEnum.cartesian_product (Set.enum x) (Set.enum y))
      |> Set.of_enum

    (* Given a constant k and a configuration c = 
           p_1(a_11, ..., a_1n)
        /\        ...
        /\ p_m(a_m1, ..., a_ml)

       We define the signature of k in c to be the set of all (p_i, j) such
       that a_ij = k.  If C, C' are configurations such that C' covers C, the
       embedding of C' into C must map each k' in C' to a constant k in C such
       that the signature of k' in C' is a subset of the signature of k in
       C. *)
    module Sig = Putil.Set.Make(struct
        type t = predicate * int
                   deriving (Show,Compare)
        let compare = Compare_t.compare
        let format = Show_t.format
        let show = Show_t.show
      end)

    module KSet = Putil.Set.Make(Putil.PInt)
    module KMap = BatMap.Make(Putil.PInt)

    (* Compute the signature of a constant in some configuration *)
    let mk_sig i config =
      let f (head,args) sg =
        let g pos j sg =
          if i = j then Sig.add (head,pos) sg
          else sg
        in
        BatEnum.foldi g sg (BatList.enum args)
      in
      fold f config Sig.empty

    let constants config =
      let f (head, args) constants =
        List.fold_left (fun s x -> KSet.add x s) constants args
      in
      fold f config KSet.empty

    let mk_sig_map config =
      let f k map = KMap.add k (mk_sig k config) map in
      KSet.fold f (constants config) KMap.empty

    let covers x y =
      (cardinal x <= cardinal y)
      && (subset x y || begin
          let x_sigs = mk_sig_map x in
          let y_sigs = mk_sig_map y in
          let check map =
            let f (head,args) =
              mem (head, List.map (fun x -> KMap.find x map) args) y
            in
            for_all f x
          in
          let rec go xs y_sigs map = match xs with
            | [] -> check map
            | (x::xs) ->
              let x_sig = KMap.find x x_sigs in
              let f (y,y_sig) =
                Sig.subset x_sig y_sig
                &&
                (go xs (KMap.remove y y_sigs) (KMap.add x y map))
              in
              BatEnum.exists f (KMap.enum y_sigs)
          in
          go (KSet.elements (constants x)) y_sigs KMap.empty
        end)
  end

  (* A configuration is accepting if it contains only accepting predicates *)
  let accept pa config =
    Config.for_all (fun (x,_) -> pa.accepting x) config

  let find_transition pa predicate alpha =
    try HT.find pa.delta (predicate, alpha)
    with Not_found -> False

  let add_transition pa predicate alpha formula =
    try
      let old = HT.find pa.delta (predicate, alpha) in
      HT.replace pa.delta (predicate, alpha) (Or (old, formula))
    with Not_found -> HT.add pa.delta (predicate, alpha) formula

  let make ?(delta=[]) sigma accepting initial =
    let pa =
      { delta = HT.create 991;
        sigma = sigma;
        accepting = accepting;
        initial = initial }
    in
    let add_delta (predicate, alpha, formula) =
      add_transition pa predicate alpha formula
    in
    List.iter add_delta delta;
    pa

  module PSet = BatSet.Make(P)
  let rec formula_predicates = function
    | True | False | Eq (_, _) | Neq (_, _) -> PSet.empty
    | Atom (p, _) -> PSet.singleton p
    | And (phi, psi) | Or (phi, psi) -> 
      PSet.union (formula_predicates phi) (formula_predicates psi)

  (* Get the set of all predicates which are used by a given PA *)
  let predicates pa =
    let formulas = HT.values pa.delta in
    BatEnum.push formulas pa.initial;
    BatEnum.fold
      (fun set phi -> PSet.union (formula_predicates phi) set)
      (PSet.of_enum (HT.keys pa.delta /@ fst))
      formulas

  let combine_bang pa qa =
    if not (BatList.for_all2 (fun a b -> A.equal a b) pa.sigma qa.sigma)
    then invalid_arg "Can't combine: PAs must have equal alphabets";
    let f (p, a) phi = add_transition pa p a phi in
    let old_accepting = pa.accepting in
    let qa_accepting = qa.accepting in
    pa.accepting <- (fun p -> old_accepting p || qa_accepting p);
    HT.iter f qa.delta

  let union_bang pa qa =
    if not (PSet.is_empty (PSet.inter (predicates pa) (predicates qa)))
    then invalid_arg "Can't union: PAs must have disjoint predicates";
    combine_bang pa qa;
    pa.initial <- Or (pa.initial, qa.initial) (* wrong! *)

  let intersect_bang pa qa =
    if not (PSet.is_empty (PSet.inter (predicates pa) (predicates qa)))
    then invalid_arg "Can't intersect: PAs must have disjoint predicates";
    combine_bang pa qa;
    pa.initial <- And (pa.initial, qa.initial) (* wrong! *)

  let copy pa =
    { delta = HT.copy pa.delta;
      sigma = pa.sigma;
      accepting = pa.accepting;
      initial = pa.initial }

  let union pa qa =
    let ra = copy pa in
    union_bang ra qa;
    ra

  let intersect pa qa =
    let ra = copy pa in
    intersect_bang ra qa;
    ra

  let big_conj conjuncts =
    if BatEnum.peek conjuncts = None then True
    else BatEnum.reduce (fun x y -> And (x, y)) conjuncts
  let big_disj disjuncts =
    if BatEnum.peek disjuncts = None then True
    else BatEnum.reduce (fun x y -> Or (x, y)) disjuncts

  (* Negates a formula, except that atomic (non-equality) propositions are
     left untouched. *)
  let rec negate_formula = function
    | And (phi, psi) -> Or (negate_formula phi, negate_formula psi)
    | Or (phi, psi) -> And (negate_formula phi, negate_formula psi)
    | Atom (p, args) -> Atom (p, args)
    | Eq (i, j) -> Neq (i, j)
    | Neq (i, j) -> Eq (i, j)
    | True -> False
    | False -> True

  let negate pa =
    let predicates = predicates pa in
    let accept p = PSet.mem p predicates && not (pa.accepting p) in
    let neg_pa =
      make pa.sigma accept (negate_formula pa.initial)
    in
    let f (p, a) =
      let phi =
        try negate_formula (HT.find pa.delta (p, a))
        with Not_found -> True
      in
      add_transition neg_pa p a phi
    in
    let sigma = BatList.enum pa.sigma in
    BatEnum.iter f (ApakEnum.cartesian_product (PSet.enum predicates) sigma);
    neg_pa

  let next pa (head, actuals) (alpha, i) =
    (* env maps formal variables which appear in transition rules to their
       actual parameters *)
    let env = Array.make (List.length actuals + 1) 0 in
    env.(0) <- i;
    BatList.iteri
      (fun formal actual -> env.(formal+1) <- actual)
      actuals;
    let subst i = env.(i) in

    let rec eval = function
      | And (phi, psi) -> And (eval phi, eval psi)
      | Or (phi, psi) -> Or (eval phi, eval psi)
      | Atom (p, args) -> Atom (p, List.map subst args)
      | True -> True
      | False -> False
      | Eq (s, t) -> if env.(s) = env.(t) then True else False
      | Neq (s, t) -> if env.(s) = env.(t) then False else True
    in
    try eval (find_transition pa head alpha)
    with Invalid_argument _ -> begin
        Log.errorf "Invalid transition!";
        Log.errorf "%a%a --([#%d] %a)--> %a"
          P.format head
          Show.format<int list> actuals
          i
          A.format alpha
          Show.format<formula> (find_transition pa head alpha);
        assert false
      end

  type abs =
    { abs_delta : P.t * int list -> A.t * int -> formula;
      abs_sigma : A.t list;
      mutable abs_predicates : PSet.t;
      mutable abs_accepting : P.t -> bool;
      mutable abs_initial : formula; }

  let mk_abstract pa =
    let predicates = predicates pa in
    { abs_delta = next pa;
      abs_sigma = pa.sigma;
      abs_predicates = predicates;
      abs_accepting = pa.accepting;
      abs_initial = pa.initial }

  let abs_next pa config (alpha, i) =
    let rec eval = function
      | And (phi, psi) -> Config.conj (eval phi) (eval psi)
      | Or (phi, psi) -> Config.Set.union (eval phi) (eval psi)
      | Atom (p, args) ->
        Config.Set.singleton (Config.singleton (p, args))
      | True -> Config.Set.singleton Config.empty
      | False -> Config.Set.empty
      | Eq (s, t) -> if s = t then (eval True) else (eval False)
      | Neq (s, t) -> if s = t then (eval False) else (eval True)
    in
    let rewrite head actuals =
      eval (pa.abs_delta (head, actuals) (alpha, i))
    in
    Config.fold
      (fun (head, actuals) eval -> Config.conj (rewrite head actuals) eval)
      config
      (Config.Set.singleton Config.empty)
  let abs_accept pa config =
    Config.for_all (fun (x,_) -> pa.abs_accepting x) config

  let enum_delta pa = HT.enum pa.delta /@ (fun ((l,a),r) -> (l,a,r))

  exception Accepting of Config.t
  (* Reachability graph *)
  module Rg = struct
    module CHT = BatHashtbl.Make(Config)
    type t =
      { mutable worklist : Config.t list;
        successor : Config.Set.t CHT.t;
        parent : (A.t * int * Config.t) CHT.t;
        cover : Config.t CHT.t }
    let vertices rg = CHT.keys rg.successor
    let expand rg (pa : abs) config =
      logf ~level:`trace ~attributes:[`Blue;`Bold]
        "Expanding vertex: %a" Config.format config;
      let used_constants = Config.constants config in
      let fresh =
        if Config.KSet.cardinal used_constants > 0
        then 1 + Config.KSet.fold max used_constants 0
        else 0
      in
      let constants = Config.KSet.add fresh used_constants in
      let labels =
        ApakEnum.cartesian_product
          (BatList.enum pa.abs_sigma)
          (Config.KSet.enum constants)
      in
      let label_succ (alpha, k) =
        logf ~level:`trace " + Action: <%d, %a>" k A.format alpha;
        let succs = abs_next pa config (alpha, k) in
        begin
          try
            let all_succs =
              Config.Set.union succs (CHT.find rg.successor config)
            in
            CHT.replace rg.successor config all_succs
          with Not_found -> CHT.add rg.successor config succs
        end;

        let add_succ succ =
          if CHT.mem rg.parent succ || CHT.mem rg.successor succ
          then logf ~level:`trace "   - Skipped vertex: %a" Config.format succ
          else begin
            logf ~level:`trace "   - Added successor: %a" Config.format succ;
            CHT.add rg.parent succ (alpha, k, config);
            if abs_accept pa succ then raise (Accepting succ);
            rg.worklist <- succ::rg.worklist
          end
        in
        Config.Set.iter add_succ succs
      in
      BatEnum.iter label_succ labels

    let close rg pa config =
      try
        let cover = BatEnum.find (flip Config.covers config) (vertices rg) in
        CHT.add rg.cover config cover;
        logf ~level:`trace ~attributes:[`Green;`Bold] "Covered vertex: %a"
          Config.format config;
        logf ~level:`trace " by %a" Config.format cover;
        true
      with Not_found -> false
         | _ -> assert false
  end

  let abs_empty pa =
    let open Rg in
    let rec fix rg =
      match rg.worklist with
      | (config::rest) ->
        rg.worklist <- rest;
        if not (close rg pa config) then expand rg pa config;
        fix rg
      | [] -> ()
    in
    let rec eval = function
      | And (phi, psi) -> Config.conj (eval phi) (eval psi)
      | Or (phi, psi) -> Config.Set.union (eval phi) (eval psi)
      | Atom (p, rgs) -> Config.Set.singleton (Config.singleton (p, rgs))
      | True -> Config.Set.singleton Config.empty
      | False -> Config.Set.empty
      | Eq (_, _) | Neq (_, _) ->
        invalid_arg "Pa: equalities not allowed in initial formula!"
    in
    let eval x = try eval x with _ -> assert false in

    let rg =
      try
        { worklist = Config.Set.elements (eval pa.abs_initial);
          successor = CHT.create 991;
          parent = CHT.create 991;
          cover = CHT.create 991 }
      with _ -> assert false
    in
    let rec path_to_root v path =
      try
        let (a,i,p) = CHT.find rg.parent v in
        path_to_root p ((a,i)::path)
      with Not_found -> path
         | _ -> assert false
    in
    if List.exists (abs_accept pa) rg.worklist then Some [] else
      try
        (fix rg); None
      with Accepting v -> Some (path_to_root v [])
  let abs_empty pa = Log.time "PA emptiness" abs_empty pa
  let abs_empty pa = abs_empty pa

  let empty pa = abs_empty (mk_abstract pa)
  let abs_intersect pa qa =
    if not (PSet.is_empty (PSet.inter pa.abs_predicates qa.abs_predicates))
    then invalid_arg "Can't intersect: PAs must have disjoint predicates";
    let delta (p,args) a =
      if PSet.mem p pa.abs_predicates then pa.abs_delta (p,args) a
      else qa.abs_delta (p,args) a
    in
    let accept p =
      (PSet.mem p pa.abs_predicates && pa.abs_accepting p)
      || (PSet.mem p qa.abs_predicates && qa.abs_accepting p)
    in
    { abs_delta = delta;
      abs_sigma = pa.abs_sigma;
      abs_predicates = PSet.union pa.abs_predicates qa.abs_predicates;
      abs_accepting = accept;
      abs_initial = And (pa.abs_initial, qa.abs_initial) }

  let abs_negate pa =
    let delta p a = negate_formula (pa.abs_delta p a) in
    let accept p = not (pa.abs_accepting p) in
    { abs_delta = delta;
      abs_sigma = pa.abs_sigma;
      abs_predicates = pa.abs_predicates;
      abs_accepting = accept;
      abs_initial = (negate_formula pa.abs_initial) }
end


module Verify = struct
  open Core
  open Ark
  open Ark.Syntax

  let tr_typ typ =
    match resolve_type typ with
      | Int _   -> TyInt
      | Float _ -> TyReal
      | Pointer _ -> TyInt
      | Enum _ -> TyInt
      | Array _ -> TyInt
      | Dynamic -> TyReal
      | _ -> TyInt

  module PInt = Putil.PInt

  module IV = struct
    module I = struct
      type t = Var.t * int deriving (Compare)
      include Putil.MakeFmt(struct
          type a = t
          let format formatter (var, i) =
            if Var.is_shared var then Var.format formatter var
            else Format.fprintf formatter "%a[#%d]" Var.format var i
        end)
      let compare = Compare_t.compare
      let equal x y = compare x y = 0
      let hash (v, i) = Hashtbl.hash (Var.hash v, i)
    end
    include I
    let typ = tr_typ % Var.get_type % fst
    let subscript (v, i) ss = (Var.subscript v ss, i)
  end

  let ctx = mk_context (module IV)
  let z3 = new Smt.context []
  let loc = Var.mk (Varinfo.mk_local "@" (Concrete (Int unknown_width)))

  module P = struct
    type t = Formula.t
    let hash = Formula.hash
    let equal = Formula.equal
    let compare = Formula.compare
    let format formatter phi = Formula.format ctx formatter phi
    let conj = Formula.mk_and ctx
    let disj = Formula.mk_or ctx
    let negate = Formula.mk_not ctx
    let tru = Formula.mk_true ctx
    let fls = Formula.mk_false ctx
    let leq = Formula.mk_leq ctx
    let lt = Formula.mk_lt ctx
    let eq = Formula.mk_eq ctx
    let constants = Formula.constants
    let substitute = Formula.substitute ctx
    let substitute_const = Formula.substitute_const ctx
    let existential_closure = Formula.existential_closure ctx
    let conjuncts phi =
      match Formula.destruct_flat phi with
      | `And conjuncts -> BatList.enum conjuncts
      | `Tru -> BatEnum.empty ()
      | _ -> BatEnum.singleton phi
    let big_conj = Formula.mk_conjunction ctx
    let big_disj = Formula.mk_disjunction ctx
  end
  module T = struct
    type t = Term.t
    let hash = Term.hash
    let equal = Term.equal
    let compare = Term.compare
    let var = Term.mk_var ctx
    let add = Term.mk_add ctx
    let mul = Term.mk_mul ctx
    let div = Term.mk_div ctx
    let modulo = Term.mk_mod ctx
    let floor = Term.mk_floor ctx
    let neg = Term.mk_neg ctx
    let sub = Term.mk_sub ctx
    let real = Term.mk_real ctx
    let int zz = Term.mk_real ctx (QQ.of_zz zz)
    let zero = Term.mk_zero ctx
    let one = Term.mk_zero ctx
    let program_var v = Term.mk_const ctx (symbol_of_const ctx v)
  end
  module PA = Make(Def)(P)

  module VarSet = struct
    module S = ConstSymbol.Set
    let enum cs = S.enum cs /@ (const_of_symbol ctx)
    let exists p cs = S.exists (p % (const_of_symbol ctx)) cs
    let mem elt cs = S.mem (symbol_of_const ctx elt) cs
  end

  let stable phi args def k =
    let program_vars = P.constants phi in
    match def.dkind with
    | Assign (v, expr) ->
      let p (v', k') =
        Var.equal loc v'
        || (Var.equal v v' && (Var.is_shared v || List.nth args (k' - 1) = k))
      in
      not (VarSet.exists p program_vars)
    | _ ->
      not (VarSet.exists (fun (v, _) -> Var.equal loc v) program_vars)

  (* Determine the arity of a predicate (i.e., the number of distinct threads
     whose local variables appear in the predicate).  This function assumes
     that expressions are "normal" in the sense that thread id's have been
     renamed to occupy an initial segment of the naturals. *)
  let arity phi =
    let f m (v, id) =
      if Var.is_shared v then max m id else m
    in
    1 + (BatEnum.fold f (-1) (VarSet.enum (P.constants phi)))

  (* Subscripting *)
  type ss =
    { ssglobal : int Var.Map.t;
      sslocal : (int Var.Map.t) PInt.Map.t }

  let ss_init =
    { ssglobal = Var.Map.empty;
      sslocal = PInt.Map.empty }

  let subscript ss i =
    let lookup map x =
      try Var.Map.find x map
      with Not_found -> 0
    in
    let local =
      try PInt.Map.find i ss.sslocal
      with Not_found -> Var.Map.empty
    in
    fun x ->
      if Var.is_shared x then IV.subscript (x,0) (lookup ss.ssglobal x)
      else IV.subscript (x,i) (lookup local x)

  let subscript_incr ss i x =
    let lookup map x =
      try Var.Map.find x map
      with Not_found -> 0
    in
    if Var.is_shared x then
      { ss with ssglobal = Var.Map.add x (1+lookup ss.ssglobal x) ss.ssglobal }
    else
      let local =
        try PInt.Map.find i ss.sslocal
        with Not_found -> Var.Map.empty
      in
      let sub = 1 + lookup local x in
      { ss with sslocal = PInt.Map.add i (Var.Map.add x sub local) ss.sslocal }

  let gensym =
    let n = ref (-1) in
    fun () -> incr n; !n

  let subscript_expr ss i =
    let subscript = subscript ss i in
    let alg = function
      | OHavoc typ -> T.var (gensym ()) (tr_typ typ)
      | OConstant (CInt (k, _)) -> T.int (ZZ.of_int k)
      | OConstant (CFloat (k, _)) -> T.real (QQ.of_float k)
      | OCast (_, expr) -> expr
      | OBinaryOp (a, Add, b, _) -> T.add a b
      | OBinaryOp (a, Mult, b, _) -> T.mul a b
      | OBinaryOp (a, Minus, b, _) -> T.sub a b

      | OUnaryOp (Neg, a, _) -> T.neg a

      | OAccessPath (Variable v) -> T.program_var (subscript v)

      (* No real translations for anything else -- just return a free var "tr"
         (which just acts like a havoc). *)
      | OBinaryOp (a, _, b, typ) -> T.var (gensym ()) (tr_typ typ)
      | OUnaryOp (_, _, typ) -> T.var (gensym ()) (tr_typ typ)
      | OBoolExpr _ -> T.var (gensym ()) TyInt
      | OAccessPath ap -> T.var (gensym ()) (tr_typ (AP.get_type ap))
      | OConstant _ -> T.var (gensym ()) TyInt
      | OAddrOf _ -> T.var (gensym ()) TyInt
    in
    Expr.fold alg

  let unsubscript =
    let sigma v = T.program_var (fst (const_of_symbol ctx v), 0) in
    P.substitute_const sigma

  let subscript_bexpr ss i bexpr =
    let subscript = subscript_expr ss i in
    let alg = function
      | Core.OAnd (a, b) -> P.conj a b
      | Core.OOr (a, b) -> P.disj a b
      | Core.OAtom (pred, x, y) ->
        let x = subscript x in
        let y = subscript y in
        begin
          match pred with
          | Lt -> P.lt x y
          | Le -> P.leq x y
          | Eq -> P.eq x y
          | Ne -> P.negate (P.eq x y)
        end
    in
    P.existential_closure (Bexpr.fold alg bexpr)

  let generalize_atom phi =
    let subst = BatDynArray.make 10 in
    let rev_subst = BatHashtbl.create 31 in
    let generalize i =
      try BatHashtbl.find rev_subst i
      with Not_found -> begin
          let id = BatDynArray.length subst in
          BatHashtbl.add rev_subst i id;
          BatDynArray.add subst i;
          id
        end
    in
    let sigma v =
      let (v, tid) = const_of_symbol ctx v in
      let iv =
        if Var.is_shared v then (v, tid) else (v, 1 + generalize tid)
      in
      T.program_var (IV.subscript iv 0)
    in
    let gen_phi = P.substitute_const sigma phi in
    (gen_phi, BatDynArray.to_list subst)

  let generalize i phi psi =
    let subst = BatDynArray.make 10 in
    let rev_subst = BatHashtbl.create 31 in
    BatDynArray.add subst i;

    let generalize i =
      try BatHashtbl.find rev_subst i
      with Not_found -> begin
          let id = BatDynArray.length subst in
          BatHashtbl.add rev_subst i id;
          BatDynArray.add subst i;
          id
        end
    in
    let sigma v =
      let (v, tid) = const_of_symbol ctx v in
      let iv =
        if Var.is_shared v then (v, tid) else (v, generalize tid)
      in
      T.program_var (IV.subscript iv 0)
    in
    let gen_phi = P.substitute_const sigma phi in
    BatHashtbl.add rev_subst i 0;
    let f psi =
      let (gen_psi, args) = generalize_atom psi in
      PA.Atom (gen_psi, List.map generalize args)
    in
    let mk_eq ((i,j), (k,l)) = if i = k then PA.Eq (j,l) else PA.Neq (j,l) in

    let rhs =
      PA.big_conj
        (BatEnum.append
           (BatEnum.map f (P.conjuncts psi))
           (ApakEnum.distinct_pairs (BatHashtbl.enum rev_subst) /@ mk_eq))
    in
    (subst, gen_phi, rhs)
  let generalize i phi psi =
    try generalize i phi psi
    with _ -> assert false

  (* Given a trace <a_0 : i_0> ... <a_n : i_n>, produces the sequence
     (a_0, i_0, phi_0) ... (a_n, i_n, phi_n)
     where the sequence of phis is the SSA form of the trace.
  *)
  let trace_formulae trace =
    let f (def, i) (ss, rest) = match def.dkind with
      | Assume phi -> (ss, (i, def, subscript_bexpr ss i phi)::rest)
      | Assign (v, expr) ->
        let rhs = subscript_expr ss i expr in
        let ss' = subscript_incr ss i v in
        let assign =
          P.eq (T.program_var (subscript ss' i v)) rhs
          |> P.existential_closure
        in
        (ss', (i, def, assign)::rest)
      | _ -> (ss, (i, def, P.tru)::rest)
    in
    snd (List.fold_right f trace (ss_init, []))

  let construct ipa trace =
    let rec go post = function
      | ((i, tr, phi)::rest) ->
        let phis = BatList.map (fun (_,_,phi) -> phi) rest in
        let a = P.big_conj (BatList.enum phis) in
        let b = P.conj phi (P.negate post) in
        let itp = match z3#interpolate_seq ctx [a; b] with
          | Some [itp] ->
            (Log.logf ~level:`trace "Found interpolant!@\n%a / %a: %a"
               P.format a P.format b P.format itp;
             assert (Smt.implies z3 a itp);
             assert (Smt.is_sat z3 (P.conj itp b) = `Unsat);
             itp)
          | _ ->
            (Log.errorf "Failed to interpolate! %a / %a"
               P.format a P.format b;
             assert false)
        in
        if P.compare (unsubscript post) (unsubscript itp) = 0 then begin
          Log.logf "Skipping transition: [#%d] %a" i Def.format tr;
          go itp rest
        end else begin
          BatEnum.iter (flip go rest) (P.conjuncts itp);
          let (_, lhs, rhs) = generalize i post itp in

          Log.logf
            "Added PA transition:@\n @[%a@]@\n --( [#0] %a )-->@\n @[%a@]"
            P.format lhs
            Def.format tr
            Show.format<PA.formula> rhs;
          PA.add_transition ipa lhs tr rhs
        end

      | [] -> assert false
    in
    go P.fls (trace_formulae trace)
  let construct ipa trace =
    Log.time "PA construction" (construct ipa) trace

  module PHT = Hashtbl.Make(P)
  module PSet = BatSet.Make(P)

  let program_automaton file rg =
    let open Interproc in
    let main = match file.CfgIr.entry_points with
      | [x] -> x
      | _   -> failwith "PA: No support for multiple entry points"
    in

    let sigma = ref [] in
    let preds = ref PSet.empty in
    let add_pred p = preds := PSet.add p (!preds) in
    let main_locs = ref PSet.empty in

    (* Map each control location to a unique predicate symbol *)
    let loc_pred def =
      P.eq (T.program_var (loc,1)) (T.real (QQ.of_int def.did))
    in

    (* Map control locations to their successors *)
    let next = PHT.create 991 in
    let add_next u v =
      let u,v = loc_pred u, loc_pred v in
      try PHT.replace next u (PSet.add v (PHT.find next u))
      with Not_found -> PHT.add next u (PSet.singleton v)
    in
    let get_next v =
      try PHT.find next v
      with Not_found -> PSet.empty
    in

    (* Each thread gets a new initial vertex.  If some thread is in the
       initial location, the only transition that can be executed is a fork
       which spawns that thread. *)
    let thread_init = PHT.create 31 in
    let add_thread_init thread =
      let init = Def.mk Initial in
      let entry = RG.block_entry rg thread in
      sigma := init::(!sigma);
      add_pred (loc_pred init);
      add_next init entry;
      PHT.add thread_init (loc_pred init) thread
    in

    (* Error location; must replace asserts with guarded transitions to
       error. *)
    let err = Def.mk (Assume Bexpr.ktrue) in
    add_pred (loc_pred err);

    (* Transitions to the error state *)
    let err_tr = Def.HT.create 61 in
    let add_err_tr def phi =
      let guard =
        Def.mk ~loc:(Def.get_location def) (Assume (Bexpr.negate phi))
      in
      sigma := guard::(!sigma);
      Def.HT.add err_tr guard (loc_pred def)
    in

    let delta (p, args) (a,i) =
      match args with
      | [] -> (* loc *)
        if Def.HT.mem err_tr a
        then PA.And (PA.Atom (p, []),
                     PA.Atom (Def.HT.find err_tr a, [i]))
        else PA.And (PA.Atom (p, []),
                     PA.Atom (loc_pred a, [i]))
      | [j] ->
        if PHT.mem thread_init p then begin
          match a.dkind with
          | Builtin (Fork (_, expr, _)) ->
            let func = match Expr.strip_casts expr with
              | AddrOf (Variable (func, OffsetFixed 0)) -> func
              | _ -> assert false
            in
            if Varinfo.equal (PHT.find thread_init p) func && i != j
            then PA.True
            else PA.False
          | _ -> PA.False
        end else
        if P.equal p (loc_pred err) && Def.HT.mem err_tr a then
          if i = j then PA.Atom (Def.HT.find err_tr a, [i])
          else PA.False
        else if i = j && PSet.mem p (get_next (loc_pred a)) then PA.True
        else if i != j && not (PSet.mem (loc_pred a) (!main_locs))
        then PA.Atom (p, args)
        else PA.False
      | _ -> assert false
    in

    (* loc predicate ensure that whenever a new thread executes a command its
       program counter is instantiated properly. *)
    let loc = P.tru in
    add_pred loc;

    BatEnum.iter (fun (thread, body) ->
        RG.G.iter_edges (fun u v -> add_next u v) body;
        RG.G.iter_vertex (fun u ->
            sigma := u::(!sigma);
            add_pred (loc_pred u);
            match u.dkind with
            | Assert (phi, _) -> add_err_tr u phi
            | _ -> ()
          ) body;
        if not (Varinfo.equal thread main) then add_thread_init thread
      ) (RG.bodies rg);
    RG.G.iter_vertex (fun d ->
        main_locs := PSet.add (loc_pred d) (!main_locs)
      ) (RG.block_body rg main);
    let accept =
      let entry = RG.block_entry rg main in
      (fun p -> P.equal (loc_pred entry) p || P.equal loc p)
    in
    { PA.abs_delta = delta;
      PA.abs_sigma = !sigma;
      PA.abs_predicates = !preds;
      PA.abs_accepting = accept;
      PA.abs_initial = PA.And (PA.Atom (loc_pred err, [0]), PA.Atom (loc, [])) }

  let verify file =
    let open PA in
    let rg = Interproc.make_recgraph file in
    let program_pa = program_automaton file rg in
    let pf =
      PA.make program_pa.abs_sigma (fun _ -> false) (Atom (P.fls, []))
    in
    let abstract_pf pf =
      let open PA in
      let delta (p,args) (a,i) =
        if stable p args a i
        then Or (Atom (p, args), next pf (p,args) (a,i))
        else next pf (p,args) (a,i)
      in
      { abs_predicates = PSet.add P.fls (predicates pf);
        abs_delta = delta;
        abs_sigma = pf.sigma;
        abs_accepting = pf.accepting;
        abs_initial = pf.initial
      }
    in
    let check pf =
      abs_empty (abs_intersect program_pa (abs_negate (abstract_pf pf)))
      (* (mk_abstract pf)))*)
    in
    let number_cex = ref 0 in
    let print_info () =
      logf ~level:`info "  PA transitions: %d"
        (BatEnum.count (PA.enum_delta pf));
      logf ~level:`info "  Spurious counter-examples: %d " !number_cex;
    in
    let rec loop () =
      match check pf with
      | Some trace ->
        logf ~attributes:[`Bold] "@\nFound error trace (%d):" (!number_cex);
        List.iter (fun (def, id) ->
            logf "  [#%d] %a" id Def.format def
          ) (List.rev trace);
        logf ""; (* newline *)
        let trace_formula =
          BatList.enum (trace_formulae trace)
          /@ (fun (_,_,phi) -> phi) |> P.big_conj
        in
        begin
          match Smt.is_sat z3 trace_formula with
          | `Sat ->
            log ~level:`always ~attributes:[`Bold;`Red]
              "Verification result: Unsafe";
            print_info ();
            logf ~level:`info ~attributes:[`Bold] "  Error trace:";
            List.iter (fun (def, id) ->
                logf ~level:`info "    [#%d] %a" id Def.format def
              ) trace
          | `Unsat ->
            construct pf trace;
            incr number_cex;
            loop ()
          | `Unknown ->
            log ~level:`always ~attributes:[`Bold;`Red]
              "Verification result: Unknown";
            print_info ();
            logf ~level:`info ~attributes:[`Bold] "  Could not verify trace:";
            List.iter (fun (def, id) ->
                logf ~level:`info "    [#%d] %a" id Def.format def
              ) trace
        end
      | None ->
        log ~level:`always ~attributes:[`Bold;`Green]
          "Verification result: Safe";
        print_info ()
    in
    loop ()
end


let _ =
  CmdLine.register_pass
    ("-ipa", Verify.verify, " Inductive predicate automata")
