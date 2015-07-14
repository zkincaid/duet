open Apak
open BatPervasives

include Log.Make(struct let name = "pa" end)

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
