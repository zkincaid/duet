(*pp camlp4find deriving.syntax *)

open Apak
open BatPervasives

module type Sigma = sig
  include Putil.Hashed.S
end

module type Predicate = sig
  include Putil.Hashed.S
  include Putil.OrderedMix with type t := t
  type alpha
  val stable : t -> int list -> alpha -> int -> bool
end

include Log.Make(struct let name = "ipa" end)

module Make (A : Sigma) (P : Predicate with type alpha = A.t) = struct

  module HT = BatHashtbl.Make(struct
    type t = P.t * A.t
    let equal (p, a) (q, b) = P.equal p q && A.equal a b
    let hash (p, a) = Hashtbl.hash (P.hash p, A.hash a)
  end)

  type formula =
  | And of formula * formula
  | Or of formula * formula
  | Atom of P.t * int list
  | True
  | False
  | Eq of int * int
  | Neq of int * int 
      deriving (Show)

  type atom = P.t * int list
    deriving (Show,Compare)

  type t =
    { delta : formula HT.t;
      sigma : A.t list;
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
	(Putil.cartesian_product (Set.enum x) (Set.enum y))
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
      type t = P.t * int
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

  module PSet = Putil.Set.Make(P)
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
    BatEnum.iter f (Putil.cartesian_product (PSet.enum predicates) sigma);
    neg_pa

  let next pa config alpha i =
    let rewrite head actuals =
      (* env maps formal variables which appear in transition rules to their
	 actual parameters *)
      let env = Array.make (List.length actuals + 1) 0 in
      env.(0) <- i;
      BatList.iteri
	(fun formal actual -> env.(formal+1) <- actual)
	actuals;
      let subst i = env.(i) in

      let rec eval = function
	| And (phi, psi) -> Config.conj (eval phi) (eval psi)
	| Or (phi, psi) -> Config.Set.union (eval phi) (eval psi)
	| Atom (p, args) ->
	  Config.Set.singleton (Config.singleton (p, List.map subst args))
	| True -> Config.Set.singleton Config.empty
	| False -> Config.Set.empty
	| Eq (s, t) ->
	  if env.(s) = env.(t) then (eval True)
	  else (eval False)
	| Neq (s, t) ->
	  if env.(s) = env.(t) then (eval False)
	  else (eval True)
      in
      let res = eval (find_transition pa head alpha) in
      let res =
      if P.stable head actuals alpha i
      then Config.Set.add (Config.singleton (head, actuals)) res
      else res
      in
      if Config.Set.is_empty res
      then logf ~level:Log.bottom "Nowhere to go: %a" P.format head
      else begin
	logf ~level:Log.bottom "%a -> %a" P.format head Config.Set.format res
      end;
      res
    in
    let res =
    Config.fold
      (fun (head, actuals) eval -> Config.conj (rewrite head actuals) eval)
      config
      (Config.Set.singleton Config.empty)
    in
    logf ~level:Log.bottom
      "Next: %a => %a" Config.format config Config.Set.format res;
    res

  exception Accepting of Config.t
  module Arg = struct
    module CHT = BatHashtbl.Make(Config)
    type t =
      { mutable worklist : Config.t list;
	successor : Config.Set.t CHT.t;
	parent : (A.t * int * Config.t) CHT.t;
	cover : Config.t CHT.t }
    let vertices arg = CHT.keys arg.successor
    let expand arg pa config =
      logf ~attributes:[Log.Blue;Log.Bold]
	"Expanding vertex: %a" Config.format config;
      let used_constants = Config.constants config in
      let fresh =
	if Config.KSet.cardinal used_constants > 0
	then 1 + Config.KSet.fold max used_constants 0
	else 0
      in
      let constants = Config.KSet.add fresh used_constants in
      let labels =
	Putil.cartesian_product
	  (BatList.enum pa.sigma)
	  (Config.KSet.enum constants)
      in
      let label_succ (alpha, k) =
	logf " + Action: <%d, %a>" k A.format alpha;
	let succs = next pa config alpha k in
	begin
	  try
	    let all_succs =
	      Config.Set.union succs (CHT.find arg.successor config)
	    in
	    CHT.replace arg.successor config all_succs
	  with Not_found -> CHT.add arg.successor config succs
	end;

	let add_succ succ =
	  if CHT.mem arg.parent succ || CHT.mem arg.successor succ
	  then logf "   - Skipped vertex: %a" Config.format succ
	  else begin
	    logf "   - Added successor: %a" Config.format succ;
	    CHT.add arg.parent succ (alpha, k, config);
	    if accept pa succ then raise (Accepting succ);
	    arg.worklist <- succ::arg.worklist
	  end
	in
	Config.Set.iter add_succ succs
      in
      BatEnum.iter label_succ labels

    let close arg pa config =
      try
	let cover = BatEnum.find (flip Config.covers config) (vertices arg) in
	CHT.add arg.cover config cover;
	logf ~attributes:[Log.Green;Log.Bold] "Covered vertex: %a"
	  Config.format config;
	logf " by %a" Config.format cover;
	true
      with Not_found -> false
  end

  let empty pa =
    let open Arg in
    let rec fix arg =
      match arg.worklist with
      | (config::rest) ->
	arg.worklist <- rest;
	if not (close arg pa config) then expand arg pa config;
	fix arg
      | [] -> ()
    in
    let rec eval = function
      | And (phi, psi) -> Config.conj (eval phi) (eval psi)
      | Or (phi, psi) -> Config.Set.union (eval phi) (eval psi)
      | Atom (p, args) -> Config.Set.singleton (Config.singleton (p, args))
      | True -> Config.Set.singleton Config.empty
      | False -> Config.Set.empty
      | Eq (_, _) | Neq (_, _) ->
	invalid_arg "Pa: equalities not allowed in initial formula!"
    in
    let arg =
      { worklist = Config.Set.elements (eval pa.initial);
	successor = CHT.create 991;
	parent = CHT.create 991;
	cover = CHT.create 991 }
    in
    let rec path_to_root v path =
      try
	let (a,i,p) = CHT.find arg.parent v in
	path_to_root p ((a,i)::path)
      with Not_found -> path
    in
    if List.exists (accept pa) arg.worklist then Some [] else
      try
	(fix arg); None
      with Accepting v -> Some (path_to_root v [])
end
