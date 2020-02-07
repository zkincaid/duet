(** Equality logic and Kleene algebras extending equality logic. *)

open Core
open Apak
open Srk

(** A "predicate" is any monoid (with multiplication interpreted as
    conjunction) with some notion of satisfiability and of variable
    substitution/existential quantification.  The {!subst} function does both
    existential quantification and substitution: variable which are mapped to
    None by the substitution function are existentially quantified, and
    variables mapped to Some v are substituted with v. *)
module type Predicate = sig
  include Sig.Monoid.Ordered.S
  type var
  val subst : (var -> var option) -> t -> t
  val implies : (var -> var) -> t -> t -> bool
end

module type Var = sig
  include Putil.Ordered
  val hash : t -> int
  val equal : t -> t -> bool
end

(** Conjunctive formulae *)
module type ConjFormula =
sig
  include Sig.Monoid.Ordered.S
  type var
  type eqs
  type pred

  (** Predicate determines which variables may appear in the resulting formula
      (i.e., which variables are NOT existentially quantified *)
  val exists : (var -> bool) -> t -> t
  val subst : (var -> var) -> t -> t
  val get_pred : t -> pred
  val get_eqs : t -> (var * var) list
  val get_eqs_canonical : t -> (var * var) list
  val get_subst : t -> (var -> var)
  val make : (var * var) list -> pred -> t
  val implies : t -> t -> bool
  val relprod : (var -> bool) -> t -> t -> t
end

(** Maintain a predicate modulo a theory consisting of a conjunction of a set
    of equalities. *)
module MakeEQ (V : Var) (P : Predicate with type var = V.t) : 
  ConjFormula with type var = V.t
               and type pred = P.t =
struct
  type var = V.t
  type pred = P.t
  module VMap = Putil.MonoMap.Make(V)(V)
  module VSet = Putil.Set.Make(V)
  module DS = Srk.DisjointSet.Make(V)

  (* There are two possible representations of a conjunction of equalities:
     - Canonical, which maps each variable to its equivalence class
     representitive (but doesn't map ECRs to anything)
     - Noncanonical, which is just a list of equations

     Noncanonical representation is faster for substitutions, conjunctions,
     etc, but we need the canonical form for existential quantification and
     comparison.  So we'll canonicalize lazily. *)
  type eqs =
    | Canonical of VMap.t
    | Noncanonical of (var * var) list

  type t =
    { mutable equalities : eqs;
      mutable predicates : pred }

  (* Disjoint set data structure used for canonicalization.  This is going to
     end up leaking when the module is no longer in use, but it avoids a lot
     of hash table reallocation. *)
  let ds = DS.create 32

  let unit =
    { equalities = Canonical VMap.empty;
      predicates = P.unit }

  let compute_rep p ds =
    let minimum v x =
      if p v then begin match x with
        | None -> Some v
        | Some v0 as old ->
          if Stdlib.compare v v0 < 0 then Some v else old
      end else x
    in
    let r = DS.reverse_map ds None minimum in
    fun x -> (try r x with Not_found -> if p x then Some x else None)

  let fold_eqs f x a =
    match x.equalities with
    | Noncanonical nc -> List.fold_left (fun a (x,y) -> f x y a) a nc
    | Canonical c -> VMap.fold f c a
  let enum_eqs x =
    match x.equalities with
    | Noncanonical nc -> BatList.enum nc
    | Canonical c -> VMap.enum c

  let pp formatter x =
    let open Format in
    fprintf formatter "[|@[%a@ && %a@]|]"
      (SrkUtil.pp_print_enum
         ~pp_sep:(fun formatter () -> fprintf formatter "@ && ")
         (fun formatter (x, rep) ->
            fprintf formatter "%a = %a" V.pp x V.pp rep))
      (enum_eqs x)
      P.pp x.predicates

  let exists p x =
    let g x y () = ignore (DS.union (DS.find ds x) (DS.find ds y)) in
    fold_eqs g x ();
    let rep = compute_rep p ds in
    let add_eq x m =
      if p x then begin
        match rep x with
        | Some r -> if V.compare x r = 0 then m else VMap.add x r m
        | None   -> m
      end else m
    in
    let add_eqs x y m = add_eq x (add_eq y m) in
    let eqs = fold_eqs add_eqs x VMap.empty in
    let preds = P.subst rep x.predicates in
    DS.clear ds;
    { equalities = Canonical eqs;
      predicates = preds }
  let exists p x = Log.time "EqLogic.exists" (exists p) x

  let canonicalize x =
    match x.equalities with
    | Canonical c -> c
    | Noncanonical _ -> begin
        let ex = exists (fun _ -> true) x in
        x.predicates <- ex.predicates;
        x.equalities <- ex.equalities;
        match x.equalities with
        | Canonical c -> c
        | Noncanonical _ -> assert false (* impossible *)
      end

  let add_eq x y eqs =
    let cmp = V.compare x y in
    let add k v eqs = (k,v)::eqs in
    if cmp = 0 then eqs else
      let (x,y) = if cmp < 0 then (x,y) else (y,x) in
      match eqs with
      | Canonical c ->
        if VMap.mem x c
        then Noncanonical (VMap.fold add c [(x,y)])
        else Canonical (VMap.add x y c)
      | Noncanonical nc -> Noncanonical ((x,y)::nc)

  let add_eqs = fold_eqs add_eq

  let compare x y =
    let xc = canonicalize x in
    let yc = canonicalize y in
    match P.compare x.predicates y.predicates with
    | 0 -> VMap.compare V.compare xc yc
    | other -> other

  let equal x y = compare x y = 0

  let make eqs pred =
    { predicates = pred;
      equalities = Noncanonical eqs }

  let subst f x =
    let g x y xs = (f x, f y)::xs in
    { predicates = P.subst (fun v -> Some (f v)) x.predicates;
      equalities = Noncanonical (fold_eqs g x []) }

  let get_pred x =
    ignore (canonicalize x);
    x.predicates

  let get_eqs x = fold_eqs (fun x y eqs -> (x,y)::eqs) x []
  let get_eqs_canonical x =
    ignore (canonicalize x);
    get_eqs x

  let get_subst x =
    let equalities = canonicalize x in
    fun v -> try VMap.find v equalities with Not_found -> v

  let implies x y =
    let x_subst = get_subst x in
    let is_implied (a, b) = V.equal (x_subst a) (x_subst b) in
    List.for_all is_implied (get_eqs y)
    && P.implies x_subst x.predicates y.predicates

  let mul x y =
    if equal x unit then y
    else if equal y unit then x else begin
      let z_eq = match x.equalities, y.equalities with
        | (Canonical _, _) -> add_eqs y x.equalities
        | (_, Canonical _) -> add_eqs x y.equalities
        | (_, _) -> add_eqs x y.equalities
      in
      let z = { equalities = z_eq; predicates = P.unit } in
      let equalities = canonicalize z in
      let s v = Some (try VMap.find v equalities with Not_found -> v) in
      let subst = P.subst s in
      { z with predicates = P.mul (subst x.predicates) (subst y.predicates) }
    end

  let relprod p x y =
    if equal x unit then exists p y
    else if equal y unit then exists p x else begin
      let g x y () = ignore (DS.union (DS.find ds x) (DS.find ds y)) in
      fold_eqs g x ();
      fold_eqs g y ();
      let rep = compute_rep p ds in
      let add_eq x m =
        if p x then begin
          match rep x with
          | Some r -> if V.compare x r = 0 then m else VMap.add x r m
          | None   -> m
        end else m
      in
      let add_eqs x y m = add_eq x (add_eq y m) in
      let eqs = fold_eqs add_eqs x VMap.empty in
      let eqs = fold_eqs add_eqs y eqs in
      let preds =
        P.mul (P.subst rep x.predicates) (P.subst rep y.predicates)
      in
      DS.clear ds;
      { equalities = Canonical eqs;
        predicates = preds }
    end
end

module Hashed = struct
  module type Predicate = sig
    include Predicate
    val hash : t -> int
  end
  module type ConjFormula = sig
    include ConjFormula
    val hash : t -> int
  end
  module MakeEQ (V : Var) (P : Predicate with type var = V.t) = struct
    let p_hash = P.hash
    include MakeEQ(V)(P)
    let hash x =
      let eqs = get_eqs_canonical x in
      let hash_eq (x,y) = Hashtbl.hash (V.hash x, V.hash y) in
      let preds = get_pred x in
      Hashtbl.hash (Putil.Hashed.list hash_eq eqs, p_hash preds)
  end
  module MakeTrivEQ (V : Var) (P : Predicate with type var = V.t) = struct
    type t = P.t [@@deriving show,ord]
    type pred = P.t
    type eqs = unit
    type var = V.t

    let hash = P.hash
    let mul = P.mul
    let unit = P.unit
    let exists p = P.subst (fun x -> if p x then Some x else None)
    let subst f = P.subst (fun x -> Some (f x))
    let get_pred p = p
    let get_eqs _ = []
    let get_eqs_canonical _ = []
    let get_subst _ = fun x -> x
    let make _ p = p
    let relprod p x y = exists p (mul x y)
    let implies = P.implies (fun x -> x)
    let equal = P.equal
  end
end

(** Transition and state formulae *)
module MakeFormula (Minterm : Hashed.ConjFormula with type var = Var.t) : sig
  module Transition : sig
    include Sig.KA.Ordered.S
    val exists : (Var.t -> bool) -> t -> t
    val assign : ap -> aexpr -> Minterm.pred -> t
    val assume : bexpr -> Var.Set.t -> Minterm.pred -> t
    val fold_minterms : (Minterm.t -> 'a -> 'a) -> t -> 'a -> 'a
    val get_frame : t -> Var.Set.t
    val of_minterm : Var.Set.t -> Minterm.t -> t
  end

  (* Subtype of ConjFormula, except that [exists] quantifies variables rather
     than indexed variables *)
  module State : sig
    include Sig.Monoid.Ordered.S
    type var = Var.t

    val subst : (var -> var) -> t -> t
    val get_pred : t -> Minterm.pred
    val get_subst : t -> (var -> var)
    val hash : t -> int
    val exists : (Var.t -> bool) -> t -> t
    module Set : Putil.Set.S with type elt = t
  end

  val apply : State.t -> Transition.t -> State.Set.t
end = struct
  (** State formulae are conjunctive formulae where variables are indexed, but
      [0] is the only index that should appear. *)
  module State = struct
    (* This is just a wrapper around Minterm that includes an explicit
       frame. *)
    module S = struct
      type var = Var.t
      type t = Var.Set.t * Minterm.t [@@deriving ord]
      let pp formatter (_, x) = Minterm.pp formatter x

      let hash (x,y) = Hashtbl.hash (Var.Set.hash x, Minterm.hash y)
      let get_subst x = Minterm.get_subst (snd x)
      let get_pred x = Minterm.get_pred (snd x)

      let subst f (frame, minterm) =
        (Var.Set.map f frame, Minterm.subst f minterm)
      let exists p (frame, minterm) =
        (Var.Set.filter p frame,
         Minterm.exists (fun v -> p (Var.unsubscript v)) minterm)
      let unit = (Var.Set.empty, Minterm.unit)
      let equal x y = compare x y = 0
      let mul (xv, xk) (yv, yk) = (Var.Set.union xv yv, Minterm.mul xk yk)
    end
    include S
    module Set = Putil.Hashed.Set.Make(S)
  end

  (** Conjunctive fragment for transition formulae (variables are indexed over
      \{0,1\}). Multiplication is relational composition. *)
  module ConjTransition = struct

    (** An abstract path consists of a transition formula (over indexed access
        paths, with indices in \{0,1\}). *)
    type t = Minterm.t [@@deriving show,ord]

    let unit = Minterm.unit


    let equal = Minterm.equal
    let sub_index i j m =
      Minterm.subst (fun x ->
          if Var.get_subscript x = i then Var.subscript x j else x) m
    let mul xm ym =
      let xm = sub_index 1 2 xm in
      let ym = sub_index 0 2 ym in
      Minterm.relprod (fun x -> Var.get_subscript x != 2) xm ym

    let exists p = Minterm.exists (fun v -> p (Var.unsubscript v))
    let implies = Minterm.implies
  end

  (** Transition formulae are formulae where variables are indexed over
      \{0,1\}, 0 indicating the "pre" state and 1 indicating the "post"
      state).  Addition is disjunction, multiplication is relational
      composition, and star is iterated relational composition. *)
  module Transition = struct
    module TR = Ka.ReducedDisjCompletion(ConjTransition)
    type t = Var.Set.t * TR.t [@@deriving ord]

    let pp formatter x = TR.pp formatter (snd x)

    let equal (xv, xk) (yv, yk) = Var.Set.equal xv yv && TR.equal xk yk
    let one = (Var.Set.empty, TR.one)
    let zero = (Var.Set.empty, TR.zero)
    let is_zero (_, k) = TR.equal TR.zero k

    let pred_unit = Minterm.get_pred Minterm.unit

    let set_footprint vars (v, k) =
      let frame =
        Var.Set.fold
          (fun x xs -> (Var.subscript x 0, Var.subscript x 1)::xs)
          (Var.Set.diff vars v)
          []
      in
      if frame = [] then k else
        let frame_eqs = Minterm.make frame pred_unit in
        TR.S.map (Minterm.mul frame_eqs) k
    let set_footprint vars x = Log.time "set_footprint" (set_footprint vars) x

    let add x y =
      if is_zero x then y
      else if is_zero y then x
      else begin
        let vars = Var.Set.union (fst x) (fst y) in
        (vars, TR.add (set_footprint vars x) (set_footprint vars y))
      end

    let mul_impl x y =
      let x_vars = fst x in
      let y_vars = fst y in
      let common = Var.Set.inter x_vars y_vars in
      let sub_index i j =
        let s v =
          if Var.get_subscript v = i && Var.Set.mem (Var.unsubscript v) common
          then Var.subscript v j else v
        in
        Minterm.subst s
      in
      let xtr =
        TR.S.fold (fun x s -> TR.S.add (sub_index 1 2 x) s) (snd x) TR.S.empty
      in
      let ytr =
        TR.S.fold (fun x s -> TR.S.add (sub_index 0 2 x) s) (snd y) TR.S.empty
      in
      let mul_minterm xm ym =
        Minterm.relprod (fun v -> Var.get_subscript v != 2) xm ym
      in
      let g a b = TR.S.add (mul_minterm a b) in
      let f a = TR.S.fold (g a) ytr in
      let res =
        Log.time "mul [disjunctive completion] " (TR.S.fold f xtr) TR.S.empty
      in
      (Var.Set.union x_vars y_vars, TR.reduce res)

    let mul x y =
      if is_zero x || is_zero y then zero
      else if equal x one then y
      else if equal y one then x
      else mul_impl x y

    (* Can't use TR.star, because TR.one is not actually the multiplicative
       unit. *)
    let star x =
      let rec fix s =
        let next = mul s s in
        if equal s next then s else fix next
      in
      fix (add one x)

    let make vars eqs pred =
      (vars, TR.S.singleton (Minterm.make eqs pred))

    (** Add the appropriate equalities for the transition relation for an
        assignment statement [lhs := rhs] to pred. *)
    let assign lhs rhs pred =
      match lhs, Aexpr.strip_casts rhs with
      | (Variable x, AccessPath (Variable y)) ->
        let eqs = [(Var.subscript x 1, Var.subscript y 0);
                   (Var.subscript y 0, Var.subscript y 1)]
        in
        make (Var.Set.add x (Var.Set.singleton y)) eqs pred
      | (Variable x, _) ->
        make (Var.Set.singleton x) [] pred
      | (ap, _) ->
        let open PointerAnalysis in
        let roots = AP.free_vars ap in

        (* If p may be &a, then we need to add a to the frame without the
           equality a0 = a1 if *p gets written to. *)
        let add_memloc memloc varset = match memloc with
          | (MAddr v, offset) -> Var.Set.add (v, offset) varset
          | (_, _) -> varset
        in
        let memlocs = resolve_ap ap in

        let killed =
          MemLoc.Set.fold add_memloc memlocs (Var.Set.empty)
        in
        let add_root root (frame, eqs) =
          if Var.Set.mem root killed then (frame, eqs)
          else (Var.Set.add root frame,
                ((Var.subscript root 0, Var.subscript root 1)::eqs))
        in
        let (frame, eqs) = Var.Set.fold add_root roots (killed, []) in
        make frame eqs pred

    let exists p (xv, xk) =
      (Var.Set.filter p xv,
       Log.time "exists" (TR.S.map (ConjTransition.exists p)) xk)

    let assume _bexpr frame pred =
      let frame_eqs =
        Var.Set.fold
          (fun x xs -> (Var.subscript x 0, Var.subscript x 1)::xs)
          frame
          []
      in
      make frame frame_eqs pred

    let fold_minterms f tr = TR.S.fold f (snd tr)
    let of_minterm frame minterm = (frame, TR.S.singleton minterm)
    let get_frame = fst
  end

  (** Apply a transition formula to a state formula (i.e., compute the post
      state [post(state, transition))].  State formulae are conjunctive (and
      transitions are not), so [apply] returns a set of minterms rather than a
      single state formulae.  *)
  let apply state transition =
    let vars = Var.Set.union (fst state) (fst transition) in
    let transition = Transition.set_footprint vars transition in
    let state_mt = ConjTransition.sub_index 0 1 (snd state) in
    let app x =
      (vars, ConjTransition.sub_index 1 0 (ConjTransition.mul state_mt x))
    in
    let add x = State.Set.add (app x) in
    Transition.TR.S.fold add transition State.Set.empty
end
