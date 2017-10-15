open BatPervasives
open PaFormula
open Ark

include Log.Make(struct let name = "struct" end)


let embed = ref 0

module type Symbol = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module type S = sig
  type t
  type predicate
  module Predicate : Symbol with type t = predicate
  val pp : Format.formatter -> t -> unit
  val show : t -> string
  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int
  val props : t -> (predicate * int list) BatEnum.t
  val preds : t -> predicate BatEnum.t
  val universe_size : t -> int
  val universe : t -> int BatEnum.t
  val make : ?size:int -> (predicate * int list) BatEnum.t -> t
  val models : ?env:(int list) -> t -> (predicate,int) formula -> bool
  val min_models :
    ?env:(int list) ->
    int ->
    (predicate,int) formula ->
    t BatEnum.t
  val substructure : t -> t -> bool
  val embeds : t -> t -> bool
  val embeds_novel : t -> t -> bool
  val embeds_novel2 : t -> t -> bool
  val uembeds : t -> t -> bool
  val cembeds : t -> t -> bool
  val str2mzn : t -> t -> bool
  val union : t -> t -> t
  val empty : int -> t
  val full : (predicate * int) BatEnum.t -> int -> t
  val add : predicate -> int list -> t -> t
  val remove : predicate -> int list -> t -> t
  val minimize : ?env:(int list) -> t -> (predicate,int) formula -> t
  val instantiate :
    ?env:(int list) ->
    t ->
    (predicate,int) formula ->
    (predicate,int) formula option
end

module F = PaFormula

module Make (P : Symbol) = struct
  type predicate = P.t
  type atom = P.t * int list [@@deriving ord]
  module Predicate = P
                        
  let pp_atom formatter (p,args) =
    Format.fprintf formatter "@[%a(%a)@]"
      P.pp p
      (ArkUtil.pp_print_enum Format.pp_print_int) (BatList.enum args)

  module AtomSet = BatSet.Make(struct
      type t = atom [@@deriving ord]
    end)

  type t =
    { universe : int;
      prop : AtomSet.t }

  let pp formatter str =
    ArkUtil.pp_print_enum
      ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ /\\ ")
      pp_atom
      formatter
      (AtomSet.enum str.prop)

  let show = ArkUtil.mk_show pp

  let pp_formula formatter phi =
    F.pp P.pp Format.pp_print_int formatter phi

  let hash str =
    (str.universe,
     List.map
       (fun (p, args) -> (P.hash p, args))
       (AtomSet.elements str.prop))
    |> Hashtbl.hash

  let equal x y =
    x.universe = y.universe && AtomSet.equal x.prop y.prop

  let compare x y =
    match Pervasives.compare x.universe y.universe with
    | 0 -> AtomSet.compare x.prop y.prop
    | cmp -> cmp
  
  let substructure x y =
    x.universe <= y.universe && AtomSet.subset x.prop y.prop

  let props x = AtomSet.enum x.prop
  let universe_size x = x.universe
  let universe x = 1 -- x.universe

  (* Get the maximum constant used in a formula *)
  let max_constant phi =
    let term_const = function
      | Const k -> k
      | Var _ -> 0
    in
    let f = function
      | `Eq (x, y) -> max (term_const x) (term_const y)
      | `Neq (x, y) -> max (term_const x) (term_const y)
      | `Atom (p, args) -> List.fold_left max 0 (List.map term_const args)
      | `And (x, y) | `Or (x, y) -> max x y
      | `Forall (_, x) | `Exists (_, x) -> x
      | `T | `F -> 0
    in
    F.eval f phi

  let empty size =
    { universe = size;
      prop = AtomSet.empty }

  let full predicates size =
    let prop =
      predicates
      /@ (fun (p, k) ->
          ArkUtil.tuples (BatList.of_enum ((1 -- k) /@ (fun _ -> (1 -- size))))
          /@ (fun tuple -> (p, tuple))
          |> AtomSet.of_enum)
      |> BatEnum.fold AtomSet.union AtomSet.empty
    in
    { prop = prop;
      universe = size }

  let union x y =
    { universe = max x.universe y.universe;
      prop = AtomSet.union x.prop y.prop }

  let add_minimal x xs =
    let rec go rest = function
      | (y::ys) ->
        if substructure y x then xs
        else if substructure x y then go rest ys
        else go (y::rest) ys
      | [] -> x::rest
    in
    go [] xs
  let append_minimal xs ys =
    let (big, small) =
      if (List.length xs) >= (List.length ys) then (xs, ys)
      else (ys, xs)
    in
    List.fold_left (flip add_minimal) big small
  let minimal_of_enum enum =
    let rec go rest =
      match BatEnum.get enum with
      | Some elt -> go (add_minimal elt rest)
      | None -> rest
    in
    go []

  let rec models ?env:(env=[]) str phi =
    let term_val = function
      | Const s -> s
      | Var v ->
        try BatList.nth env v
        with Invalid_argument _ -> invalid_arg "models"
    in
    match F.destruct phi with
    | `Eq (s, t) -> (term_val s) = (term_val t)
    | `Neq (s, t) -> (term_val s) != (term_val t)
    | `Atom (p, args) ->
      AtomSet.mem (p, List.map term_val args) str.prop
    | `And (phi, psi) -> models ~env:env str phi && models ~env:env str psi
    | `Or (phi, psi) -> models ~env:env str phi || models ~env:env str psi
    | `Forall (_, phi) ->
      BatEnum.for_all (fun elt ->
          models ~env:(elt::env) str phi
        ) (universe str)
    | `Exists (_, phi) ->
      BatEnum.exists (fun elt ->
          models ~env:(elt::env) str phi
        ) (universe str)
    | `T -> true
    | `F -> false

  let min_models ?env:(env=[]) size phi =
    let rec go env phi =
      let term_val = function
        | Const s -> s
        | Var v ->
          try BatList.nth env v
          with Invalid_argument _ ->
            invalid_arg ("min_models: unbound " ^ (string_of_int v))
      in
      match F.destruct phi with
      | `Eq (s, t) ->
        if (term_val s) = (term_val t) then [empty size] else []
      | `Neq (s, t) ->
        if (term_val s) != (term_val t) then [empty size] else []
      | `Atom (p, args) ->
        [{ universe = size;
           prop = AtomSet.singleton (p, List.map term_val args) }]
      | `And (phi, psi) ->
        ArkUtil.cartesian_product
          (BatList.enum (go env phi))
          (BatList.enum (go env psi))
        /@ (uncurry union)
        |> BatList.of_enum
      | `Or (phi, psi) ->
        List.rev_append (go env phi) (go env psi)
      | `Forall (_, phi) ->
        let f strs n =
          ArkUtil.cartesian_product
            (BatList.enum (go (n::env) phi))
            strs
          /@ uncurry union
        in
        BatEnum.fold f (BatEnum.singleton (empty size)) (1 -- size)
        |> BatList.of_enum
      | `Exists (_, phi) ->
        let f strs n =
          List.rev_append (go (n::env) phi) strs
        in
        BatEnum.fold f [] (1 -- size)
      | `T -> [empty size]
      | `F -> []
    in
    BatList.enum (go env phi)

  (***************************************************************************)
  (* Structure embeddings                                                    *)
  (***************************************************************************)
  
  (* Given a constant k and a configuration c = 
           p_1(a_11, ..., a_1n)
        /\        ...
        /\ p_m(a_m1, ..., a_ml)

     We define the signature of k in c to be the set of all (p_i, j) such that
     a_ij = k.  If C, C' are configurations such that C' covers C, the
     embedding of C' into C must map each k' in C' to a constant k in C such
     that the signature of k' in C' is a subset of the signature of k in C. *)
  module Sig = BatSet.Make(struct
      type t = P.t * int [@@deriving ord]
    end)

  module KSet = ArkUtil.Int.Set
  module KMap = ArkUtil.Int.Map

  (* Compute the signature of a constant in some configuration *)
  let mk_sig i str =
    let f (head,args) sg =
      let g pos j sg =
        if i = j then Sig.add (head,pos) sg
        else sg
      in
      BatEnum.foldi g sg (BatList.enum args)
    in
    AtomSet.fold f str.prop Sig.empty

  let mk_sig_map str =
    let f map k = KMap.add k (mk_sig k str) map in
    BatEnum.fold f KMap.empty (universe str)

  (* Is there an embedding (injective homomorphism) of x into y? *)
  let embeds_naive x y =
    let x_sigs = mk_sig_map x in
    let y_sigs = mk_sig_map y in
    let check map =
      let f (head,args) =
        AtomSet.mem (head, List.map (fun x -> KMap.find x map) args) y.prop
      in
      AtomSet.for_all f x.prop
    in
    let rec go xs y_sigs map =
      match xs with
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
    go (BatList.of_enum (universe x)) y_sigs KMap.empty

  module PSet = BatSet.Make(P)

  (* Gets a list of all predicate symbols *)
  let get_preds str =
    let f (head, args) preds =
      PSet.add head preds
    in
    AtomSet.fold f str.prop PSet.empty

  let preds str = PSet.enum (get_preds str)

  (* Gets a list of all predicate variables *)
  let get_ids str =
    let f (head, args) ids =
      let g ids id =
        KSet.add id ids
      in
      List.fold_left g ids args
    in
    AtomSet.fold f str.prop KSet.empty

  module Graph = Matching.Make(ArkUtil.Int)

  (* Create a Bipartite Graph from structures X and Y
     Where X embeds Y -> |max_matching G| = |U|
     For monadic structures this is a bimplication
  *)
  let mk_graph x y =
    let mk_edges x_ids x_sigs y_ids y_sigs = (* Create an Enumeration of Edges *)
      let e = BatEnum.empty() in
      let f x_id =
        let g y_id =
          if Sig.subset (KMap.find x_id x_sigs) (KMap.find y_id y_sigs) then
            BatEnum.push e (x_id, y_id)
        in
        KSet.iter g y_ids
      in
      KSet.iter f x_ids; e
    in
    let u = get_ids x in
    let v = get_ids y in
    let x_sigs = mk_sig_map x in
    let y_sigs = mk_sig_map y in
    let e = mk_edges u x_sigs v y_sigs in
    Graph.make (KSet.enum u) (KSet.enum v) e

  module MatchCPP = MatchingCPP.Make(P)
  module Embeds = Embeds.Make(P)

  (* Is there an embedding (injective homomorphism) of x into y? 
     Only gauranteed to work with monadic structures *)
  let embeds_matching x y =
    ((x.universe >= 10) && MatchCPP.embeds (MatchCPP.make (x.universe) (props x) (y.universe) (props y))) ||
    begin
      let g = mk_graph x y in
         (Graph.incident_u g) >= (Graph.u_size g)       (* Quick check to see if |max_matching g| <= |U| *)
      && (Graph.incident_v g) >= (Graph.u_size g)
      && ((Graph.max_matching g) = (Graph.u_size g))
    end

  let embeds_novel x y =
    (x.universe <= y.universe)
    && (AtomSet.cardinal x.prop <= AtomSet.cardinal y.prop)
    && (PSet.subset (get_preds x) (get_preds y)) (* this is always true when using Search Tree *)
    && (AtomSet.subset x.prop y.prop ||
       (Embeds.embeds (Embeds.make x.universe (props x) y.universe (props y))))

  let embeds_novel2 x y =
    (x.universe <= y.universe)
    && (AtomSet.cardinal x.prop <= AtomSet.cardinal y.prop)
    && (PSet.subset (get_preds x) (get_preds y)) (* this is always true when using Search Tree *)
    && (AtomSet.subset x.prop y.prop ||
       (MatchCPP.embeds (MatchCPP.make (x.universe) (props x) (y.universe) (props y))))

  let uembeds x y =
    incr embed;
    (x.universe <= y.universe)
    && (AtomSet.cardinal x.prop <= AtomSet.cardinal y.prop)
    && (PSet.subset (get_preds x) (get_preds y)) (* this is always true when using Search Tree *)
    && (AtomSet.subset x.prop y.prop ||
       (MatchCPP.uembeds (MatchCPP.make (x.universe) (props x) (y.universe) (props y))))

  let cembeds x y =
    (x.universe <= y.universe)
    && (AtomSet.cardinal x.prop <= AtomSet.cardinal y.prop)
    && (PSet.subset (get_preds x) (get_preds y)) (* this is always true when using Search Tree *)
    && (AtomSet.subset x.prop y.prop ||
       (MatchCPP.cembeds (MatchCPP.make (x.universe) (props x) (y.universe) (props y))))

  let str2mzn x y =
    (x.universe <= y.universe)
    && (AtomSet.cardinal x.prop <= AtomSet.cardinal y.prop)
    && (PSet.subset (get_preds x) (get_preds y)) (* this is always true when using Search Tree *)
    && (AtomSet.subset x.prop y.prop ||
       (MatchCPP.emb2mzn (MatchCPP.make (x.universe) (props x) (y.universe) (props y))))    

  (* Is there an embedding (injective homomorphism) of x into y? *)
  let embeds x y =
    (x.universe <= y.universe)
    && (AtomSet.cardinal x.prop <= AtomSet.cardinal y.prop)
    && (PSet.subset (get_preds x) (get_preds y)) (* this is always true when using Search Tree *)
    && (AtomSet.subset x.prop y.prop || begin
    let monadic str =
      let f (head, args) =
        (List.length args) <= 1
      in
      AtomSet.for_all f str.prop
    in
    if (monadic x) && (monadic y) then embeds_matching x y else embeds_naive x y
  end)

  let embeds x y = Log.time "Embedding" (uembeds x) y

  let make ?size:(size=(-1)) prop_enum =
    let prop = AtomSet.of_enum prop_enum in
    let universe =
      AtomSet.fold (fun (_, args) m ->
          List.fold_left max m args
        ) prop size
    in
    { prop; universe }

  let add p tuple str =
    let universe = List.fold_left max str.universe tuple in
    { universe = universe;
      prop = AtomSet.add (p, tuple) str.prop }
  let remove p tuple str =
    { str with prop = AtomSet.remove (p, tuple) str.prop }

  let minimize ?env:(env=[]) str phi =
    AtomSet.fold (fun (p, tuple) m ->
        let rm = remove p tuple m in
        if models ~env:env rm phi then rm
        else m
      ) str.prop str

  let rec instantiate ?env:(env=[]) str phi =
    let term_val = function
      | Const s -> s
      | Var v ->
        try BatList.nth env v
        with Invalid_argument _ -> invalid_arg "models"
    in
    match F.destruct phi with
    | `Eq (s, t) ->
      if (term_val s) = (term_val t) then
        Some (mk_eq (Const (term_val s)) (Const (term_val t)))
      else
        None
    | `Neq (s, t) ->
      if (term_val s) = (term_val t) then
        None
      else
        Some (mk_neq (Const (term_val s)) (Const (term_val t)))
    | `Atom (p, args) ->
      if AtomSet.mem (p, List.map term_val args) str.prop then
        Some (mk_atom p (List.map (fun i -> Const (term_val i)) args))
      else
        None
    | `And (phi, psi) ->
      begin match instantiate ~env:env str phi with
        | None -> None
        | Some phi' -> match instantiate ~env:env str psi with
          | None -> None
          | Some psi' -> Some (mk_and phi' psi')
      end
    | `Or (phi, psi) ->
      begin match instantiate ~env:env str phi with
        | Some phi' -> Some phi'
        | None -> instantiate ~env:env str psi
      end
    | `Forall (_, _) ->
      if models ~env:env str phi then
        Some (F.var_substitute (fun i -> Const (List.nth env i)) phi)
      else
        None
    | `Exists (_, phi) ->
      let universe = universe str in
      let rec go () =
        match BatEnum.get universe with
        | Some elt -> begin match instantiate ~env:(elt::env) str phi with
            | Some phi ->
              Some phi
            | None -> go ()
          end
        | None -> None
      in
      go ()
    | `T -> Some (mk_true)
    | `F -> None
end
