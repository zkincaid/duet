(** Abstract flow graphs. Vertices in a CDG represent assignments,
    conditions, and function calls.  An edge from a vertex {i d} to {i
    u} labelled with partial state {i s} indicates that the definition
    of {i s} at {i d} can be the value read {i u}. *)

open Graph
open Apak
open Core

module Log = Srk.Log

module type FlowGraph = sig
  include Graph.Sig.I
  val is_initial : V.t -> t -> bool
  val is_terminal : V.t -> t -> bool
  val enum_initial : t -> V.t BatEnum.t
  val enum_terminal : t -> V.t BatEnum.t
  val clone : (V.t -> V.t) -> t -> t
end

module MakeFG (G : Graph.Sig.I) =
struct
  include G
  module VHT = Hashtbl.Make(V)

  let is_initial v afg = in_degree afg v = 0
  let enum_initial afg =
    let add_init v init =
      if is_initial v afg then v::init else init
    in
    BatList.enum (fold_vertex add_init afg [])

  let is_terminal v afg = out_degree afg v = 0
  let enum_terminal afg =
    let add_init v init =
      if is_terminal v afg then v::init else init
    in
    BatList.enum (fold_vertex add_init afg [])

  let clone vertex_clone g =
    let ht = VHT.create 32 in
    let h = create () in
    let process_vertex v =
      let clone = vertex_clone v in
      add_vertex h clone;
      VHT.add ht v clone
    in
    let process_edge e =
      let src = VHT.find ht (E.src e) in
      let dst = VHT.find ht (E.dst e) in
      add_edge_e h (E.create src (E.label e) dst)
    in
    iter_vertex process_vertex g;
    iter_edges_e process_edge g;
    h
end

module Pack : sig
  type pair
  module SetMap : (BatMap.S with type key = AP.Set.t)
  module PowerSet : Putil.Set.S with type elt = AP.Set.t
  module PairSet : Putil.Set.S with type elt = pair
  val fst : pair -> AP.t
  val snd : pair -> AP.t
  val project_fst : PairSet.t -> AP.Set.t
  val project_snd : PairSet.t -> AP.Set.t
  val mk_pair : AP.t -> AP.t -> pair
end = struct
  include AP
  type pair = t * t [@@deriving show,ord]
  module SetMap = BatMap.Make(Set)
  module PowerSet = Putil.Set.Make(Set)
  module PairSet = Putil.Set.Make(
    struct
      type t = pair [@@deriving show,ord]
    end)
  let fst (x,_) = x
  let snd (_,y) = y
  let project prj set = PairSet.fold (fun x -> Set.add (prj x)) set Set.empty
  let project_fst = project fst
  let project_snd = project snd
  let mk_pair x y = (x,y)
end

module G : sig
  include FlowGraph with type V.t = def
                     and type E.label = Pack.PairSet.t
  val group_pred : V.t -> t -> (V.t -> 'a) -> 'a ->
    (AP.Set.t -> 'a -> 'a -> 'a) ->
    'a Pack.SetMap.t
  val edge_label : E.t -> Pack.PairSet.t
  val inputs : t -> V.t -> Pack.PowerSet.t
  val outputs : t -> V.t -> Pack.PowerSet.t
  val domain : t -> V.t -> AP.Set.t
  val codomain : t -> V.t -> AP.Set.t
  val sanity_check : t -> unit
  val minimize : t -> t
  val display_labelled : t -> unit (** Display with edge labels *)
end = struct

  (* ocamlgraph requires a default edge value, so edges are labeled
     with edge_label option rather than edge_value.  No edge should
     ever be labelled with None *)
  module EdgeLabel = struct
    type t = Pack.PairSet.t
    let default = Pack.PairSet.empty
    let compare = Pack.PairSet.compare
  end

  module G0 = Imperative.Digraph.ConcreteBidirectionalLabeled(Def)(EdgeLabel)
  module SubG0 = ExtGraph.Subgraph(G0)
  module SliceG0 = ExtGraph.Slice.Make(G0)
  module DisplaySubG0 = ExtGraph.Display.MakeSimple(SubG0)(Def)
  open G0
  let edge_label e = E.label e

  let project_fst = Pack.project_fst
  let project_snd = Pack.project_snd

  let inputs afg v =
    let add_input edge = Pack.PowerSet.add (project_snd (edge_label edge)) in
    fold_pred_e add_input afg v Pack.PowerSet.empty

  let outputs afg v =
    let add_output edge = Pack.PowerSet.add (project_fst (edge_label edge)) in
    fold_succ_e add_output afg v Pack.PowerSet.empty

  let domain afg v =
    let add_input edge = AP.Set.union (project_snd (edge_label edge)) in
    fold_pred_e add_input afg v AP.Set.empty

  let codomain afg v =
    let add_output edge = AP.Set.union (project_fst (edge_label edge)) in
    fold_succ_e add_output afg v AP.Set.empty

  module G = MakeFG(G0)
  include G

  (** Group the predecessors of vertex by the label of the corresponding
      edge.  Within each group of predecessors, apply f, and then add
      resulting values in the monoid given by (zero, combine).  Return a
      map from edge labels to the corresponding monoid value. *)
  let group_pred vertex cdg f zero combine =
    let add_pred edge map =
      let old = (try Pack.SetMap.find (project_snd (edge_label edge)) map
                 with Not_found -> zero)
      in
      let set = project_snd (edge_label edge) in
      Pack.SetMap.add set (combine set old (f (E.src edge))) map
    in
    fold_pred_e add_pred cdg vertex Pack.SetMap.empty

  let minimize g =
    let module AbsEdge = struct
      type t = Def.t * Pack.PairSet.t [@@deriving show,ord]
    end in
    let module Key = Putil.Set.Make(AbsEdge) in
    let module M = Map.Make(Key) in
    let alpha = Def.HT.create 32 in
    let gamma = Def.HT.create 32 in

    let get_alpha x = Def.HT.find alpha x in
    let set_alpha x y =
      let a = get_alpha x in
      Def.HT.replace alpha x y;
      Def.HT.replace gamma y (Def.Set.add x (Def.HT.find gamma y));
      Def.HT.replace gamma a (Def.Set.remove x (Def.HT.find gamma a))
    in

    let changed = ref false in
    let vertex_edges v =
      let add_abs_edge k e = Key.add (get_alpha (E.src e), edge_label e) k in
      List.fold_left add_abs_edge Key.empty (pred_e g v)
    in
    let add_vertex v map =
      let alpha = get_alpha v in
      let preds = vertex_edges v in
      let (abs,map) =
        try (M.find preds map, map)
        with Not_found -> (v, M.add preds v map)
      in
      if Def.equal abs alpha then map
      else begin
        changed := true;
        Def.HT.add gamma abs Def.Set.empty;
        set_alpha v abs;
        map
      end
    in
    let split_partition p defs =
      ignore (Def.Set.fold add_vertex defs (M.add (vertex_edges p) p M.empty))
    in
    let rec fix () =
      Def.HT.iter split_partition gamma;
      if !changed then (changed := false; fix ())
    in
    let initial = ref [] in
    let set_initial def =
      let p = 
        try List.find (fun d -> def.dkind = d.dkind) (!initial)
        with Not_found -> begin
            initial := def::(!initial);
            Def.HT.add gamma def Def.Set.empty;
            def
          end
      in
      Def.HT.replace alpha def p;
      Def.HT.replace gamma p (Def.Set.add def (Def.HT.find gamma p))
    in
    let m = create () in
    let add_edge e =
      let edge =
        E.create (get_alpha (E.src e)) (E.label e) (get_alpha (E.dst e))
      in
      add_edge_e m edge
    in
    iter_vertex set_initial g;
    fix ();
    iter_edges_e add_edge g;
    m

  module EdgeDisplay = ExtGraph.Display.MakeLabeled(G)(Def)(Pack.PairSet)

  (** Display the AFG with edges labelled by the set of access paths
      carried along that path *)
  let display_labelled = EdgeDisplay.display

  (** Check that a graph satisfies the expected properties of AFGs. *)
  let sanity_check afg =
    let check_vertex v =
      match v.dkind with
      | Initial -> () (* Initial vertex is always well-formed *)
      | _ ->
        if not (AP.Set.subset (Def.get_uses v) (domain afg v)) then begin
          Log.fatalf
            "Missing inputs for `%a':@\nexpected %a@\ngot %a"
            Def.pp v
            AP.Set.pp (Def.get_uses v)
            AP.Set.pp (domain afg v);
        end;
        if not (AP.Set.subset
                  (codomain afg v)
                  ((AP.Set.union (domain afg v)) (Def.get_defs v)))
        then begin
          Log.fatalf
            "Extra outputs for `%a':@\nexpected %a@\ngot %a"
            Def.pp v
            AP.Set.pp (AP.Set.union (domain afg v) (Def.get_defs v))
            AP.Set.pp (codomain afg v);
        end
    in
    iter_vertex check_vertex afg;
    Log.debug "AFG sanity check complete."
end 
