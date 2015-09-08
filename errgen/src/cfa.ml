open Ast
open Apak
open Syntax
open BatPervasives

include Log.Make(struct let name = "cfa" end)

module Cfa = struct
  module G = ExtGraph.Persistent.Digraph.MakeBidirectionalLabeled(Putil.PInt)(K)
  include G
  include ExtGraph.Display.MakeLabeled(G)(Putil.PInt)(K)
  let collect_vars cfa =
    edges_e cfa /@ (K.modifies % E.label)
    |> BatEnum.reduce K.VarSet.union
    |> K.VarSet.elements
end

module Slice = ExtGraph.Slice.Make(Cfa)
module VSet = Putil.PInt.Set
module L = Loop.SccGraph(Cfa)
module Top = Graph.Topological.Make(Cfa)

let add_edge g v u k =
  if Cfa.mem_edge g v u then begin
    let e = Cfa.find_edge g v u in
    let g = Cfa.remove_edge_e g e in
    Cfa.add_edge_e g (Cfa.E.create v (K.add (Cfa.E.label e) k) u)
  end else Cfa.add_edge_e g (Cfa.E.create v k u)

let add_edge_e g e =
  add_edge g (Cfa.E.src e) (Cfa.E.dst e) (Cfa.E.label e)

let elim v g =
  assert (Cfa.mem_vertex g v);
  assert (not (Cfa.mem_edge g v v));
  let f se h =
    let v_to_se = Cfa.E.label se in
    let add pe h =
      let weight = K.mul (Cfa.E.label pe) v_to_se in
      add_edge h (Cfa.E.src pe) (Cfa.E.dst se) weight
    in
    Cfa.fold_pred_e add g v h
  in
  Cfa.fold_succ_e f g v (Cfa.remove_vertex g v)

let reduce_cfa cfa entry exit =
  let scc = L.construct cfa in
  let is_header = L.is_header scc in
  let is_cp v = is_header v || v = entry || v = exit in
  let cp = BatList.of_enum (BatEnum.filter is_cp (Cfa.vertices cfa)) in
  logf "Entry: %d" entry;
  logf "Exit: %d" exit;
  logf "Cutpoints: %a" Show.format<int list> cp;
  let dag =
    let f g v =
      Cfa.fold_succ_e (fun e g -> Cfa.remove_edge_e g e) cfa v g
    in
    List.fold_left f cfa cp
  in
  let add_succs cpg u =
    assert (Cfa.mem_vertex dag u);
    let graph =
      Cfa.fold_succ_e (fun e g -> add_edge_e g e) cfa u dag
    in
    assert (Cfa.mem_vertex graph u);
    let graph =
      Top.fold (fun v g ->
        if is_cp v then g else elim v g
      ) graph graph
    in
    assert (Cfa.mem_vertex graph u);
    Cfa.fold_succ_e (fun e cpg -> add_edge_e cpg e) graph u cpg
  in
  List.fold_left add_succs Cfa.empty cp

(* collapse_assume interferes with analyze_sep *)
let rec collapse_assume g =
  try
    let e =
      BatEnum.find (fun e -> K.M.is_empty (Cfa.E.label e).K.transform)
                   (Cfa.edges_e g)
    in
    let tr = Cfa.E.label e in
    let add se h =
      let weight = K.mul tr (Cfa.E.label se) in
      add_edge h (Cfa.E.src e) (Cfa.E.dst se) weight
    in
    let g = Cfa.remove_edge_e g e in
    let g =
      if (Cfa.E.src e) = (Cfa.E.dst e) then g
      else Cfa.fold_succ_e add g (Cfa.E.dst e) g
    in
    logf "Collapse assume: %d -> %d" (Cfa.E.src e) (Cfa.E.dst e);
    collapse_assume g;
  with Not_found -> g


let build_cfa s weight =
  let fresh =
    let m = ref (-1) in
    fun () -> (incr m; !m)
  in
  let add_edge cfa u lbl v =
    add_edge_e cfa (Cfa.E.create u (weight lbl) v)
  in
  let rec go cfa entry = function
    | Cmd Skip -> (cfa, entry)
    | Cmd c ->
      let succ = fresh () in
      (add_edge cfa entry c succ, succ)
    | Seq (c, d) ->
      let (cfa, exit) = go cfa entry c in
      go cfa exit d
    | Ite (phi, c, d) ->
      let succ, enter_then, enter_else = fresh (), fresh (), fresh () in
      let cfa = add_edge cfa entry (Assume phi) enter_then in
      let cfa = add_edge cfa entry (Assume (Not_exp phi)) enter_else in
      let (cfa, exit_then) = go cfa enter_then c in
      let (cfa, exit_else) = go cfa enter_else d in
      (Cfa.add_edge (Cfa.add_edge cfa exit_then succ) exit_else succ, succ)
    | While (phi, body, _) ->
      let (cfa, enter_body) = go cfa entry (Cmd (Assume phi)) in
      let (cfa, exit_body) = go cfa enter_body body in
      let cfa = Cfa.add_edge cfa exit_body entry in
      go cfa entry (Cmd (Assume (Not_exp phi)))
  in
  let entry = fresh () in
  let (cfa, exit) = go (Cfa.add_vertex Cfa.empty entry) entry s in
  (cfa, entry, exit)

let add_stuttering cfa =
  (* For each edge u --k--> v such that u has a self loop u --k'--> u, add
     relabel the u->v edge u --(k + k'k)--> v. *)
  let f e g =
    let u = Cfa.E.src e in
    let v = Cfa.E.dst e in
    let k = Cfa.E.label e in
    let double k = K.add k (K.mul k k) in
    if u = v then
      add_edge g u v (K.mul k k)
    else
      let u_loop =
        if Cfa.mem_edge cfa u u then
          double (Cfa.E.label (Cfa.find_edge cfa u u))
        else
          K.zero
      in
      let v_loop =
        if Cfa.mem_edge cfa v v then
          double (Cfa.E.label (Cfa.find_edge cfa v v))
        else
          K.zero
      in
      add_edge g u v (K.add (K.mul u_loop k)
                        (K.add (K.mul k v_loop)
                                (K.mul (K.mul u_loop k) v_loop)))
  in
  let stutter g v = add_edge g v v K.one in
(*  Cfa.fold_edges_e f cfa cfa*)
  BatEnum.fold stutter
               (Cfa.fold_edges_e f cfa cfa)
               (L.enum_headers (L.construct cfa))

let map_edges f cfa =
  Cfa.fold_edges_e (fun e g -> Cfa.add_edge_e g (f e)) cfa Cfa.empty

let normalize cfa =
  let f e g =
    add_edge g (Cfa.E.src e) (Cfa.E.dst e) (K.normalize (Cfa.E.label e))
  in
  Cfa.fold_edges_e f cfa Cfa.empty

(******************************************************************************)
(* Tensor *)

module TCfa = struct
  module VP = struct
    module I = struct
      type t = int * int deriving (Compare, Show)
      let compare = Compare_t.compare
      let show = Show_t.show
      let format = Show_t.format
      let equal x y = compare x y = 0
      let hash = Hashtbl.hash
    end
    include I
    module Set = Putil.Hashed.Set.Make(I)
    module Map = Putil.Map.Make(I)
    module HT = BatHashtbl.Make(I)
  end
  module G = ExtGraph.Persistent.Digraph.MakeBidirectionalLabeled(VP)(K)
  module D = ExtGraph.Display.MakeSimple(G)(VP)
  include G
  include D
end
module TW = Loop.Wto(TCfa)
module TL = Loop.SccGraph(TCfa)
