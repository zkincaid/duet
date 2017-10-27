open Pervasives
open BatPervasives
open Srk

include Log.Make(struct let name = "Embeds" end)

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

  (* empty embedding problem *)
  val empty : t

  (* Pass in the two structures *)
  val make : int -> (predicate * int list) BatEnum.t -> int -> (predicate * int list) BatEnum.t -> t

  (* Solves Embedding Problem for relational structures *)
  val embeds : t -> bool
end

(*
(* An Efficient BiPartite Graph Representation when elements of
   u are labeled from 1..n and v 1..m *)
module IntGraph = struct
  module DA = BatDynArray

  type edge = (int*int) (* adjacent vertex label, reverse edge position *)
  type t = {u : edge DA.t DA.t;
            v : edge DA.t DA.t}

  let make u_size v_size : t =
    { u = DA.init u_size (fun _ -> DA.create());
      v = DA.init v_size (fun _ -> DA.create())}

  (* Adds edge (u, v) and (v, u) to graph in constant time *)
  let add_edge (g : t) u v : unit =
    let u_pos = DA.length (DA.get g.u u) in
    let v_pos = DA.length (DA.get g.v v) in
    DA.add (DA.get g.u u) (v, v_pos);
    DA.add (DA.get g.v v) (u, u_pos)

  (* Constant time removal of (u, v) and (v, u) from graph *)
  let remove_edge_aux (g : t) u v upos vpos : unit =
    let (vl, _) = DA.last (DA.get g.u u) in
    let (ul, _) = DA.last (DA.get g.v v) in
    DA.set (DA.get g.u u) upos (vl, vpos);
    DA.set (DA.get g.v v) vpos (ul, upos);
    DA.delete_last (DA.get g.u u);
    DA.delete_last (DA.get g.v v)

  (* Constant time removal of edge and it's reverse edge *)
  let remove_edge_u (g : t) u upos : unit =
    let (v, vpos) = DA.get (DA.get g.u u) upos in
    remove_edge_aux g u v upos vpos

  (* Constant time removal of edge and it's reverse edge *)
  let remove_edge_v (g : t) v vpos : unit =
    let (u, upos) = DA.get (DA.get g.v v) vpos in
    remove_edge_aux g u v upos vpos

  (* O(|V|) should be avoided if possible *)
  let remove_edge (g : t) u v : unit =
    let rec go u_pos : unit =
      if u_pos <> DA.length (DA.get g.u u) then
        begin
          let (vi, vi_pos) = DA.get (DA.get g.u u) u_pos in
          if vi == v then
            remove_edge_aux g u v u_pos vi_pos
          else
            go (u_pos + 1)
        end
    in
    go 0

  (* Unit Propagation for Bipartite Matching *)
  let unit_prop (g : t) : unit =
    let q = Queue.create() in (* Edges to be removed (u, upos) *)
    let f u (v, vpos) : unit =
      DA.iter (fun (ui, ui_pos) -> if u <> ui then begin Queue.add (ui, ui_pos) q end) (DA.get g.v v)
    in
    DA.iteri (fun u adj -> if (DA.length adj) == 1 then begin f u (DA.last adj) end) g.u;
    while not (Queue.is_empty q) do
      let (u, upos) = Queue.take q in
      remove_edge_u g u upos;
      if (DA.length (DA.get g.u u)) == 1 then
        begin
          f u (DA.last (DA.get g.u u))
        end
    done

  (* Ford Fulkerson Algorithm for Max Flow *)
  let max_matching (g : t) : int =
    let matching_u = DA.init (DA.length g.u) (fun _ -> -1) in
    let matching_v = DA.init (DA.length g.v) (fun _ -> -1) in
    let visited = DA.init (DA.length g.u) (fun _ -> 0) in
    let count : int ref = ref 0 in
    let rec f i : unit =
      let rec dfs u iter : bool =
        if (u == DA.length g.u) || (DA.get visited u) == iter then false else
          begin
            DA.set visited u iter;
            let adj = (DA.get g.u u) in
            let rec go k : bool =
              if (k <> (DA.length adj)) then
                begin
                  let (v, vpos) = (DA.get adj k) in
                  if ((DA.get matching_v v) < 0) || (dfs (DA.get matching_v v) iter) then
                    begin
                      DA.set matching_u u v;
                      DA.set matching_v v u;
                      true
                    end
                  else
                    go (k + 1)
                end
              else
                false
            in go 0
          end
      in
      if (i <> DA.length g.u) then
        begin
          if i == 0 || (dfs i i) then begin incr count end; f (i + 1)
        end
    in (f 0); (!count)
end *)

module Make (Predicate : Symbol) = struct
  type predicate = Predicate.t
  type str = (int * (predicate * int list) BatSet.t)
  type t = { str1 : str;
             str2 : str}

  let empty = { str1 = (0, BatSet.empty);
                str2 = (0, BatSet.empty) }

  (* Just store info -- don't do any processing eagerly *)
  let make univ1 props1 univ2 probs2 =
    { str1 = (univ1, (BatSet.of_enum props1));
      str2 = (univ2, (BatSet.of_enum probs2))}

  module DA = BatDynArray
  module Vset = SrkUtil.Int.Set
  module BitSet = BatBitSet
  module PMap = BatMap.Make(Predicate)
  type u_graph = { u : Vset.t DA.t;
                   v : Vset.t DA.t}
  type p_graph = { u : int DA.t DA.t;
                   u_label : (int list) DA.t;
                   v_label : (int list) DA.t}

  (* Make Signature of Each Variable in str *)
  let make_sigs ((univ, props) : str) (map : int * (int PMap.t)): (int * (int PMap.t)) * (BitSet.t DA.t) =
    let sigs = DA.init (univ + 1) (fun _ -> BitSet.empty()) in
    let f (pred, vars) (next, pred_map) : (int * int PMap.t) =
      let g i var : int =
        BitSet.set (DA.get sigs var) i;
        (i + 1)
      in
      match vars with
      | [] -> (next, pred_map)
      | _ ->
         begin
           if PMap.mem pred pred_map then
             begin
               ignore (List.fold_left g (PMap.find pred pred_map) vars);
               (next, pred_map)
             end
           else
             ((List.fold_left g next vars), (PMap.add pred next pred_map))
         end
    in
    let map = (BatSet.fold f props map) in
    (map, sigs)


  let unit_prop (g : u_graph ) : (int * int) list  =
    let q = Queue.create() in (* Edges to perform unit prop on *)
    let edges : ((int * int) list) ref = ref [] in (* edges (u, v) removed from graph *)
    let remove u v = (* keep edges (u, v) and remove all u' <> u, (u', v) *)
      Vset.iter (fun k ->
          if k <> u then
            begin
              DA.set g.u k (Vset.remove v (DA.get g.u k));
              if (Vset.cardinal (DA.get g.u k)) = 1 then
                begin
                  Queue.add (k, (Vset.choose (DA.get g.u k))) q
                end;
              edges := (k, v) :: (!edges)
            end) (DA.get g.v v);
      DA.set g.v v (Vset.singleton u)
    in
    DA.iteri (fun u adj -> if (Vset.cardinal adj) = 1 then begin Queue.add (u, Vset.choose adj) q end) g.u;
    while not (Queue.is_empty q) do
      let (u, v) = Queue.take q in
      if Vset.mem v (DA.get g.u u) then (* (u, v) may have been removed from the graph already *)
        begin                           (* If so then, don't unit propagate *)
          remove u v
        end
    done;
    (!edges)

  let print_u_graph (g : u_graph) : unit =
    DA.iteri (fun i adj -> logf ~level:`always "%d {%a}" i (SrkUtil.pp_print_enum Format.pp_print_int) (Vset.enum adj)) g.u

  let print_p_graph (g : p_graph) : unit =
    DA.iteri (fun i adj -> logf ~level:`always "%d {%a}" i (SrkUtil.pp_print_enum Format.pp_print_int) (DA.enum adj)) g.u

  (* Make Universe Graph (Potential mappings of variables in str1 to variables in str2) *)
  let make_ugraph (emb : t) : u_graph =
    let (pmap, x_sigs) = make_sigs emb.str1 (0, PMap.empty) in
    let (_, y_sigs) = make_sigs emb.str2 pmap in
    let u = DA.init (DA.length x_sigs) (fun _ -> Vset.empty) in
    let v = DA.init (DA.length y_sigs) (fun _ -> Vset.empty) in
    let update i j xsig ysig : unit =
      if i <> 0 && j <> 0 && (xsig = (BitSet.inter xsig ysig)) then
        begin
          DA.set u i (Vset.add j (DA.get u i));
          DA.set v j (Vset.add i (DA.get v j))
        end
    in
    DA.iteri (fun i xsig -> DA.iteri (fun j ysig -> update i j xsig ysig) y_sigs) x_sigs;
    let u_graph = { u = u; v = v} in
    ignore (unit_prop u_graph); (* Simplify Graph *)
    u_graph

  let make_graph (emb : t) : (u_graph*p_graph) =
    let uG = make_ugraph emb in
    let high_arity (pred, vars) : bool =
      match vars with
      | [] -> false
      | _ :: [] -> false
      | _ -> true
    in
    let str1 = BatSet.filter high_arity (match emb.str1 with (_, s) -> s) in
    let str2 = BatSet.filter high_arity (match emb.str2 with (_, s) -> s) in
    let pu = DA.init (BatSet.cardinal str1) (fun _ -> DA.create()) in
    let pul = DA.init (DA.length pu) (fun _ -> []) in
    let pvl = DA.init (BatSet.cardinal str2) (fun _ -> []) in
    let f (xpred, xvars) i =
      DA.set pul i xvars;
      let adj = DA.get pu i in
      let rec p ul vl : bool =
        match ul with
        | [] -> true
        | u :: ul' ->
           match vl with
           | [] -> false
           | v :: vl' -> (Vset.exists (fun v' -> v = v') (DA.get uG.u u)) && (p ul' vl')
      in
      let g (ypred, yvars) j =
        if i = 0 then begin DA.set pvl j yvars end;
        if xpred = ypred && (p xvars yvars) then
          begin
            DA.add adj j
          end;
        j + 1
      in
      DA.set pu i adj;
      ignore (BatSet.fold g str2 0); (* emulate iteri using fold *)
      i + 1
    in
    ignore (BatSet.fold f str1 0); (* emulate iteri using fold *)
    (uG, { u = pu;
           u_label = pul;
           v_label = pvl})
    
  (* Ford Fulkerson Algorithm for Max Flow *)
  let max_matching (g : u_graph): ((int DA.t)*int) =
    let matching_u = DA.init (DA.length g.u) (fun _ -> -1) in
    let matching_v = DA.init (DA.length g.v) (fun _ -> -1) in
    let visited = DA.init (DA.length g.u) (fun _ -> 0) in
    let count : int ref = ref 0 in
    let rec f i : unit =
      let rec dfs u iter : bool =
        if (u = DA.length g.u) || (DA.get visited u) = iter then false else
          begin
            DA.set visited u iter;
            Vset.exists
              (fun v ->
                if ((DA.get matching_v v) < 0) || (dfs (DA.get matching_v v) iter) then
                  begin
                    DA.set matching_u u v;
                    DA.set matching_v v u;
                    true
                  end
                else false) (DA.get g.u u)
          end
      in
      if (i <> DA.length g.u) then
        begin
          if i = 0 || (dfs i i) then begin incr count end; f (i + 1)
        end
    in (f 0); (matching_u, (!count))

  (* returns a list of indices to g that are in conflict with the matching *)
  (* If the list is [] then the matching forms a matching on the p_graph *)
  let conflicts (g : p_graph) (matching : int DA.t) : int list =
    let conflicts : (int list) ref = ref [] in
    let f i adj : unit =
      let exists (p : 'a -> bool) (arr : 'a DA.t) : bool =
        let rec go i : bool =
          if i = DA.length arr then false
          else (p (DA.get arr i)) || go (i + 1)
        in go 0
      in
      let p j = (List.map (DA.get matching) (DA.get g.u_label i)) = (DA.get g.v_label j) in
      if not (exists p adj) then
        begin
          conflicts := i :: (!conflicts)
        end
    in
    DA.iteri f g.u;
    (!conflicts)

  (* We should probably do arc consistency on pG as well *)
  let rec backtrack (decisions : ((int * int)*((int*int) list)) list) (pG : p_graph) (uG : u_graph) : ((int * int)*((int*int) list)) list =
    let add_edges edges : unit = (* adds edges back to uG now that we're backtracking *)
      match edges with
      | [] -> ()
      | (u, v) :: e ->
         DA.set uG.u u (Vset.add v (DA.get uG.u u));
         DA.set uG.v v (Vset.add u (DA.get uG.v v))
    in
    let remove_edges u v : (int * int) list = (* removes edges in uG inconsistent with decision *)
      let remove e u v : (int * int) list =
        let l =
          Vset.fold (fun k e ->
            if k <> u then
              begin
                DA.set uG.u k (Vset.remove v (DA.get uG.u k));
                (k, v) :: e
              end
            else e) (DA.get uG.v v) e
        in
        DA.set uG.v v (Vset.singleton u);
        l
      in
      let l = List.fold_left2 remove [] (DA.get pG.u_label u) (DA.get pG.v_label v) in
      List.append (unit_prop uG) l
    in
    let conflict (u : int) (v : int) : bool = (* true <-> (u, v) is consistent with the decisions made thus far *)
      let check u v =
        Vset.mem v (DA.get uG.u u)
      in
      not (List.for_all2 check (DA.get pG.u_label u) (DA.get pG.v_label v))
    in
    match decisions with
    | [] -> []
    | ((u, i), e) :: d -> (* e is the list of edges removed when decision (u, i) was made *)
       let rec go j =
         if j = (DA.length (DA.get pG.u u)) then
           backtrack d pG uG
         else
           if conflict u (DA.get (DA.get pG.u u) j) then (* (u, j) conflicts with d *)
             go (j + 1)
           else
             ((u, j), (remove_edges u (DA.get (DA.get pG.u u) j))) :: d
       in
       add_edges e;
       go (i + 1)

  let choose decisions (conflicts : int list) (pG : p_graph) (uG : u_graph) : ((int * int)*((int*int) list)) list =
    let check (conf : (int * int) list) (u : int) : (int * int) list =
      let rec go j =
        if j = DA.length (DA.get pG.u u) then
          conf
        else
          begin
            if (List.for_all2 (fun u v -> Vset.mem v (DA.get uG.u u)) (DA.get pG.u_label u) (DA.get pG.v_label (DA.get (DA.get pG.u u) j))) then
              (u, j) :: conf
            else
              go (j + 1)
          end
      in
      go 0      
    in
    let remove_edges u v : (int * int) list = (* removes edges in uG inconsistent with decision *)
      let remove e u v : (int * int) list =
        let l =
          Vset.fold (fun k e ->
            if k <> u then
              begin
                DA.set uG.u k (Vset.remove v (DA.get uG.u k));
                (k, v) :: e
              end
            else e) (DA.get uG.v v) e
        in
        DA.set uG.v v (Vset.singleton u);
        l
      in
      let l = List.fold_left2 remove [] (DA.get pG.u_label u) (DA.get pG.v_label v) in
      List.append (unit_prop uG) l
    in
    let conf = List.fold_left check [] conflicts in (* All (u, j) in conf are consistent with all previous decisions *)
    match conf with
    | [] -> decisions
    | (u, j) :: _ -> ((u, j), remove_edges u (DA.get (DA.get pG.u u) j))::decisions

  (* Decision Procedure for Embedding Algorithm *)
  let embeds embedding =
    let (uG, pG) = make_graph embedding in
    let rec go decisions: bool =
      let clean_up (_ : unit): bool =
        let d = backtrack decisions pG uG in
        if d = [] then false else go d
      in
      let (matching, count) = max_matching uG in
      if count <> (DA.length uG.u) then
        clean_up ()
      else
        begin
          let c = conflicts pG matching in
          match c with
          | [] -> true
          | _ ->
            begin
              let d = choose decisions c pG uG in (* choose decision from the set of conflicts *)
              if d = decisions then               (* If no decision is consistent with previous decisions  *)
                clean_up ()                       (* Then back track (otherwise recurse with new decision) *)
              else
                go d
            end
        end
    in
    go []
end
