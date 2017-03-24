open Pervasives
open BatPervasives
open Apak

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

module Make (Predicate : Symbol) = struct
  type predicate = Predicate.t
  type str = (int * (predicate * int list) BatEnum.t)
  type t = { str1 : str;
             str2 : str}

  let empty = { str1 = (0, BatEnum.empty ());
                str2 = (0, BatEnum.empty ()) }

  (* Just store info -- don't do any processing eagerly *)
  let make univ1 props1 univ2 probs2 =
    { str1 = (univ1, props1);
      str2 = (univ2, probs2)}

  module DA = BatDynArray
  module Vset = BatSet.Make(Putil.PInt)
  module Pset = BatSet.Make(Predicate)
  type u_graph = { u : Vset.t DA.t;
                   v : Vset.t DA.t}
  type p_graph = { adj : int DA.t DA.t;
                   u_label : (int list) DA.t;
                   v_label : (int list) DA.t}

  (* Make Signature of Each Variable in str *)
  let make_sigs ((univ, props) : str) : Pset.t DA.t =
    let sigs = DA.init (univ + 1) (fun _ -> Pset.empty) in
    let f (pred, vars) : unit =
      let rec go vars : unit =
        match vars with
        | [] -> ()
        | hv :: tv -> DA.set sigs hv (Pset.add pred (DA.get sigs hv)); go tv
      in
      go vars
    in
    BatEnum.iter f props;
    sigs

  let print_u_graph (g : u_graph) : unit =
    DA.iteri (fun i adj -> logf ~level:`always "%d {%a}" i (ApakEnum.pp_print_enum Format.pp_print_int) (Vset.enum adj)) g.u

  let rec unit_prop (g : u_graph) : unit =
    let prop : bool ref = ref false in
    let remove u v =
      Vset.iter (fun k ->
          if k <> u then
            begin
              prop := true;
              DA.set g.u k (Vset.remove v (DA.get g.u k));
            end) (DA.get g.v v);
      DA.set g.v v (Vset.singleton u)
    in
    DA.iteri (fun i adj -> if (Vset.cardinal adj) == 1 then begin remove i (Vset.choose adj) end) g.u;
    if (!prop) then begin unit_prop g end

  (* Make Universe Graph (Potential mappings of variables in str1 to variables in str2) *)
  let make_ugraph (emb : t) : u_graph =
    let x_sigs = make_sigs emb.str1 in
    let y_sigs = make_sigs emb.str2 in
    let u = DA.init (DA.length x_sigs) (fun _ -> Vset.empty) in
    let v = DA.init (DA.length y_sigs) (fun _ -> Vset.empty) in
    let update i j xsig ysig : unit =
      if i <> 0 && j <> 0 && (Pset.subset xsig ysig) then
        begin
          DA.set u i (Vset.add j (DA.get u i));
          DA.set v j (Vset.add i (DA.get v j))
        end
    in
    DA.iteri (fun i xsig -> DA.iteri (fun j ysig -> update i j xsig ysig) y_sigs) x_sigs;
    let u_graph = { u = u; v = v} in
    unit_prop u_graph; (* Simplify Graph *)
    u_graph

  let max_matching (g : u_graph) : int =
    let matching_u = DA.init (DA.length g.u) (fun _ -> -1) in
    let matching_v = DA.init (DA.length g.v) (fun _ -> -1) in
    let visited = DA.init (DA.length g.u) (fun _ -> 0) in
    let count : int ref = ref 0 in
    let rec f i : unit =
      let rec dfs u iter : bool =
        if (u == DA.length g.u) || (DA.get visited u) == iter then false else
          begin
            DA.set visited u iter;
            Vset.exists
              (fun v ->
                if ((DA.get matching_v v) < 0) || (dfs (u+1) iter) then
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
          if i == 0 || (dfs i i) then begin incr count end; f (i + 1)
        end
    in (f 0); (!count)

  (* Decision Procedure for Embedding Algorithm *)
  let embeds embedding =
    let uG = make_ugraph embedding in
    (max_matching uG) == (DA.length uG.u)
end
