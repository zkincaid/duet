module Make
         (G : sig
            type t
            module V : sig
              type t
              val compare : t -> t -> int
              val hash : t -> int
              val equal : t -> t -> bool
            end
            module E : sig
              type t
              val src : t -> V.t
            end
            val iter_vertex : (V.t -> unit) -> t -> unit
            val iter_succ : (V.t -> unit) -> t -> V.t -> unit
            val fold_pred_e : (E.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
          end)
         (Domain : sig
            type t
            type edge = G.E.t
            val join : t -> t -> t
            val widening : t -> t -> t
            val equal : t -> t -> bool
            val transform : edge -> t -> t
          end) = struct
  module L = Loop.Make(G)
  module A = Hashtbl.Make(G.V)

  (* Compute fixpoint according to the recursive strategy in
     Bourdoncle's "Efficient chaotic iteration strategies with
     widenings" *)
  let analyze ?(delay=0) graph init =
    let loop_nest = L.loop_nest graph in
    let annotation = A.create 991 in
    let get_annotation vertex =
      try A.find annotation vertex
      with Not_found -> init vertex
    in
    let set_annotation vertex data =
      A.replace annotation vertex data
    in
    let next_annotation v =
      G.fold_pred_e (fun e flow_in ->
          Domain.join
            flow_in
            (Domain.transform e (get_annotation (G.E.src e))))
        graph
        v
        (get_annotation v)
    in
    let rec fix = function
      | `Vertex v ->
         set_annotation v (next_annotation v)
      | `Loop loop ->
         let header = L.header loop in
         let rec fix_loop delay =
           let old_annotation = get_annotation header in
           let next_annotation = next_annotation header in
           let new_annotation =
             if delay > 0 then next_annotation
             else Domain.widening old_annotation next_annotation
           in
           set_annotation header new_annotation;
           List.iter fix (L.children loop);
           if not (Domain.equal old_annotation new_annotation)
           then fix_loop (delay - 1)
         in
         fix_loop delay
    in
    List.iter fix loop_nest;
    get_annotation
end

