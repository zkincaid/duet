open BatHashcons
open Printf
open Pathexpr
open WeightedGraph

include Log.Make(struct let name = "srk.nestedLoops" end)

(* module SCC = Graph.Components.Make(U) *)
module Solver = SrkZ3.Solver

(* TODO: refactor loop nesting relation from label algebras *)
type 'a loops =
    { 
        header: vertex;
        splitted_hd: vertex;
        loop_body_vertices: vertex list;
        back_edge: vertex * vertex * 'a;
        children: 'a loops list;
        depth: int;
        header_f: 'a;
        body_f: 'a;
    }

let print_loop {header; splitted_hd; loop_body_vertices; back_edge; children; depth; header_f; body_f} =
    printf "\n======== Loop ======== \n";
    printf "header: %d\nsplitted_hd: %d\ndepth: %d\n" header splitted_hd depth;
    let (x, y, _) = back_edge in 
    printf "back edge: %d %d\n"  x y;
    printf "loop body:\n";
    List.iter (fun x -> printf "%d " x) loop_body_vertices;
    printf "\n";
    printf "Children's headers:";
    List.iter (fun r -> printf "%d " r.header) children;
    printf "\n====== end loop ======\n"


(** Decide if v is a header for the i-th SCC in wg by looking at whether
    its coming edges are all in this scc.
    `f` is an SCC function that maps each v to its SCC component number.
*)
let is_header wg f i_th_scc v = 
    fold_pred_e 
        (fun (u, weight, v) (acc) -> (f u <> i_th_scc) || acc)
        wg
        v
        false
    
(** find a header and a backedge that goes into the header *)
(* replace filter with find *)
let find_header_backedge wg f i_th_scc scc =
    printf "... finding a header and a backedge ... \n";
    let headers = List.filter (is_header wg f i_th_scc) scc in
    match headers with
    | [] -> assert false
    (* we assume that only allowing 1 header is enough *)
    | hd :: _ -> 
        let backedge_list = 
        fold_pred_e 
            (fun (u, weight, v) l -> if (List.mem u scc) then (u, weight) :: l else l)
            wg
            hd
            []
        in
        match backedge_list with
        | [] -> assert false
        | t :: _ -> (fst t, hd, snd t)

(** replace the pos-th element in l with a *)
let replace l pos a = 
    List.mapi (fun i x -> if i = pos then a else x) l

(** Assign child loops to parent loops, given two lists of loops.
    `f` is the SCC function that maps vertex to SCC component number, which a by-product of
    parent loop computation.
 *)
let rec assign_child_loops l_parent l_children f =
    printf "... trying to assign child loops to parent loops\n";
    printf "parent list:\n";
    List.iteri (fun i l -> match l with None -> printf "%d:{}\n" i | Some ll -> printf "%d:" i; print_loop ll) l_parent;
    printf "children list:\n";
    List.iter (fun l -> print_loop l) l_children;

    match l_children with
    | [] -> l_parent
    | hd :: tail -> 
        let parent_ord = f hd.header in
        let parent_loop = (List.nth l_parent parent_ord) in
        match parent_loop with 
            | None -> assert false 
            | Some parent_loop ->
                printf "this child should be assigned to %d -th parent\n" parent_ord;
                replace 
                    (assign_child_loops l_parent tail f) 
                    parent_ord 
                    (Some { parent_loop with children = hd :: parent_loop.children })
                    

(** Remove all backedges (top-level) recorded in a list of loops from wg *)
let rec remove_all_backedges wg l_loops =
    match l_loops with
    | [] -> wg
    | loop_op :: tail -> 
        begin
            match loop_op with
            | None -> remove_all_backedges wg tail
            | Some loop ->
            let (u, v, _) = loop.back_edge in
            let wgn = remove_edge wg u v in
                remove_all_backedges wgn tail
        end

(** compute a tree of nested loops, returns a tuple of
    (a wg with all backedges deleted, a list of loops at the top level)
*)
let rec compute_nested_loops wg d =
    printf "\n\nComputing loop nesting relations at level %d\n" d;
    (* if d>5 then assert false; *)
    let (m, (n, f), scc_list) = get_non_trivial_scc wg in
    if m = 0 then 
    begin
        printf "Cannot find non-trivial SCC at level %d\n" d; (wg, []) 
    end
    else 
    begin
        (* first compute the SCC *)
        (* within each scc identify the header, back edge *)
        printf "number of non-trivial SCCs: %d\nSCCs:\n" m;
        List.iteri 
            (fun i scc ->
                printf "%d: " i;
                List.iter (printf "%d ") scc;
                printf "\n"
            )
            scc_list;
        let results_1 = 
            List.mapi 
                (fun i_th_scc scc -> 
                    if List.length scc > 1 then
                        let (hd_pred, hd, be) = find_header_backedge wg f i_th_scc scc in
                        let r = {
                            header = hd;
                            splitted_hd = hd;
                            loop_body_vertices = scc;
                            back_edge = (hd_pred, hd, be);
                            children = [];
                            depth = d;
                            header_f = get_true_from_algebra wg;
                            body_f = get_true_from_algebra wg;
                        } in
                        print_loop r;
                        Some r
                    else
                        None
                )   
                scc_list 
        in
        (* delete all back edges at this depth *)
        let new_wg = remove_all_backedges wg results_1 in
        (* recursively compute child loops from the modified wg *)
        let (nnwg, child_loops) = compute_nested_loops new_wg (d+1) in
        let results_2 = assign_child_loops results_1 child_loops f in
        let results_3 = List.filter (fun x -> match x with None -> false | Some x -> true) results_2 in
        let results = List.map (fun x -> match x with None -> assert false | Some x -> x) results_3 in
        (nnwg, results)
    end

let split_header wg hd body_f loop =
    printf "... now trying to split header of the following loop:\n";
    print_loop loop;
    let alg = get_algebra wg in
    let new_vertex = (max_vertex wg)+1 in
    printf "new vertex has number: %d\n" new_vertex;
    (split_vertex wg hd (alg.star body_f) new_vertex, new_vertex)

(** Compute loop body formula recursively from inside out. 
    `wg_no_bg` is weighted graph without back edges
    `loop` is a loops object, with all fields except header_F and body_f`populated
    `f` is a function that computes the loop body formula based on header and back edge info
*)
let rec compute_body_weight wg_no_bg loop =
    printf "... computing body weight of the following loop:\n";
    print_loop loop;
    (* should split the parent loop header first *)
    let compute_body_with_header_and_backedge wg hd hd_pred be =
        let a = get_algebra wg in
        a.mul (path_weight wg hd hd_pred) be
    in
    if loop.children = [] then 
    begin
        printf "this loop is a terminal loop";
        let (hd_pred, hd, be) = loop.back_edge in
        let bf = compute_body_with_header_and_backedge wg_no_bg hd hd_pred be in
        let (wgnn, splitted_vertex) = split_header wg_no_bg hd bf loop in
            (wgnn,
            { loop with splitted_hd = splitted_vertex; body_f = bf}) 
    end
    else 
        (* simultaneously compute transformed graph and list of processed children *)
        let (wgg, processed_children) = 
            List.fold_right
                (fun child tup -> 
                    let (wgt, list) = tup in
                    let (wgtt, processed_loop) = compute_body_weight wgt child in
                    (wgtt, processed_loop :: list)
                )
                loop.children
                (wg_no_bg, [])
        in
        let finished_children = processed_children in
        let (hd_pred, hd, be) = loop.back_edge in
        let bf = compute_body_with_header_and_backedge wgg hd hd_pred be in
            let (wgnn, splitted_vertex) = split_header wgg hd bf loop in
            (wgnn, 
            { loop with splitted_hd = splitted_vertex; body_f = bf; children = finished_children})


(** Compute a path from beginning to the header of this loop and all its children loops,
    given a weighted graph with all back edges removed and header splitted to contain
    the label of the loop body. 
    `start_to_v` is a function that computes the path from the entry to any vertex. 
    `combine` is a function that constructs the path in the form header * star(body). 
 *)
let rec compute_path_to_header wg_no_bg_and_splitted_headers loop start =
    let construct_header_guard path_to_hd body_f =
        let alg = get_algebra wg_no_bg_and_splitted_headers in
        alg.mul path_to_hd (alg.star body_f)
    in
    let splitted_hd = loop.splitted_hd in
    if splitted_hd = loop.header then
        assert false
    else
        let bf = loop.body_f in
        if loop.children = [] then
            {
                loop with 
                    header_f = construct_header_guard 
                                    (path_weight wg_no_bg_and_splitted_headers start splitted_hd) 
                                    bf
            }
        else
            let processed_children =
                List.map
                    (fun child ->
                        compute_path_to_header 
                            wg_no_bg_and_splitted_headers  
                            child  
                            start)
                    loop.children
            in
            {
                loop with
                    header_f = construct_header_guard 
                                    (path_weight wg_no_bg_and_splitted_headers start splitted_hd) 
                                    bf;
                    children = processed_children
            }

let rec flatten_loops loops_l results =
    match loops_l with
    | [] -> results
    | hd :: tl -> 
        begin
            let r1 = flatten_loops hd.children results in
            let r2 = (hd.header_f, hd.body_f) :: r1 in
            flatten_loops tl r2
        end


let compute_all_nested_loops wg start =
    let (wg_no_backedges, l_top_loops) = compute_nested_loops wg 0 in
    let (wgg, loops_with_body_f) = 
            List.fold_right
                (fun top_level_loop acc -> 
                    let (wgt, list) = acc in
                    let (wgtt, processed_loop) = compute_body_weight wgt top_level_loop in
                    (wgtt, processed_loop :: list)
                )
                l_top_loops
                (wg_no_backedges, [])
    in
    let top_level_loops_l =
    List.map
        (fun top_level_loop -> 
            compute_path_to_header wgg top_level_loop start)
        loops_with_body_f
    in
    let flattened_loops_l = flatten_loops top_level_loops_l []
    in
    (top_level_loops_l, flattened_loops_l)

(* let rec print_final_results loops =
  if List.length loops > 0 then printf "\n\n\n=========== Showing final results ==========\n\n\n";
  List.iter 
    (fun loop ->
        NL.print_loop loop;
        printf "path to header: %s\n" (T.show loop.NL.header_f);
        printf "loop body: %s\n" (T.show loop.NL.body_f);
        print_final_results loop.NL.children
    )
    loops *)

let print_flattened_results show loops =
printf "\n\n\n********* Printing flattened loops **********\n\n\n";
 List.iteri
  (fun i (header_f, body_f) -> 
    printf "%d-th loop:\n" i;
    printf "path to header: %s\n" (show header_f);
    printf "loop body: %s\n" (show body_f);
  )
  loops

