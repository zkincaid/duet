open Syntax
open Apak
open BatPervasives

include Log.Make(struct let name = "ark.transition" end)

module type Var = sig
  type t
  val pp : Format.formatter -> t -> unit
  val show : t -> string
  val typ : t -> [ `TyInt | `TyReal ]
  val compare : t -> t -> int
  val symbol_of : t -> symbol
  val of_symbol : symbol -> t option
end

module Make
    (C : sig
       type t
       val context : t context
     end)
    (Var : Var) =
struct
  module M = BatMap.Make(Var)

  type var = Var.t

  type t =
    { transform : (C.t term) M.t;
      guard : C.t formula }

  type iter = C.t Iteration.Split.split_iter

  let compare x y =
    match Formula.compare x.guard y.guard with
    | 0 -> M.compare Term.compare x.transform y.transform
    | cmp -> cmp

  let ark = C.context

  let pp formatter tr =
    Format.fprintf formatter "{@[<v 0>";
    ApakEnum.pp_print_enum_nobox
       ~pp_sep:(fun formatter () -> Format.pp_print_break formatter 0 0)
       (fun formatter (lhs, rhs) ->
          Format.fprintf formatter "%a := @[%a@]"
            Var.pp lhs
            (Term.pp ark) rhs)
       formatter
       (M.enum tr.transform);
    begin match Formula.destruct ark tr.guard with
      | `Tru -> ()
      | _ ->
        if not (M.is_empty tr.transform) then
          Format.pp_print_break formatter 0 0;
        Format.fprintf formatter "when @[<v 0>%a@]" (Formula.pp ark) tr.guard
    end;
    Format.fprintf formatter "@]}"

  let show = Apak.Putil.mk_show pp

  let construct guard assignment =
    { transform =
        List.fold_left (fun m (v, term) -> M.add v term m) M.empty assignment;
      guard = guard }

  let assign v term =
    { transform = M.add v term M.empty;
      guard = mk_true ark }

  let parallel_assign assignment = construct (mk_true ark) assignment

  let assume guard = construct guard []

  let havoc vars =
    let transform =
      List.fold_left (fun transform v ->
          M.add
            v
            (mk_const ark (mk_symbol ark ~name:"havoc" (Var.typ v :> typ)))
            transform)
        M.empty
        vars
    in
    { transform = transform; guard = mk_true ark }

  let mul left right =
    let fresh_skolem =
      Memo.memo (fun sym ->
          let name = show_symbol ark sym in
          let typ = typ_symbol ark sym in
          mk_const ark (mk_symbol ark ~name typ))
    in
    let left_subst sym =
      match Var.of_symbol sym with
      | Some var ->
        if M.mem var left.transform then
          M.find var left.transform
        else
          mk_const ark sym
      | None -> fresh_skolem sym
    in
    let guard =
      mk_and ark [left.guard;
                  substitute_const ark left_subst right.guard]
    in
    let transform =
      M.fold (fun var term transform ->
          if M.mem var transform then
            transform
          else
            M.add var term transform)
        left.transform
        (M.map (substitute_const ark left_subst) right.transform)
    in
    { transform; guard }

  let add left right =
    let left_eq = ref [] in
    let right_eq = ref [] in
    let transform =
      let merge v x y =
        match x, y with
        | Some s, Some t when Term.equal s t -> Some s
        | _, _ ->
          let phi =
            mk_symbol ark ~name:("phi_" ^ (Var.show v)) ((Var.typ v) :> typ)
            |> mk_const ark
          in
          let left_term =
            match x with
            | Some s -> s
            | None -> mk_const ark (Var.symbol_of v)
          in
          let right_term =
            match y with
            | Some t -> t
            | None -> mk_const ark (Var.symbol_of v)
          in
          left_eq := (mk_eq ark left_term phi)::(!left_eq);
          right_eq := (mk_eq ark right_term phi)::(!right_eq);
          Some phi
      in
      M.merge merge left.transform right.transform
    in
    let guard =
      mk_or ark [mk_and ark (left.guard::(!left_eq));
                 mk_and ark (right.guard::(!right_eq))]
    in
    { guard; transform }

  module Iter = struct

    (* Canonical names for post-state symbols.  Having canonical names
       simplifies equality testing and widening. *)
    let post_symbol =
      Memo.memo (fun sym ->
          match Var.of_symbol sym with
          | Some var ->
            mk_symbol ark ~name:(Var.show var ^ "'") (Var.typ var :> typ)
          | None -> assert false)

    let alpha ?(split=true) tr =
      let (tr_symbols, post_def) =
        M.fold (fun var term (symbols, post_def) ->
            let pre_sym = Var.symbol_of var in
            let post_sym = post_symbol pre_sym in
            let post_term = mk_const ark post_sym in
            ((pre_sym,post_sym)::symbols,
             (mk_eq ark post_term term)::post_def))
          tr.transform
          ([], [])
      in
      let exists =
        let post_symbols =
          List.fold_left
            (fun set (_, sym') -> Symbol.Set.add sym' set)
            Symbol.Set.empty
            tr_symbols
        in
        fun x ->
          match Var.of_symbol x with
          | Some _ -> true
          | None -> Symbol.Set.mem x post_symbols
      in
      let body =
        ArkSimplify.simplify_terms ark (mk_and ark (tr.guard::post_def))
      in
      if split then
        Iteration.Split.abstract_iter ~exists ark body tr_symbols
      else
        Iteration.abstract_iter ~exists ark body tr_symbols
        |> Iteration.Split.lift_split

    let closure ?(use_ocrs=false) iter =
      let transform =
        List.fold_left (fun tr (pre, post) ->
            match Var.of_symbol pre with
            | Some v -> M.add v (mk_const ark post) tr
            | None -> assert false)
          M.empty
          (Iteration.Split.tr_symbols iter)
      in
      { transform = transform;
        guard = Iteration.Split.closure ~use_ocrs iter }

    let join = Iteration.Split.join

    let widen = Iteration.Split.widen

    let equal = Iteration.Split.equal

    let pp = Iteration.Split.pp_split_iter

    let show = Iteration.Split.show_split_iter
  end

  let star ?(split=true) ?(use_ocrs=false) tr =
    Iter.closure ~use_ocrs (Iter.alpha ~split tr)


  let zero =
    { transform = M.empty; guard = mk_false ark }

  let one =
    { transform = M.empty; guard = mk_true ark }

  let is_zero tr =
    match Formula.destruct ark tr.guard with
    | `Fls -> true
    | _ -> false

  let is_one tr =
    match Formula.destruct ark tr.guard with
    | `Tru -> M.is_empty tr.transform
    | _ -> false

  let widen x y =
    (* Introduce fresh symbols for variables in the transform of x/y, then
       abstract x and y to a cube over pre-symbols and these fresh symbols.
       Widen in the cube domain, then covert back to a formula. *)
    let (transform, post_sym) =
      let add (map, post) var =
        if M.mem var map then
          (map, post)
        else
          let name = Var.show var ^ "'" in
          let sym = mk_symbol ark ~name (Var.typ var :> typ) in
          (M.add var (mk_const ark sym) map, Symbol.Set.add sym post)
      in
      BatEnum.fold
        add
        (BatEnum.fold add (M.empty, Symbol.Set.empty) (M.keys y.transform))
        (M.keys x.transform)
    in
    let exists sym =
      match Var.of_symbol sym with
      | Some v -> true
      | None -> Symbol.Set.mem sym post_sym
    in
    let to_cube z =
      let eqs =
        M.fold (fun var term eqs ->
            let term' =
              if M.mem var z.transform then
                M.find var z.transform
              else
                mk_const ark (Var.symbol_of var)
            in
            (mk_eq ark term term')::eqs)
          transform
          []
      in
      mk_and ark (z.guard::eqs)
      |> Cube.abstract ~exists ark
    in
    let guard =
      Cube.widen (to_cube x) (to_cube y)
      |> Cube.to_formula
    in
    { transform; guard }

  let widen x y =
    if is_zero x then y
    else if is_zero y then x
    else widen x y

  (* alpha equivalence - only works for normalized transitions! *)
  exception Not_normal
  let equiv x y =
    let sigma =
      let map =
        M.fold (fun v rhs m ->
            match Term.destruct ark rhs,
                  Term.destruct ark (M.find v y.transform) with
            | `App (a, []), `App (b, []) -> Symbol.Map.add a (mk_const ark b) m
            | _ -> raise Not_normal)
          x.transform
          Symbol.Map.empty
      in
      fun sym ->
        try Symbol.Map.find sym map
        with Not_found -> mk_const ark sym
    in
    let x_guard = substitute_const ark sigma x.guard in
    let equiv = ArkSimplify.simplify_terms ark (mk_iff ark x_guard y.guard) in
    match Cube.is_sat ark (mk_not ark equiv) with
    | `Unsat -> true
    | _ -> false

  let equiv x y =
    try equiv x y
    with | Not_found -> false
         | Not_normal -> false

  let equal x y = compare x y = 0 || equiv x y
  let exists p tr =
    let transform = M.filter (fun k _ -> p k) tr.transform in
    let rename =
      Memo.memo (fun sym ->
          mk_symbol ark ~name:(show_symbol ark sym) (typ_symbol ark sym))
    in
    let sigma sym =
      let sym' = match Var.of_symbol sym with
        | Some v -> if p v then sym else rename sym
        | None -> sym
      in
      mk_const ark sym'
    in
    { transform = M.map (substitute_const ark sigma) transform;
      guard = substitute_const ark sigma tr.guard }

  let mem_transform x tr = M.mem x tr.transform
  let get_transform x tr = M.find x tr.transform
  let transform tr = M.enum tr.transform
  let guard tr = tr.guard

  let interpolate trs post =
    let trs =
      trs |> List.map (fun tr ->
          let fresh_skolem =
            Memo.memo (fun sym ->
                match Var.of_symbol sym with
                | Some v -> mk_const ark sym
                | None ->
                  let name = show_symbol ark sym in
                  let typ = typ_symbol ark sym in
                  mk_const ark (mk_symbol ark ~name typ))
          in
          { transform = M.map (substitute_const ark fresh_skolem) tr.transform;
            guard = substitute_const ark fresh_skolem tr.guard })
    in
    let z3 = ArkZ3.mk_context ark [] in
    let unsubscript_tbl = Hashtbl.create 991 in
    let subscript_tbl = Hashtbl.create 991 in
    let subscript sym =
      try
        Hashtbl.find subscript_tbl sym
      with Not_found -> mk_const ark sym
    in
    let unsubscript sym =
      try
        Hashtbl.find unsubscript_tbl sym
      with Not_found -> mk_const ark sym
    in
    (* Convert tr into a formula, and simultaneously update the subscript
       table *)
    let to_ss_formula tr =
      let (ss, phis) =
        M.fold (fun var term (ss, phis) ->
            let var_sym = Var.symbol_of var in
            let var_ss_sym = mk_symbol ark (Var.typ var :> typ) in
            let var_ss_term = mk_const ark var_ss_sym in
            let term_ss = substitute_const ark subscript term in
            Hashtbl.add unsubscript_tbl var_ss_sym (mk_const ark var_sym);
            ((var_sym, var_ss_term)::ss,
             mk_eq ark var_ss_term term_ss::phis))
          tr.transform
          ([], [substitute_const ark subscript tr.guard])
      in
      List.iter (fun (k, v) -> Hashtbl.add subscript_tbl k v) ss;
      mk_and ark phis
    in
    let seq =
      List.fold_left
        (fun subscripted tr ->
           (to_ss_formula tr)::subscripted)
        []
        trs
    in
    let ss_post = substitute_const ark subscript (mk_not ark post) in
    match z3#interpolate_seq (List.rev (ss_post::seq)) with
    | `Sat m -> `Invalid
    | `Unknown -> `Unknown
    | `Unsat itp ->
      `Valid (List.map (substitute_const ark unsubscript) itp)

  let valid_triple phi path post =
    let path_not_post = List.fold_right mul path (assume (mk_not ark post)) in
    match Smt.is_sat ark (mk_and ark [phi; path_not_post.guard]) with
    | `Sat -> `Invalid
    | `Unknown -> `Unknown
    | `Unsat -> `Valid

end
