open Syntax

type 'a t =
  { formula : 'a formula;
    symbols : (symbol * symbol) list;
    exists : (symbol -> bool) }

include Log.Make(struct let name = "srk.transitionFormula" end)


let identity srk symbols =
  let formula = 
    List.map (fun (sym, sym') ->
        mk_eq srk (mk_const srk sym) (mk_const srk sym'))
      symbols
    |> mk_and srk
  in
  let exists _ = true in
  { formula; symbols; exists }

let zero srk symbols = let exists _ = true in { formula = mk_false srk; symbols; exists}

let pre_symbols tr_symbols =
  List.fold_left (fun set (s,_) ->
      Symbol.Set.add s set)
    Symbol.Set.empty
    tr_symbols

let post_symbols tr_symbols =
  List.fold_left (fun set (_,s') ->
      Symbol.Set.add s' set)
    Symbol.Set.empty
    tr_symbols

(* Map from pre-state vars to their post-state counterparts *)
let post_map srk tr_symbols =
  List.fold_left
    (fun map (sym, sym') -> Symbol.Map.add sym (mk_const srk sym') map)
    Symbol.Map.empty
    tr_symbols

let pre_map srk tr_symbols =
  List.fold_left
    (fun map (sym, sym') -> Symbol.Map.add sym' (mk_const srk sym) map)
    Symbol.Map.empty
    tr_symbols

let formula tf = tf.formula
let symbols tf = tf.symbols
let exists tf = tf.exists

let make ?(exists=fun _ -> true) formula symbols =
  { exists; formula; symbols }

let wedge_hull srk tf =
  let post_symbols = post_symbols tf.symbols in
  let subterm x = not (Symbol.Set.mem x post_symbols) in
  Wedge.abstract ~exists:tf.exists ~subterm srk tf.formula

let is_symbolic_constant tf =
  let pre_symbols = pre_symbols tf.symbols in
  let post_symbols = post_symbols tf.symbols in
  fun x -> tf.exists x && (not (Symbol.Set.mem x pre_symbols || Symbol.Set.mem x post_symbols))

let symbolic_constants tf =
  Symbol.Set.filter (is_symbolic_constant tf) (Syntax.symbols tf.formula)

let mul srk tf1 tf2 =
  if (tf1.symbols != tf2.symbols) then
    invalid_arg "TransitionFormula.mul: incompatible transition formulas";
  let fresh_symbols = ref Symbol.Set.empty in
  let (map1, map2) =
    List.fold_left (fun (phi_map, psi_map) (sym, sym') ->
        let mid_name = "mid_" ^ (show_symbol srk sym) in
        let mid_symbol =
          mk_symbol srk ~name:mid_name (typ_symbol srk sym)
        in
        fresh_symbols := Symbol.Set.add mid_symbol (!fresh_symbols);
        let mid = mk_const srk mid_symbol in
        (Symbol.Map.add sym' mid phi_map,
         Symbol.Map.add sym mid psi_map))
      (Symbol.Map.empty, Symbol.Map.empty)
      tf1.symbols
  in
  let subst1 = substitute_map srk map1 in
  let rename =
    Memo.memo (fun x ->
        let fresh =
          mk_symbol srk ~name:(show_symbol srk x) (typ_symbol srk x)
        in
        fresh_symbols := Symbol.Set.add fresh (!fresh_symbols);
        mk_const srk fresh)
  in
  let subst2 = (* rename Skolem constants *)
    substitute_const srk
      (fun x ->
        if Symbol.Map.mem x map2 then
          Symbol.Map.find x map2
        else if tf2.exists x then
          mk_const srk x
        else rename x)
  in
  { symbols = tf1.symbols;
    exists = (fun x -> tf1.exists x && not (Symbol.Set.mem x !fresh_symbols));
    formula = mk_and srk [subst1 tf1.formula; subst2 tf2.formula] }

let add srk tf1 tf2 =
  if (tf1.symbols != tf2.symbols) then
    invalid_arg "TransitionFormula.add: incompatible transition formulas";
  { tf1 with formula = mk_or srk [tf1.formula; tf2.formula]  }

let linearize srk tf =
  { tf with formula = Nonlinear.linearize srk tf.formula }

let map_formula f tf = { tf with formula = f tf.formula }

let preimage srk tf state =
  logf "preimage of transition formula: %a" (Formula.pp srk) tf.formula;
  logf "and state formula: %a" (Formula.pp srk) state;
  let open Syntax in
  let tf = linearize srk tf in
  let fresh_skolem =
    Memo.memo (fun sym ->
        let name = show_symbol srk sym in
        let typ = typ_symbol srk sym in
        mk_const srk (mk_symbol srk ~name typ))
  in
  let post_map =
    List.fold_left
      (fun map (sym, sym') -> Symbol.Map.add sym sym' map)
      Symbol.Map.empty
      tf.symbols
  in
  let pre_map =
    List.fold_left
      (fun map (sym, sym') -> Symbol.Map.add sym' sym map)
      Symbol.Map.empty
      tf.symbols
  in
  (* let post_map = post_map srk tf.symbols in *)
  (* let pre_map = pre_map srk tf.symbols in *)
  let pre_to_fresh_skolems_map = Symbol.Map.fold 
    (fun sym _ m -> 
      Symbol.Map.add sym (fresh_skolem sym) m)
    post_map 
    Symbol.Map.empty in
  let subst_tf sym = 
    match Symbol.Map.find_opt sym pre_map with 
    | Some pre_symbol -> Symbol.Map.find pre_symbol pre_to_fresh_skolems_map 
    | None -> mk_const srk sym 
  in
  let subst_state sym =
    match ((exists tf) sym) with
    | true -> 
      begin 
        match (Symbol.Map.find_opt sym post_map) with 
          | Some _ -> Symbol.Map.find sym pre_to_fresh_skolems_map 
          | _ -> mk_const srk sym
      end
    | false -> fresh_skolem sym
  in
  let result = mk_and srk [substitute_const srk subst_tf (formula tf); substitute_const srk subst_state state]
  in
  logf "result state formula: %a" (Formula.pp srk) result;
  result 
