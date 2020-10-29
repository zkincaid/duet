open Syntax

type 'a t =
  { formula : 'a formula;
    symbols : (symbol * symbol) list;
    exists : (symbol -> bool) }

let identity srk symbols =
  let formula = 
    List.map (fun (sym, sym') ->
        mk_eq srk (mk_const srk sym) (mk_const srk sym'))
      symbols
    |> mk_and srk
  in
  let exists _ = true in
  { formula; symbols; exists }

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
  let (map1, map2) =
    List.fold_left (fun (phi_map, psi_map) (sym, sym') ->
        let mid_name = "mid_" ^ (show_symbol srk sym) in
        let mid_symbol =
          mk_symbol srk ~name:mid_name (typ_symbol srk sym)
        in
        let mid = mk_const srk mid_symbol in
        (Symbol.Map.add sym' mid phi_map,
         Symbol.Map.add sym mid psi_map))
      (Symbol.Map.empty, Symbol.Map.empty)
      tf1.symbols
  in
  let subst1 = substitute_map srk map1 in
  let fresh_symbols = ref Symbol.Set.empty in
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
