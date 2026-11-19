open Syntax

module TF = TransitionFormula

(** The array-to-integer correspondence produced by [project] and used to
    lift scalar summaries back to array formulas.

    [index] is the variable used to denote the symbolic index of the array.
    [mapping] maps array transition symbols and array-valued symbolic
    constants to integer symbols representing their contents at the
    symbolic index [index].
*)
type correspondence =
  { index : symbol
  ; mapping : symbol Symbol.Map.t }

let index correspondence = correspondence.index
let mapped_symbol correspondence array = Symbol.Map.find_opt array correspondence.mapping

let project srk tf =
  let index = mk_symbol srk ~name:"ama_index" `TyInt in
  let mapping = ref Symbol.Map.empty in
  let get_or_create_symbol array =
    match Symbol.Map.find_opt array !mapping with
    | Some value -> value
    | None ->
      let value = mk_symbol srk ~name:(show_symbol srk array ^ "_cell") `TyInt in
      mapping := Symbol.Map.add array value !mapping;
      value
  in
  let is_array symbol = typ_symbol srk symbol = `TyArr in
  let pairs =
    List.map (fun (pre, post) ->
        if is_array pre && is_array post then
          (get_or_create_symbol pre, get_or_create_symbol post)
        else if is_array pre || is_array post then
          invalid_arg "SkolemFragment.project: mismatched array transition pair"
        else (pre, post))
      (TF.symbols tf)
  in
  let constants =
    Symbol.Set.fold (fun symbol constants ->
        Symbol.Set.add
          (if is_array symbol then get_or_create_symbol symbol else symbol)
          constants)
      (TF.symbolic_constants tf)
      (Symbol.Set.singleton index)
  in
  let bindings =
    Symbol.Map.fold (fun array value bindings ->
        mk_eq srk (mk_const srk value)
          (mk_select srk (mk_const srk array) (mk_const srk index))
        :: bindings)
      !mapping []
  in
  let formula = mk_and srk (TF.formula tf :: bindings) in
  (* Existentially quantify the original arrays by marking them as Skolems.
     This records their quantification in the transition formula's metadata,
     without adding explicit quantifiers to its body. *)
  let state = Symbol.Set.union (TF.pre_symbols pairs) (TF.post_symbols pairs) in
  let exists symbol = Symbol.Set.mem symbol constants || Symbol.Set.mem symbol state in
  ({ index; mapping = !mapping }, TF.make ~exists formula pairs)

let lift srk correspondence formula =
  let substitutions =
    Symbol.Map.fold (fun array value substitutions ->
        Symbol.Map.add value
          (mk_select srk (mk_const srk array) (mk_const srk correspondence.index))
          substitutions)
      correspondence.mapping Symbol.Map.empty
  in
  substitute_map srk substitutions formula
  |> mk_forall_const srk correspondence.index
