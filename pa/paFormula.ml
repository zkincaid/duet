open Batteries
open Srk

let sep formatter () = Format.fprintf formatter ";@ "
let pp_print_list ?(pp_sep=sep) pp_elt formatter xs =
    SrkUtil.pp_print_enum ~pp_sep pp_elt formatter (BatList.enum xs)

let rec alpha_of_int i =
  assert (i >= 0);
  let shift = i + (Char.code 'a') in
  if shift <= (Char.code 'z') then Char.escaped (Char.chr shift)
  else "Z" ^ (alpha_of_int (shift - (Char.code 'z')))

type 'a term =
  | Var of int
  | Const of 'a

type ('a,'b) formula =
  | And of ('a,'b) formula * ('a,'b) formula
  | Or of ('a,'b) formula * ('a,'b) formula
  | Atom of 'a * ('b term) list
  | Forall of (string option) * ('a,'b) formula
  | Exists of (string option) * ('a,'b) formula
  | Eq of ('b term) * ('b term)
  | Neq of ('b term) * ('b term)
  | True
  | False

type ('a,'b,'c) open_formula = [
  | `T
  | `F
  | `And of 'c * 'c
  | `Or of 'c * 'c
  | `Atom of 'a * ('b term) list
  | `Forall of (string option) * 'c
  | `Exists of (string option) * 'c
  | `Eq of ('b term) * ('b term)
  | `Neq of ('b term) * ('b term)
]

let destruct = function
  | And (phi, psi) -> `And (phi, psi)
  | Or (phi, psi) -> `Or (phi, psi)
  | Atom (rel, args) -> `Atom (rel, args)
  | Forall (name, phi) -> `Forall (name, phi)
  | Exists (name, phi) -> `Exists (name, phi)
  | Eq (x, y) -> `Eq (x, y)
  | Neq (x, y) -> `Neq (x, y)
  | True -> `T
  | False -> `F

let rec eval alg = function
  | And (phi, psi) -> alg (`And (eval alg phi, eval alg psi))
  | Or (phi, psi) -> alg (`Or (eval alg phi, eval alg psi))
  | Atom (rel, args) -> alg (`Atom (rel, args))
  | Forall (name, phi) -> alg (`Forall (name, eval alg phi))
  | Exists (name, phi) -> alg (`Exists (name, eval alg phi))
  | Eq (x, y) -> alg (`Eq (x, y))
  | Neq (x, y) -> alg (`Neq (x, y))
  | True -> alg `T
  | False -> alg `F

let construct = function
  | `And (phi, psi) -> And (phi, psi)
  | `Or (phi, psi) -> Or (phi, psi)
  | `Atom (rel, args) -> Atom (rel, args)
  | `Forall (name, phi) -> Forall (name, phi)
  | `Exists (name, phi) -> Exists (name, phi)
  | `Eq (x, y) -> Eq (x, y)
  | `Neq (x, y) -> Neq (x, y)
  | `T -> True
  | `F -> False


(* Replace atoms, equations, and inequations appearing in a formula.  First
   parameter to the mapped function indicates quantifier depth. *)
let map_with_depth f =
  let rec go depth phi =
    match destruct phi with
    | `And (phi, psi) -> And (go depth phi, go depth psi)
    | `Or (phi, psi) -> Or (go depth phi, go depth psi)
    | `Atom (head, args) -> f depth (`Atom (head, args))
    | `Forall (name, phi) -> Forall (name, go (depth + 1) phi)
    | `Exists (name, phi) -> Exists (name, go (depth + 1) phi)
    | `Eq (x, y) -> f depth (`Eq (x, y))
    | `Neq (x, y) -> f depth (`Neq (x, y))
    | `T -> True
    | `F -> False
  in
  go 0

(* apply a substitution on constants *)
let substitute sigma =
  let bump_sigma depth = function
    | Const k -> begin match sigma k with
        | Var v' -> Var (v' + depth)
        | const -> const
      end
    | Var v -> Var v
  in
  let f depth = function
    | `Eq (x, y) -> Eq (bump_sigma depth x, bump_sigma depth y)
    | `Neq (x, y) -> Neq (bump_sigma depth x, bump_sigma depth y)
    | `Atom (p, args) -> Atom (p, List.map (bump_sigma depth) args)
  in
  map_with_depth f

let var_substitute sigma =
  let bump_sigma depth = function
    | Var v ->
      if v < depth then (* v is bound *)
        Var v
      else begin match sigma (v - depth) with
        | Var v' ->
          assert (v' >= 0); (* no variable capture! *)
          Var (v' + depth)
        | const -> const
      end
    | const -> const
  in
  let rec go depth phi =
    match destruct phi with
    | `Eq (x, y) -> Eq (bump_sigma depth x, bump_sigma depth y)
    | `Neq (x, y) -> Neq (bump_sigma depth x, bump_sigma depth y)
    | `Atom (p, args) -> Atom (p, List.map (bump_sigma depth) args)
    | `And (phi, psi) -> And (go depth phi, go depth psi)
    | `Or (phi, psi) -> Or (go depth phi, go depth psi)
    | `Forall (name, phi) -> Forall (name, go (depth + 1) phi)
    | `Exists (name, phi) -> Exists (name, go (depth + 1) phi)
    | `T -> True
    | `F -> False
  in
  go 0

let mk_forall ?name:(name=None) ?var:(var=0) phi =
  let subs v =
    if v = var then
      Var 0
    else if v < var then
      Var (v + 1)
    else
      Var v
  in
  match phi with
  | True -> True
  | False -> False
  | _ -> Forall (name, var_substitute subs phi)

let mk_exists ?name:(name=None) ?var:(var=0) phi =
  let subs v =
    if v = var then
      Var 0
    else if v < var then
      Var (v + 1)
    else
      Var v
  in
  match phi with
  | True -> True
  | False -> False
  | _ -> Exists (name, var_substitute subs phi)

let quantify equal var phi =
  let sub depth = function
    | Const k when equal k var -> Var depth
    | ow -> ow
  in
  let f depth = function
    | `Atom (p, args) -> Atom (p, List.map (sub depth) args)
    | `Eq (x, y) -> Eq (sub depth x, sub depth y)
    | `Neq (x, y) -> Neq (sub depth x, sub depth y)
  in
  map_with_depth f phi

let rec flatten_or = function
  | Or (phi, psi) -> (flatten_or phi) @ (flatten_or psi)
  | phi -> [phi]

let rec flatten_and = function
  | And (phi, psi) -> (flatten_and phi) @ (flatten_and psi)
  | phi -> [phi]

let rec flatten_universal = function
  | Forall (hint, phi) ->
    let (hints, phi') = flatten_universal phi in
    (hint::hints, phi')
  | phi -> ([], phi)

let rec flatten_existential = function
  | Exists (hint, phi) ->
    let (hints, phi') = flatten_existential phi in
    (hint::hints, phi')
  | phi -> ([], phi)

let destruct_flatten = function
  | And (phi, psi) -> `And ((flatten_and phi)@(flatten_and psi))
  | Or (phi, psi) -> `Or ((flatten_or phi)@(flatten_or psi))
  | Atom (rel, args) -> `Atom (rel, args)
  | Forall (hint, phi) ->
    let hints, phi' = flatten_universal phi in
    `Forall (hint::hints, phi')
  | Exists (hint, phi) ->
    let hints, phi' = flatten_existential phi in
    `Exists (hint::hints, phi')
  | Eq (x, y) -> `Eq (x, y)
  | Neq (x, y) -> `Neq (x, y)
  | True -> `T
  | False -> `F

let const_exists ?equal:(equal=(=)) ?name:(name=None) var phi =
  match phi with
  | True -> True
  | False -> False
  | _ -> Exists (name, quantify equal var phi)
let const_forall ?equal:(equal=(=)) ?name:(name=None) var phi =
  match phi with
  | True -> True
  | False -> False
  | _ -> Forall (name, quantify equal var phi)

let mk_true = True
let mk_false = False
let mk_and phi psi =
  match phi, psi with
  | False, x | x, False -> False
  | True, x | x, True -> x
  | _, _ ->
    if phi = psi then phi
    else And (phi, psi)

let mk_or phi psi =
  match phi, psi with
  | True, x | x, True -> True
  | False, x | x, False -> x
  | _, _ ->
    if phi = psi then phi
    else Or (phi, psi)
let mk_eq x y =
  match x, y with
  | Var i, Var j when i = j -> True
  | _, _ -> Eq (x, y)
let mk_neq x y =
  match x, y with
  | Var i, Var j when i = j -> False
  | _, _ -> Neq (x, y)
let mk_atom p args = Atom (p, args)

let big_conj conjuncts =
  if BatEnum.peek conjuncts = None then mk_true
  else BatEnum.reduce mk_and conjuncts

let big_disj disjuncts =
  if BatEnum.peek disjuncts = None then mk_false
  else BatEnum.reduce mk_or disjuncts

let pp pp_rel pp_const formatter phi =
  let open Format in
  let pp_term env formatter = function
    | Var i -> pp_print_string formatter (env i)
    | Const k -> pp_const formatter k
  in
  let gensym =
    let n = ref 0 in
    fun x ->
      incr n;
      match x with
      | Some hint -> hint ^ ":" ^ (string_of_int (!n))
      | None -> "anon:" ^ (string_of_int (!n))
  in
  let rec format env formatter = function
    | And (phi, psi) ->
      fprintf formatter "(@[";
      pp_print_list
        ~pp_sep:(fun formatter () -> fprintf formatter "@ /\\ ")
        (format env)
        formatter
        ((flatten_and phi) @ (flatten_and psi));
      fprintf formatter "@])"
    | Or (phi, psi) ->
      fprintf formatter "(@[";
      pp_print_list
        ~pp_sep:(fun formatter () -> fprintf formatter "@ \\/ ")
        (format env)
        formatter
        ((flatten_or phi) @ (flatten_or psi));
      fprintf formatter "@])"
    | Forall (x, phi) ->
      let (hints, phi') = flatten_universal phi in
      let var_names = Array.of_list (List.map gensym (x::hints)) in
      let num_vars = Array.length var_names in
      let env' n =
        if n >= num_vars then env (n - num_vars)
        else var_names.(num_vars - n - 1)
      in
      fprintf formatter "(@[forall@ ";
      SrkUtil.pp_print_enum
        ~pp_sep:pp_print_space
        pp_print_string
        formatter
        (BatArray.enum var_names);
      fprintf formatter ".@ %a@])" (format env') phi'

    | Exists (x, phi) ->
      let (hints, phi') = flatten_existential phi in
      let var_names = Array.of_list (List.map gensym (x::hints)) in
      let num_vars = Array.length var_names in
      let env' n =
        if n >= num_vars then env (n - num_vars)
        else var_names.(num_vars - n - 1)
      in
      fprintf formatter "(@[exists@ ";
      SrkUtil.pp_print_enum
        ~pp_sep:pp_print_space
        pp_print_string
        formatter
        (BatArray.enum var_names);
      fprintf formatter ".@ %a@])" (format env') phi'

    | Eq (x, y) ->
      fprintf formatter "@[%a = %a@]" (pp_term env) x (pp_term env) y
    | Neq (x, y) ->
      fprintf formatter "@[%a != %a@]" (pp_term env) x (pp_term env) y
    | Atom (rel, params) ->
      fprintf formatter "@[%a(@[%a@])@]"
        pp_rel rel
        (SrkUtil.pp_print_enum (pp_term env))
        (BatList.enum params)
    | True -> pp_print_string formatter "true"
    | False -> pp_print_string formatter "false"
  in
  let undef x =
    "free:" ^ (string_of_int x)
  in
  format undef formatter phi

let tptp3_pp pp_rel pp_const formatter phi =
  let open Format in
  let pp_term env formatter = function
    | Var i -> pp_print_string formatter (env i)
    | Const k -> pp_const formatter k
  in
  let gensym =
    let n = ref 0 in
    fun x ->
      incr n;
      "X" ^ (alpha_of_int (!n))
  in
  let rec format env formatter = function
    | And (phi, psi) ->
      fprintf formatter "(@[%a@ & %a@])"
        (format env) phi
        (format env) psi
    | Or (phi, psi) ->
      fprintf formatter "(@[%a@ | %a@])"
        (format env) phi
        (format env) psi
    | Forall (x, phi) ->
      let (hints, phi') = flatten_universal phi in
      let var_names = Array.of_list (List.map gensym (x::hints)) in
      let num_vars = Array.length var_names in
      let env' n =
        if n >= num_vars then env (n - num_vars)
        else var_names.(num_vars - n - 1)
      in
      fprintf formatter "(@[![";
      SrkUtil.pp_print_enum
        ~pp_sep:pp_print_space
        pp_print_string
        formatter
        (BatArray.enum var_names);
      fprintf formatter "]:@ %a@])" (format env') phi'

    | Exists (x, phi) ->
      let (hints, phi') = flatten_existential phi in
      let var_names = Array.of_list (List.map gensym (x::hints)) in
      let num_vars = Array.length var_names in
      let env' n =
        if n >= num_vars then env (n - num_vars)
        else var_names.(num_vars - n - 1)
      in
      fprintf formatter "(@[?[";
      SrkUtil.pp_print_enum
        ~pp_sep:pp_print_space
        pp_print_string
        formatter
        (BatArray.enum var_names);
      fprintf formatter "]:@ %a@])" (format env') phi'

    | Eq (x, y) ->
      fprintf formatter "@[%a = %a@]" (pp_term env) x (pp_term env) y
    | Neq (x, y) ->
      fprintf formatter "@[%a != %a@]" (pp_term env) x (pp_term env) y
    | Atom (rel, params) ->
      fprintf formatter "@[%a(@[%a@])@]"
        pp_rel rel
        (pp_print_list (pp_term env))
        params
    | True -> pp_print_string formatter "true"
    | False -> pp_print_string formatter "false"
  in
  let undef x =
    invalid_arg "format_tptp3: input must be a sentence"
  in
  format undef formatter phi

let smtlib2_pp pp_rel pp_const formatter phi =
  let open Format in
  let pp_term env formatter = function
    | Var i -> pp_print_string formatter (env i)
    | Const k -> pp_const formatter k
  in
  let gensym =
    let n = ref 0 in
    fun x ->
      incr n;
      "X" ^ (alpha_of_int (!n))
  in
  let rec format env formatter = function
    | And (phi, psi) ->
      fprintf formatter "(@[and %a@ %a@])"
        (format env) phi
        (format env) psi
    | Or (phi, psi) ->
      fprintf formatter "(@[or %a@ %a@])"
        (format env) phi
        (format env) psi
    | Forall (x, phi) ->
      let (hints, phi') = flatten_universal phi in
      let var_names = Array.of_list (List.map gensym (x::hints)) in
      let num_vars = Array.length var_names in
      let env' n =
        if n >= num_vars then env (n - num_vars)
        else var_names.(num_vars - n - 1)
      in
      fprintf formatter "(@[forall ((";
      SrkUtil.pp_print_enum
        ~pp_sep:(fun f () -> fprintf f " Int) (")
        pp_print_string
        formatter
        (BatArray.enum var_names);
      fprintf formatter " Int))@ %a@])" (format env') phi'

    | Exists (x, phi) ->
      let (hints, phi') = flatten_existential phi in
      let var_names = Array.of_list (List.map gensym (x::hints)) in
      let num_vars = Array.length var_names in
      let env' n =
        if n >= num_vars then env (n - num_vars)
        else var_names.(num_vars - n - 1)
      in
      fprintf formatter "(@[exists ((";
      SrkUtil.pp_print_enum
        ~pp_sep:(fun f () -> fprintf f " Int) (")
        pp_print_string
        formatter
        (BatArray.enum var_names);
      fprintf formatter " Int))@ %a@])" (format env') phi'

    | Eq (x, y) ->
      fprintf formatter "@[(= %a %a)@]" (pp_term env) x (pp_term env) y
    | Neq (x, y) ->
      fprintf formatter "@[(not (= %a %a))@]" (pp_term env) x (pp_term env) y
    | Atom (rel, []) -> pp_rel formatter rel
    | Atom (rel, params) ->
      fprintf formatter "@[(%a %a)@]"
        pp_rel rel
        (pp_print_list ~pp_sep:pp_print_space (pp_term env)) params
    | True -> pp_print_string formatter "true"
    | False -> pp_print_string formatter "false"
  in
  let undef x =
    invalid_arg "format_smtlib2: input must be a sentence"
  in
  format undef formatter phi

let atom_substitute sigma phi =
  let f depth = function
    | `Atom (head, args) ->
      let rhs = sigma head (List.length args) in
      let subs n =
        try List.nth args n
        with Invalid_argument _ -> invalid_arg "atom_substitute"
      in
      var_substitute subs rhs
    | `Eq (x, y) -> mk_eq x y
    | `Neq (x, y) -> mk_neq x y
  in
  map_with_depth f phi

let alpha_equiv phi psi =
  let forget_hints = function
    | `Forall (_, phi) -> Forall (None, phi)
    | `Exists (_, phi) -> Exists (None, phi)
    | phi -> construct phi
  in
  (eval forget_hints phi) = (eval forget_hints psi)

let rec instantiate_quantifiers ?env:(env=[]) phi constants =
  let term_val = function
    | Const k -> Const k
    | Var i ->
      try Const (List.nth env i)
      with Invalid_argument _ ->
        invalid_arg "instantiate_quantifiers: unbound variable"
  in
  match destruct phi with
  | `T -> mk_true
  | `F -> mk_false
  | `And (phi, psi) ->
    mk_and
      (instantiate_quantifiers ~env:env phi constants)
      (instantiate_quantifiers ~env:env psi constants)
  | `Or (phi, psi) ->
    mk_or
      (instantiate_quantifiers ~env:env phi constants)
      (instantiate_quantifiers ~env:env psi constants)
  | `Atom (p, args) ->
    mk_atom p (List.map term_val args)
  | `Forall (_, phi) ->
    BatList.enum constants
    /@ (fun k -> instantiate_quantifiers ~env:(k::env) phi constants)
    |> big_conj
  | `Exists (_, phi) ->
    BatList.enum constants
    /@ (fun k -> instantiate_quantifiers ~env:(k::env) phi constants)
    |> big_disj
  | `Eq (x, y) -> mk_eq (term_val x) (term_val y)
  | `Neq (x, y) -> mk_neq (term_val x) (term_val y)

let simplify phi =
  let alg = function
    | `And (phi, psi) -> mk_and phi psi
    | `Or (phi, psi) -> mk_or phi psi
    | `Eq (Const x, Const y) ->
      if x = y then mk_true
      else mk_false
    | `Eq (x, y) -> mk_eq x y
    | `Neq (Const x, Const y) ->
      if x = y then mk_false
      else mk_true
    | `Neq (x, y) -> mk_neq x y
    | `Atom (rel, params) -> mk_atom rel params
    | `T -> mk_true
    | `F -> mk_false
    | `Exists (hint, phi) -> Exists (hint, phi)
    | `Forall (hint, phi) -> Forall (hint, phi)
  in
  eval alg phi
