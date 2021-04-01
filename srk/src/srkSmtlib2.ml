open SrkSmtlib2Defs

let rec pp_list ?(sep=" ") pp formatter = function
  | [] -> ()
  | [x] -> Format.fprintf formatter "%a" pp x
  | x :: l -> Format.fprintf formatter "%a%s%a" pp x sep (pp_list ~sep pp) l

let pp_constant formatter = function
  | Int zz -> Format.fprintf formatter "%a" ZZ.pp zz
  | Real qq -> Format.fprintf formatter "%a" QQ.pp qq
  | String str -> Format.fprintf formatter "%s" str

let pp_symbol = Format.pp_print_string

let pp_index formatter = function
  | Num zz -> Format.fprintf formatter "%a" ZZ.pp zz
  | Sym sym -> Format.fprintf formatter "%a" pp_symbol sym

let pp_identifier formatter = function
  | (sym, []) -> Format.fprintf formatter "%a" pp_symbol sym
  | (sym, il) -> Format.fprintf formatter "(_ %a %a)" pp_symbol sym (pp_list pp_index) il

let rec pp_sort formatter = function
  | Sort (id, []) -> Format.fprintf formatter "%a" pp_identifier id
  | Sort (id, sl) -> Format.fprintf formatter "(%a %a)" pp_identifier id (pp_list pp_sort) sl

let pp_qual_id formatter = function
  | (id, None) -> Format.fprintf formatter "%a" pp_identifier id
  | (id, Some s) -> Format.fprintf formatter "(as %a %a)" pp_identifier id pp_sort s

let pp_pattern formatter = function
  | (sym, []) -> Format.fprintf formatter "%a" pp_symbol sym
  | (sym, syms) -> Format.fprintf formatter "(%a %a)" pp_symbol sym (pp_list pp_symbol) syms

let rec pp_sexpr formatter = function
  | SConst c -> Format.fprintf formatter "%a" pp_constant c
  | SSym sym -> Format.fprintf formatter "%a" pp_symbol sym
  | SKey kw -> Format.fprintf formatter ":%a" pp_symbol kw
  | SSexpr sexprs -> Format.fprintf formatter "(%a)" (pp_list pp_sexpr) sexprs

let pp_attribute_value formatter = function
  | VConst c -> Format.fprintf formatter "%a" pp_constant c
  | VSym sym -> Format.fprintf formatter "%a" pp_symbol sym
  | VSexpr sexprs -> Format.fprintf formatter "(%a)" (pp_list pp_sexpr) sexprs

let pp_attribute formatter = function
  | (kw, None) -> Format.fprintf formatter ":%a" pp_symbol kw
  | (kw, Some v) -> Format.fprintf formatter ":%a %a" pp_symbol kw pp_attribute_value v

let rec pp_term formatter = function
  | Const c -> Format.fprintf formatter "%a" pp_constant c
  | App (id, []) -> Format.fprintf formatter "%a" pp_qual_id id
  | App (id, tl) -> Format.fprintf formatter "(%a %a)" pp_qual_id id (pp_list pp_term) tl
  | Let (vbl, t) -> Format.fprintf formatter "(let (%a) %a)" (pp_list pp_var_binding) vbl pp_term t
  | Forall (svl, t) -> Format.fprintf formatter "(forall (%a) %a)" (pp_list pp_sorted_var) svl pp_term t
  | Exists (svl, t) -> Format.fprintf formatter "(exists (%a) %a)" (pp_list pp_sorted_var) svl pp_term t
  | Match (t, cases) -> Format.fprintf formatter "(match %a (%a))" pp_term t (pp_list pp_match_case) cases
  | Attribute (t, attrs) -> Format.fprintf formatter "(! %a %a)" pp_term t (pp_list pp_attribute) attrs
and pp_var_binding formatter (sym, t) =
  Format.fprintf formatter "(%a %a)" pp_symbol sym pp_term t
and pp_sorted_var formatter (sym, s) =
  Format.fprintf formatter "(%a %a)" pp_symbol sym pp_sort s
and pp_match_case formatter (p, t) =
  Format.fprintf formatter "(%a %a)" pp_pattern p pp_term t

let pp_model formatter model =
  let pp_fn_def formatter (sym, svl, s, t) =
    Format.fprintf formatter "(define-fun %a (%a) %a %a)" pp_symbol sym (pp_list pp_sorted_var) svl pp_sort s pp_term t
  in
  Format.fprintf formatter "(%a)" (pp_list pp_fn_def) model

let file_parse_term file_name =
  let open Lexing in
  let file_in = Stdlib.open_in file_name in
  let lexbuf = Lexing.from_channel file_in in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = file_name };
  try
    let term = SrkSmtlib2Parse.main_term SrkSmtlib2Lex.token lexbuf in
    Stdlib.close_in file_in;
    term
  with
  | SrkSmtlib2Parse.Error ->
    let open Lexing in
    let pos = lexbuf.lex_curr_p in
    failwith(Printf.sprintf "Parse error: %s:%d:%d" file_name pos.pos_lnum (pos.pos_cnum-pos.pos_bol+1))

let string_parse_term str  =
  let lexbuf = Lexing.from_string str in
  try SrkSmtlib2Parse.main_term SrkSmtlib2Lex.token lexbuf with
  | SrkSmtlib2Parse.Error -> invalid_arg (Printf.sprintf "Parse error: %s" str)

let file_parse_model file_name =
  let open Lexing in
  let file_in = Stdlib.open_in file_name in
  let lexbuf = Lexing.from_channel file_in in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = file_name };
  try
    let model = SrkSmtlib2Parse.main_model SrkSmtlib2Lex.token lexbuf in
    Stdlib.close_in file_in;
    model
  with
  | SrkSmtlib2Parse.Error ->
    let open Lexing in
    let pos = lexbuf.lex_curr_p in
    failwith(Printf.sprintf "Parse error: %s:%d:%d" file_name pos.pos_lnum (pos.pos_cnum-pos.pos_bol+1))

let string_parse_model str  =
  let lexbuf = Lexing.from_string str in
  try SrkSmtlib2Parse.main_model SrkSmtlib2Lex.token lexbuf with
  | SrkSmtlib2Parse.Error -> invalid_arg (Printf.sprintf "Parse error: %s" str)

let typ_of_sort s =
  let typ_fo_of str =
    match str with
    | "Bool" -> `TyBool
    | "Int" -> `TyInt
    | "Real" -> `TyReal
    | _ -> invalid_arg "Unsupported type"
  in
  match s with
  | Sort((typ, []), args) ->
    let args =
      List.map (fun s ->
        match s with
        | Sort((typ, []), []) -> typ_fo_of typ
        | _ -> invalid_arg "Unsupported type"
      ) args
    in
    let typ_out = typ_fo_of typ in
    if args = [] then typ_out else `TyFun (args, typ_out)
  | _ -> invalid_arg "Unsupported type"

module MakeSMT2Srk(C : sig type t val context : t Syntax.context end) = struct

  let srk = C.context

  type 'a gexpr = ('a, Syntax.typ_fo) Syntax.expr
  let rec expr_of_smt of_symbol t =
    let formula_of = formula_of_smt of_symbol in
    let term_of = term_of_smt of_symbol in
    let left_assoc f init args = List.fold_left f init args in
    let chain f init args =
      let rec go acc x = function
        | [] -> acc
        | y :: rest -> go (f x y acc) y rest
      in go init (List.hd args) (List.tl args)
    in
    let pair_wise f init args =
      let rec go acc = function
        | [] -> acc
        | x :: rest -> go (List.fold_left (fun acc y -> (f x y acc)) acc rest) rest
      in go init args
    in
    let open Syntax in
    match t with
    | Const (Int zz) -> (mk_zz srk zz :> 'a gexpr)
    | Const (Real qq) -> (mk_real srk qq :> 'a gexpr)
    | Const (String _) -> invalid_arg "String constants not supported by SRK"
    | App (((sym, []), None), terms) ->
      begin match sym with
      | "true" -> assert (terms = []); (mk_true srk :> 'a gexpr)
      | "false" -> assert (terms = []); (mk_false srk :> 'a gexpr)
      | "not" ->
        begin match terms with
        | [t] -> (mk_not srk (formula_of t) :> 'a gexpr)
        | _ -> assert false
        end
      | "and" ->
        begin match terms with
        | [] -> assert false
        | [t] -> (formula_of t :> 'a gexpr)
        | _ -> (mk_and srk (List.map formula_of terms) :> 'a gexpr)
        end
      | "or" ->
        begin match terms with
        | [] -> assert false
        | [t] -> (formula_of t :> 'a gexpr)
        | _ -> (mk_or srk (List.map formula_of terms) :> 'a gexpr)
        end
      | "xor" -> (* left associative *)
        begin match terms with
        | [] -> assert false
        | _ ->
          let phis = List.map formula_of terms in
          let f res phi = mk_and srk [mk_or srk [phi; res]; mk_not srk (mk_and srk [phi; res])] in (* phi xor res *)
          (left_assoc f (List.hd phis) (List.tl phis) :> 'a gexpr)
        end
      | "=>" -> (* Right associative *)
        begin match terms with
        | [] -> assert false
        | _ ->
          let phis = List.rev_map formula_of terms in
          let f res phi = mk_or srk [mk_not srk phi; res] in (* phi => res *)
          (left_assoc f (List.hd phis) (List.tl phis) :> 'a gexpr)
        end
      | "=" -> (* chaining *)
         begin match terms with
         | [] -> assert false
         | _ :: [] -> assert false
         | _ ->
           let terms = List.map term_of terms in
           let f x y phis = (mk_eq srk x y) :: phis in
           (mk_and srk (chain f [] terms) :> 'a gexpr)
         end
      | "distinct" -> (* pairwise != *)
        begin match terms with
        | [] -> assert false
        | _ ->
          let terms = List.map term_of terms in
          let f x y phis = (mk_not srk (mk_eq srk x y)) :: phis in
          (mk_and srk (pair_wise f [] terms) :> 'a gexpr)
        end
      | "ite" ->
        begin match terms with
        | [b; x; y] ->
          let bcond = formula_of b in
          let bthen = expr_of_smt of_symbol x in
          let belse = expr_of_smt of_symbol y in
          (mk_ite srk bcond bthen belse)
        | _ -> assert false
        end
      | "+" ->
        begin match terms with
        | [] -> assert false
        | [t] -> (term_of t :> 'a gexpr)
        | _ -> (mk_add srk (List.map term_of terms) :> 'a gexpr)
        end
      | "-" -> (* neg or (sub left assoc) *)
        begin match terms with
        | [] -> assert false
        | [t] -> (mk_neg srk (term_of t) :> 'a gexpr)
        | _ ->
          let terms = List.map term_of terms in
          (left_assoc (mk_sub srk) (List.hd terms) (List.tl terms) :> 'a gexpr)
        end
      | "*" ->
        begin match terms with
        | [] -> assert false
        | [t] -> (term_of t :> 'a gexpr)
        | _ -> (mk_mul srk (List.map term_of terms) :> 'a gexpr)
        end
      | "mod" ->
        begin match terms with
        | [x; y] -> (mk_mod srk (term_of x) (term_of y) :> 'a gexpr)
        | _ -> assert false
        end
      | "div" ->
        begin match terms with
        | [x; y] -> (mk_idiv srk (term_of x) (term_of y) :> 'a gexpr)
        | _ -> assert false
        end
      | "abs" ->
        begin match terms with
        | [x] ->
          let x = term_of x in
          (mk_ite srk (mk_lt srk x (mk_int srk 0)) (mk_neg srk x) x :> 'a gexpr)
        | _ -> assert false
        end
      | "<" -> (* chainable *)
         begin match terms with
         | _ :: _ :: _ ->
           let terms = List.map term_of terms in
           let f x y phis = (mk_lt srk x y) :: phis in
           (mk_and srk (chain f [] terms) :> 'a gexpr)
         | _ -> assert false
         end
      | ">" ->
         begin match terms with
         | _ :: _ :: _ ->
           let terms = List.rev_map term_of terms in
           let f x y phis = (mk_lt srk x y) :: phis in
           (mk_and srk (chain f [] terms) :> 'a gexpr)
         | _ -> assert false
         end
      | "<=" ->
         begin match terms with
         | _ :: _ :: _ ->
           let terms = List.map term_of terms in
           let f x y phis = (mk_leq srk x y) :: phis in
           (mk_and srk (chain f [] terms) :> 'a gexpr)
         | _ -> assert false
         end
      | ">=" ->
         begin match terms with
         | _ :: _ :: _ ->
           let terms = List.rev_map term_of terms in
           let f x y phis = (mk_leq srk x y) :: phis in
           (mk_and srk (chain f [] terms) :> 'a gexpr)
         | _ -> assert false
         end
      | "/" ->
        begin match terms with
        | [x; y] -> (mk_div srk (term_of x) (term_of y) :> 'a gexpr)
        | _ -> assert false
        end
      | "to_real" -> (* maybe this should be unsupported rather than being a noop in srk *)
        begin match terms with
        | [t] -> (term_of t :> 'a gexpr)
        | _ -> assert false
        end
      | "to_int" ->
        begin match terms with
        | [t] -> (mk_floor srk (term_of t) :> 'a gexpr)
        | _ -> assert false
        end
      | "is_int" ->
        begin match terms with
        | [t] ->
          let t = term_of t in
          (mk_eq srk (mk_floor srk t) t :> 'a gexpr)
        | _ -> assert false
        end
      | srk_sym ->
        begin match terms with
        | [] ->
          let sym = of_symbol srk_sym in
          begin match typ_symbol srk sym with
          | `TyBool
          | `TyInt
          | `TyReal 
          | `TyArr -> (mk_const srk (of_symbol srk_sym) :> 'a gexpr)
          | `TyFun _ -> invalid_arg "Unexpected function symbol"
          end
        | _ ->
          let sym = of_symbol srk_sym in
          match typ_symbol srk sym with
          | `TyBool | `TyInt | `TyReal | `TyArr -> invalid_arg "Unexpected function application: Non-functional symbol"
          | `TyFun (args_typ, _) ->
            if (List.length terms) != (List.length args_typ) then invalid_arg "Unexpected function application: arity mistmatch" else
            let args =
              List.map2 (fun term typ ->
                match typ with
                | `TyBool -> (formula_of term :> 'a gexpr)
                | _ -> (term_of term :> 'a gexpr)
              ) terms args_typ
            in
            (mk_app srk sym args :> 'a gexpr)
        end
      end
    | App ((("divisible", [Num n]), None), terms) ->
      begin match terms with
      | [t] ->
        let t = term_of t in
        let sym = mk_symbol srk `TyInt in
        let n = mk_zz srk n in
        (mk_exists_const srk sym (mk_eq srk t (mk_mul srk [n; mk_const srk sym])) :> 'a gexpr)
      | _ -> assert false
      end
  (*  | Let (bindings, t) -> invalid_arg "Unsupported"
    | Forall (vars, t) -> invalid_arg "Unsupported"
    | Exists (vars, t) -> invalid_arg "Unsupported" *)
    | App _ -> invalid_arg "Unknown function name"
    | _ -> invalid_arg "Match and attribute statments are not supported"
  and term_of_smt of_symbol t =
    match Syntax.Expr.refine srk (expr_of_smt of_symbol t) with
    | `Term t -> t
    | _ -> invalid_arg "Term expected"
  and formula_of_smt of_symbol t =
    match Syntax.Expr.refine srk (expr_of_smt of_symbol t) with
    | `Formula phi -> phi
    | _ -> invalid_arg "Formula expected"

  type symbol_pool = {
    new_symbol : Syntax.typ -> Syntax.symbol;
    reset : unit -> unit
  }

  (* pool of symbols for each base type: avoids possible memory leak *)
  let formals_pool : symbol_pool =
    let module DA = BatDynArray in
    let int_symbols = DA.create () in
    let int_id = ref (-1) in
    let real_symbols = DA.create () in
    let real_id = ref (-1) in
    let bool_symbols = DA.create () in
    let bool_id = ref (-1) in
    let new_symbol typ =
      let open Syntax in
      match typ with
      | `TyInt -> incr int_id;
        if (!int_id) < (DA.length int_symbols) then DA.get int_symbols (!int_id) else
        begin let sym = mk_symbol srk typ in DA.add int_symbols sym; sym end
      | `TyReal -> incr real_id;
        if (!real_id) < (DA.length real_symbols) then DA.get real_symbols (!int_id) else
        begin let sym = mk_symbol srk typ in DA.add real_symbols sym; sym end
      | `TyBool -> incr bool_id;
        if (!bool_id) < (DA.length bool_symbols) then DA.get bool_symbols (!int_id) else
        begin let sym = mk_symbol srk typ in DA.add bool_symbols sym; sym end
      | _ -> assert false
    in
    let reset _ =
      int_id := -1;
      real_id := -1;
      bool_id := -1
    in
    { new_symbol; reset }

  (* functions are debruijn indexed *)
  let model_of_smt of_symbol (m : model) =
    let open Syntax in
    let term_of_smt of_sym t = term_of_smt of_sym t in
    let formula_of_smt of_sym phi = formula_of_smt of_sym phi in
    List.map (fun (sym, formals, ret_typ, def) ->
      let sym = of_symbol sym in
      let value =
        match (typ_symbol srk sym), (typ_of_sort ret_typ) with
        | `TyBool, `TyBool ->
          assert (formals = []);
          begin match Formula.destruct srk (formula_of_smt of_symbol def) with
          | `Tru -> `Bool true
          | `Fls -> `Bool false
          | _ -> invalid_arg "Mismatch between model and symbol definitions 1"
          end
        | `TyInt, `TyInt
        | `TyReal, `TyReal ->
          assert (formals = []);
          begin match Term.destruct srk (term_of_smt of_symbol def) with
          | `Real qq -> `Real qq
          | _ -> invalid_arg "Mismatch between model and symbol definitions 2"
          end
        | `TyFun (args, `TyInt), `TyInt
        | `TyFun (args, `TyReal), `TyReal
        | `TyFun (args, `TyBool), `TyBool ->
          let rename_var = Hashtbl.create 991 in
          let var_rename = Hashtbl.create 991 in
          List.iteri (fun i (typ, (arg, sort)) ->
            let (sym, var) =
              match typ, typ_of_sort sort with
              | `TyBool, `TyBool -> (formals_pool.new_symbol `TyBool, mk_var srk i `TyBool)
              | `TyInt, `TyInt -> (formals_pool.new_symbol `TyInt, mk_var srk i `TyInt)
              | `TyReal, `TyReal -> (formals_pool.new_symbol `TyReal, mk_var srk i `TyReal)
              | _ -> invalid_arg "Type Mismatch"
            in
            Hashtbl.add rename_var arg sym;
            Hashtbl.add var_rename sym var
          ) (List.combine args formals);
          let of_symbol sym =
            match Hashtbl.find_opt rename_var sym with
            | Some sym -> sym
            | None -> of_symbol sym
          in
          let def =
            match (typ_symbol srk sym) with
            | `TyFun (_, `TyBool) -> (formula_of_smt of_symbol def :> 'a gexpr)
            | _ -> (term_of_smt of_symbol def :> 'a gexpr)
          in
          let res =
            substitute_const srk (fun sym ->
              match Hashtbl.find_opt var_rename sym with
              | Some v -> v
              | None -> mk_const srk sym
            ) def
          in
          formals_pool.reset ();
          `Fun res
        | _ -> invalid_arg "Mismatch between model and symbol definitions 3"
      in
      (sym, value)
    ) m

end
