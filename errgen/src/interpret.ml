open Ast
open Apak
open Ark
open ArkPervasives

exception NotHandled of string

(******* Printing a program *****************
*********************************************)

let eps_mach = Real_const (QQ.exp (QQ.of_int 2) (-53))
let neg_eps_mach = Real_const (QQ.negate (QQ.exp (QQ.of_int 2) (-53)))
let max_float = Real_const (QQ.exp (QQ.of_int 2) 53)
let min_float = Real_const (QQ.negate (QQ.exp (QQ.of_int 2) 53))

let print_prog (Prog s) =
  print_string "Printing program:\n\n";
  print_string (stmt_to_string s);
  print_string "\n"


(******* Interpreter for programs **********
*********************************************)

(* Store type *)

type env_type = (string * float) list

(* Auxiliary function *)

(* Works even if list doesn't contain binding for var *)
let update_store store var value =
  (var, value)::(List.remove_assoc var store)

exception AssertionViolation

(* Interpreter for arithmetic expressions *)

let rec interpret_aexp e store =
  match e with
    Real_const r -> r
  | Var_exp x ->
    List.assoc x store
  | Mult_exp (e1, e2) ->
    QQ.mul (interpret_aexp e1 store) (interpret_aexp e2 store)
  | Sum_exp (e1, e2) ->
    QQ.add (interpret_aexp e1 store) (interpret_aexp e2 store)
  | Diff_exp (e1, e2) ->
    QQ.sub (interpret_aexp e1 store) (interpret_aexp e2 store)
  | Unneg_exp (e1) -> QQ.negate (interpret_aexp e1 store)
  | _ -> raise (NotHandled ("Arithmetic interpretation for expression "
			    ^ aexp_to_string e))


(* Interpreter for boolean expressions *)

let rec interpret_bexp b store =
  match b with
  | Bool_const (bc) -> bc
  | Gt_exp (e1, e2) ->
      (interpret_aexp e1 store) > (interpret_aexp e2 store)
  | Lt_exp (e1, e2) ->
    (interpret_aexp e1 store) < (interpret_aexp e2 store)
  | Ge_exp (e1, e2) ->
      (interpret_aexp e1 store) >= (interpret_aexp e2 store)
  | Le_exp (e1, e2) ->
    (interpret_aexp e1 store) <= (interpret_aexp e2 store)
  | Eq_exp (e1, e2) ->
    (interpret_aexp e1 store) == (interpret_aexp e2 store)
  | Ne_exp (e1, e2) ->
    (interpret_aexp e1 store) != (interpret_aexp e2 store)
  | And_exp (b1, b2) ->
    (interpret_bexp b1 store) && (interpret_bexp b2 store)
  | Not_exp b1  ->
    not (interpret_bexp b1 store)
  | Or_exp (b1, b2) ->
    (interpret_bexp b1 store) || (interpret_bexp b2 store)
  | _ -> raise (NotHandled ("Boolean interpretation for expression "
			    ^ bexp_to_string b))


(* Interpreter for statements *)

let rec interpret_stmt s store =
  match s with
     Skip -> store
  |  Assign (var, e) -> (update_store store var (interpret_aexp e store))
  | Seq (s1, s2) -> (interpret_stmt s2 (interpret_stmt s1 store))
  | Ite (b, s1, s2) ->
    let bv = interpret_bexp b store in
    if bv then (interpret_stmt s1 store)
    else (interpret_stmt s2 store)
  | While (b, s1, _) ->
    let bv = interpret_bexp b store in
    if bv then (interpret_stmt s (interpret_stmt s1 store))
    else store
  | Assert b ->
    if (interpret_bexp b store)
    then store
    else raise AssertionViolation
  | Print e ->
    (print_string (QQ.show (interpret_aexp e store)));
    (print_string "\n");
    store
  | _ -> raise (NotHandled ("Statement inrepretation of " ^ stmt_to_string s))

let interpret_prog p =
  (print_string "Interpreting program:\n\n");
  (ignore (match p with
    Prog s -> interpret_stmt s []));
  (print_string "\n")


(********** Generating the error program *************
*************************************************)

let freshvartracker = ref 0

let freshvar () =
  let z = !freshvartracker
  in
  freshvartracker := z + 1;
  (String.concat "" ["__";string_of_int z])

(* Substituting variables with other variables *)

let primify x =
  String.concat "" [x;"\'"]

let epsify x =
  String.concat "" ["eps_"; x]

let infify x =
  String.concat "" ["inf_"; x]

let rec primify_aexp e =
  match e with
    Real_const m -> e
  | Sum_exp (e1, e2) -> Sum_exp (primify_aexp e1, primify_aexp e2)
  | Diff_exp (e1, e2) -> Diff_exp (primify_aexp e1, primify_aexp e2)
  | Mult_exp (e1, e2) -> Mult_exp (primify_aexp e1, primify_aexp e2)
  | Var_exp x -> Var_exp (primify x)
  | Unneg_exp e1 -> Unneg_exp (primify_aexp e1)
  | Havoc_aexp -> e
and
primify_aexp_list lst =
  match lst with
    [] -> []
  | head :: rest ->
    (primify_aexp head) :: (primify_aexp_list rest)


let rec primify_bexp b =
  match b with
    Bool_const bc -> b
  | Eq_exp (e1, e2) -> Eq_exp (primify_aexp e1, primify_aexp e2)
  | Ne_exp (e1, e2) -> Ne_exp (primify_aexp e1, primify_aexp e2)
  | Gt_exp (e1, e2) -> Gt_exp (primify_aexp e1, primify_aexp e2)
  | Lt_exp (e1, e2) -> Lt_exp (primify_aexp e1, primify_aexp e2)
  | Le_exp (e1, e2) -> Le_exp (primify_aexp e1, primify_aexp e2)
  | Ge_exp (e1, e2) -> Ge_exp (primify_aexp e1, primify_aexp e2)
  | And_exp (b1, b2) -> And_exp (primify_bexp b1, primify_bexp b2)
  | Or_exp (b1, b2) -> Or_exp (primify_bexp b1, primify_bexp b2)
  | Not_exp b1 -> Not_exp (primify_bexp b1)
  | Havoc_bexp -> b


let rec primify_stmt s =
  match s with
    Skip -> Skip
  | Assign (x, e) -> Assign(primify x, primify_aexp e)
  | Seq (s1, s2) -> Seq (primify_stmt s1, primify_stmt s2)
  | Ite (b, s1, s2) -> Ite (primify_bexp b, primify_stmt s1, primify_stmt s2)
  | While (b, s1, residual) -> While (primify_bexp b, primify_stmt s1, residual)
  | Assert (b) -> Assert (primify_bexp b)
  | Print (e) -> Print (primify_aexp e)
  | Assume (b) -> Assume (primify_bexp b)

(* Residue computation *)

(* Mark all loops as residual *)
let rec mk_residue = function
  | Seq (x, y) -> Seq (mk_residue x, mk_residue y)
  | Ite (b, x, y) -> Ite (b, mk_residue x, mk_residue y)
  | While (b, s, _) -> While (b, mk_residue s, true)
  | atom -> atom

let rec compute_residue_aux_1 vars =
  match vars with
    [] -> Skip
  | x :: rest ->
    Seq (Assign (primify x, Var_exp x),
         Seq (Assign (infify (epsify (primify x)), Var_exp (infify (epsify x))),
              Seq (Assign (epsify (primify x), Var_exp (epsify x)),
                   (compute_residue_aux_1 rest))))


let rec  compute_residue_aux_2 vars =
  match vars with
    [] -> Skip
  | x :: rest ->
    Seq(
      Seq (Assign (epsify x, Sum_exp(Var_exp (epsify (primify x)), Diff_exp(Var_exp(primify x), (Var_exp x)))),
           Assign (infify (epsify x), Var_exp (infify (epsify (primify x))))),
           (compute_residue_aux_2 rest))

let compute_residue s1 s2 vars =
  mk_residue
    (Seq (compute_residue_aux_1 vars,
	  Seq (s1,
               Seq(primify_stmt s2,
                   compute_residue_aux_2 vars))))

(* Error term generation *)

type optype = Plus
          | Minus
          | Times

let generate_err_assign_aux x e e1 e2 op =
  let opfunc =
    function (arg1, arg2) ->
      match op with
        Plus -> Sum_exp (arg1, arg2)
      | Minus -> Diff_exp (arg1, arg2)
      | Times -> Mult_exp (arg1, arg2)
  in
  match (e1, e2) with
    (Var_exp y1, Var_exp y2) ->
      let t = (freshvar ()) in
      let s1 = Assign (t,
                       opfunc (Sum_exp (e1, Var_exp (epsify y1)),
                               Sum_exp (e2, Var_exp (epsify y2)))) in
      (* If we have uninterpreted function symbols, we should replace the variable __round_err by one *)
      let t_err = t ^ "__round_err" in
      let s_err_stmts =
        Seq (
         Assign (t_err, Havoc_aexp),
         Ite (
          Ge_exp(Var_exp t, Real_const QQ.zero),
            Assume (And_exp(Ge_exp (Var_exp (t_err),
				    Mult_exp (Var_exp t, neg_eps_mach)),
                            Le_exp (Var_exp (t_err),
				    Mult_exp (Var_exp t, eps_mach)))),
            Assume (And_exp(Le_exp (Var_exp (t_err),
				    Mult_exp (Var_exp t, neg_eps_mach)),
                           (Ge_exp (Var_exp (t_err),
				    Mult_exp (Var_exp t, eps_mach)))))))

      in
      let tmp1 = Sum_exp (Var_exp t, Var_exp t_err) in
      let s2 =
	Ite (And_exp (Ge_exp (tmp1, min_float),
		      Le_exp (tmp1, max_float)),
             Assign (epsify x, Diff_exp (tmp1, opfunc (e1, e2))),
             Assign (infify (epsify x), Real_const QQ.one))
      in
      Seq (s1, Seq (s_err_stmts, Seq (s2, Assign (x, e))))
  | _ ->
      raise (NotHandled ("Expression in assignment not handled in error term generation: " ^ (aexp_to_string e)))



let generate_err_assign x e =
  match e with
    Real_const k ->
      (* eps_x = havoc(); inf_eps_x = 0; assume (eps_x >= k * eps_mach * -1 && eps_x <= k * eps_mach); *)
      if QQ.geq k QQ.zero then
        Seq (
          Seq (
            Seq (Assign (epsify x, Havoc_aexp),
                 Assign (infify (epsify x), Real_const QQ.zero)),
                 Assume (And_exp (Ge_exp (Var_exp (epsify x),
					  Mult_exp (e, neg_eps_mach)),
                                  Le_exp (Var_exp (epsify x),
					  Mult_exp (e, eps_mach))))),
                 Assign (x, e))
      else
        Seq (
          Seq (
            Seq (Assign (epsify x, Havoc_aexp),
                 Assign (infify (epsify x), Real_const QQ.zero)),
            Assume (And_exp (Le_exp (Var_exp (epsify x),
				     Mult_exp (e, neg_eps_mach)),
                             Ge_exp (Var_exp (epsify x),
				     Mult_exp (e, eps_mach))))),
          Assign (x, e))
  | Var_exp y ->
    Seq (
      Seq (Assign (infify (epsify x), Var_exp (infify (epsify y))), 
           Assign (epsify x, Var_exp (epsify y))),
      Assign (x, e))
  | Sum_exp (e1, e2) ->
    (generate_err_assign_aux x e e1 e2 Plus)
  | Diff_exp (e1, e2) ->
    (generate_err_assign_aux x e e1 e2 Minus)
  | Mult_exp (e1, e2) ->
    (generate_err_assign_aux x e e1 e2 Times)
  | _ -> raise (NotHandled ("Assignment not handled in error term generation: " ^ (aexp_to_string e)))


type boptype = Eq
          | Neq
          | Ge
          | Le
          | Gt
          | Lt


let generate_err_bexp_aux e1 e2 op =
  let opfunc =
    function (arg1, arg2) ->
      match op with
        Eq -> Eq_exp (arg1, arg2)
      | Neq -> Ne_exp (arg1, arg2)
      | Ge -> Ge_exp (arg1, arg2)
      | Le -> Le_exp (arg1, arg2)
      | Gt -> Gt_exp (arg1, arg2)
      | Lt -> Lt_exp (arg1, arg2)
  in
  match (e1, e2) with
    (Var_exp y1, Var_exp y2) ->
      let b1 =
        And_exp
          (Havoc_bexp,
           Or_exp
             (Ge_exp (Var_exp (infify (epsify y1)), Real_const QQ.one),
              Ge_exp (Var_exp (infify (epsify y2)), Real_const QQ.one)))
      in
      let b2 =
        And_exp
          (Lt_exp (Var_exp (infify (epsify y1)), Real_const QQ.one),
           Lt_exp (Var_exp (infify (epsify y2)), Real_const QQ.one))
      in
      let b3 =
        opfunc (e1, e2)
      in
      let b4 = opfunc (Sum_exp (e1, Var_exp (epsify y1)),
                       Sum_exp (e2, Var_exp (epsify y2))) in
      Or_exp (b1,
               And_exp (b2, Or_exp (And_exp (b3, b4),
                                    And_exp (Not_exp b3, Not_exp b4))))
  | _ -> raise (NotHandled ("Bool expression not handled in error term generation: " ^ bexp_to_string (opfunc (e1, e2))))

let generate_err_bexp b =
  match b with
    Bool_const bc -> b
  | Eq_exp (e1, e2) -> (generate_err_bexp_aux e1 e2 Eq)
  | Ne_exp (e1, e2) -> (generate_err_bexp_aux e1 e2 Neq)
  | Ge_exp (e1, e2) -> (generate_err_bexp_aux e1 e2 Ge)
  | Le_exp (e1, e2) -> (generate_err_bexp_aux e1 e2 Le)
  | Gt_exp (e1, e2) -> (generate_err_bexp_aux e1 e2 Gt)
  | Lt_exp (e1, e2) -> (generate_err_bexp_aux e1 e2 Lt)
  | _ -> raise (NotHandled ("Error computation for bool expression " ^ (bexp_to_string b)))


let rec generate_err_stmt s0 vars =
  match s0 with
    Skip -> Skip
  | Assign (var, e) ->
    (generate_err_assign var e)
  | Seq (s1, s2) ->
    Seq ((generate_err_stmt s1 vars), (generate_err_stmt s2 vars))
  | Ite (b, s1, s2) ->
    Ite (And_exp (b, generate_err_bexp b),
         (generate_err_stmt s1 vars),
         (Ite (And_exp ((Not_exp b), (generate_err_bexp b)),
               (generate_err_stmt s2 vars),
               (Ite (And_exp (b, Not_exp (generate_err_bexp b)),
                     (compute_residue s1 (generate_err_stmt s2 vars) vars),
                     (compute_residue s2 (generate_err_stmt s1 vars) vars))))))
  | While (b, s, residue) ->
    Seq (While (And_exp(b, generate_err_bexp b),
                generate_err_stmt s vars,
		residue),
         Ite (b,
              (compute_residue s0 Skip vars),
              (compute_residue
                 Skip
                 (While(Or_exp (And_exp (b, (generate_err_bexp b)),
                                And_exp (Not_exp b, Not_exp (generate_err_bexp b))),
                        (generate_err_stmt s vars),
			true))
		 vars)))
  | Assume b -> Assume b
  | _ -> raise (NotHandled ("Error computation for statement " ^ (stmt_to_string s0)))

(* Reformat program to not use nested arithmetic expressions, and use 
   temporary variables instead *)
let rec simplify_aexp e = 
  match e with
    Real_const _
  | Var_exp _
  | Havoc_aexp -> (Skip, e)
  | Sum_exp (e1, e2) ->
    let (prep1, e1') = simplify_aexp e1 in
    let (prep2, e2') = simplify_aexp e2 in
    let t = (freshvar ()) in
    ((Seq (prep1, Seq (prep2, Assign (t, Sum_exp (e1', e2'))))), Var_exp t)
  | Diff_exp (e1, e2) ->
    let (prep1, e1') = simplify_aexp e1 in
    let (prep2, e2') = simplify_aexp e2 in
    let t = (freshvar ()) in
    ((Seq (prep1, Seq (prep2, Assign (t, Diff_exp (e1', e2'))))), Var_exp t)
  | Mult_exp (e1, e2) ->
    let (prep1, e1') = simplify_aexp e1 in
    let (prep2, e2') = simplify_aexp e2 in
    let t = (freshvar ()) in
    ((Seq (prep1, Seq (prep2, Assign (t, Mult_exp (e1', e2'))))), Var_exp t)
  | Unneg_exp e1 ->
    let (prep1, e1') = simplify_aexp e1 in
    let t = (freshvar ()) in
    ((Seq (prep1, Assign (t, e1'))), Var_exp t)

let rec simplify_aexp_bexp b =  
  match b with
    Bool_const bc -> (Skip, b)
  | Eq_exp (e1, e2) -> 
    let (prep1, e1') = simplify_aexp e1 in
    let (prep2, e2') = simplify_aexp e2 in
    (Seq (prep1, prep2), Eq_exp (e1', e2'))
  | Ne_exp (e1, e2) -> 
    let (prep1, e1') = simplify_aexp e1 in
    let (prep2, e2') = simplify_aexp e2 in
    (Seq (prep1, prep2), Ne_exp (e1', e2'))
  | Ge_exp (e1, e2) -> 
    let (prep1, e1') = simplify_aexp e1 in
    let (prep2, e2') = simplify_aexp e2 in
    (Seq (prep1, prep2), Ge_exp (e1', e2'))
  | Gt_exp (e1, e2) -> 
    let (prep1, e1') = simplify_aexp e1 in
    let (prep2, e2') = simplify_aexp e2 in
    (Seq (prep1, prep2), Gt_exp (e1', e2'))
  | Le_exp (e1, e2) -> 
    let (prep1, e1') = simplify_aexp e1 in
    let (prep2, e2') = simplify_aexp e2 in
    (Seq (prep1, prep2), Le_exp (e1', e2'))
  | Lt_exp (e1, e2) -> 
    let (prep1, e1') = simplify_aexp e1 in
    let (prep2, e2') = simplify_aexp e2 in
    (Seq (prep1, prep2), Lt_exp (e1', e2'))
  | And_exp (e1, e2) -> 
    let (prep1, e1') = simplify_aexp_bexp e1 in
    let (prep2, e2') = simplify_aexp_bexp e2 in
    (Seq (prep1, prep2), And_exp (e1', e2'))
  | Or_exp (e1, e2) -> 
    let (prep1, e1') = simplify_aexp_bexp e1 in
    let (prep2, e2') = simplify_aexp_bexp e2 in
    (Seq (prep1, prep2), And_exp (e1', e2'))
  | Not_exp e1 -> 
    let (prep1, e1') = simplify_aexp_bexp e1 in
    (prep1, Not_exp e1)
  | Havoc_bexp -> (Skip, Havoc_bexp)

let rec simplify_aexp_prog s0 =
  match s0 with
    Skip -> Skip
  | Assign (var, e) ->
    let (prep, e') = simplify_aexp e in
    Seq (prep, Assign(var, e'))
  | Seq (s1, s2) ->
    Seq ((simplify_aexp_prog s1), (simplify_aexp_prog s2))
  | Ite (b, s1, s2) ->
    let s1' = simplify_aexp_prog s1 in
    let s2' = simplify_aexp_prog s2 in
    let (prep, b') = simplify_aexp_bexp b in
    Seq (prep, Ite (b', s1', s2'))
  | While (b, s, residual) ->
    let s' = simplify_aexp_prog s in
    let (prep, b') =  simplify_aexp_bexp b in
    Seq (prep, While(b', s', residual))
  | Assert b -> 
    let (prep, b') = simplify_aexp_bexp b in
    Seq (prep, Assert(b'))
  | Assume b -> 
    let (prep, b') = simplify_aexp_bexp b in
    Seq (prep, Assume(b'))
  | _ -> s0

let simplify_prog p1 =
  match p1 with
    Prog s1 ->
      (Prog (simplify_aexp_prog s1))

(* Instrument a program with interval guesses for the epsilon variables at
   each loop header *)
let add_guesses stmt =
  let guess_lower = Real_const (QQ.negate QQ.one) in
  let guess_upper = Real_const QQ.one in
  let f guess err =
    And_exp (guess,
	     And_exp (Le_exp (guess_lower, Var_exp err),
		      Le_exp (Var_exp err, guess_upper)))
  in
  let mk_guess vars = Assert (List.fold_left f (Bool_const true) vars) in
  let rec go = function
    | Seq (x, y) -> Seq (go x, go y)
    | Ite (c, x, y) -> Ite (c, go x, go y)
    | While (c, body, _) ->
      let vars =
	List.filter (fun x -> BatString.starts_with x "eps") (collect_vars body)
      in
      While (c, Seq (mk_guess vars, go body), false)
    | atom -> atom
  in
  go stmt

let generate_err_prog p1 =
  match p1 with
    Prog s1 ->
      let vars = collect_vars s1 in
      (Prog (add_guesses (generate_err_stmt s1 vars)))

(********** Translation to input format of T2 *****
****************************************************)
let cnt = ref 0
let inc = function () ->
  ((cnt := !cnt + 1); !cnt)

(* Makes one assume for each conjunct. Increases T2 performance dramatically when used in combination with disjunctions. *)
let rec bexp_to_assume_list s =
  match s with
   | And_exp (c1, c2) -> (bexp_to_assume_list c1) ^ ";\n" ^ (bexp_to_assume_list c2)
   | _ -> stmt_to_string (Assume s)

let rec convert_cfg s =
  match s with
    Skip
  | Assign (_) ->
    let en = inc () in
    let ex = inc () in
    (en, ex, [(en, stmt_to_string s, ex)])
  | Seq (s1, s2) ->
    let (en1, ex1, t1) = convert_cfg s1 in
    let (en2, ex2, t2) = convert_cfg s2 in
    (en1, ex2, t1 @  [(ex1, stmt_to_string Skip, en2)] @ t2 )
  | Ite (b, s1, s2) ->
    let en = inc () in
    let ex = inc () in
    let (en1, ex1, t1) = convert_cfg s1 in
    let (en2, ex2, t2) = convert_cfg s2 in
    let newedges =
      [(en, stmt_to_string (Assume b), en1);
       (en, stmt_to_string (Assume (Not_exp b)), en2)]
      @ t1 @ t2 @
        [(ex1, stmt_to_string Skip, ex);
         (ex2, stmt_to_string Skip, ex)]
    in
    (en, ex, newedges)
  | While (b, s1, _) ->
    let en = inc () in
    let ex = inc () in
    let (en1, ex1, t1) = convert_cfg s1 in
    let loop_edges =
       match b with
        | Or_exp(b1, b2) -> [(en, bexp_to_assume_list b1, en1); (en, bexp_to_assume_list b2, en1)]
        | _ -> [(en, bexp_to_assume_list b, en1)]
    in
    let newedges =
      loop_edges @
       [(en, bexp_to_assume_list (Not_exp b), ex)]
      @ t1 @
       [(ex1, stmt_to_string Skip, en)]
    in
    (en, ex, newedges)
  | Assert (b)
  | Assume (b) ->
    let en = inc () in
    let ex = inc () in
    (en, ex, [(en, bexp_to_assume_list b, ex)])
  | _ -> raise (NotHandled ("T2 Translation of " ^ (stmt_to_string s)))


let rec transitions_T2_to_string tr =
  match tr with
    [] -> ""
  | (u, label, v) :: tail ->
    if label <> "skip" then
     String.concat ""
       ["FROM: "; string_of_int u; ";\n"; label; ";\n";
        "TO: "; string_of_int v; ";\n\n";
        transitions_T2_to_string tail]
    else
     String.concat ""
       ["FROM: "; string_of_int u; ";\n";
        "TO: "; string_of_int v; ";\n\n";
        transitions_T2_to_string tail]



let cfg_T2_to_string g =
  match g with
    (en, ex, edges) ->
      String.concat ""
       ["START: "; string_of_int en; ";\n\n"; transitions_T2_to_string edges]

let print_cfg_T2 g =
  print_string "\n\nPrinting program in T2 input format...\n\n";
  print_string (cfg_T2_to_string g)


let print_T2_prog p =
  match p with
    Prog s ->
      let g = convert_cfg s in
      (print_cfg_T2 g)


(*********** Main function ****************
*******************************************)


let read_and_process infile =
   let lexbuf  = Lexing.from_channel infile in
   let result = Parser.main Lexer.token lexbuf in
   print_prog result;
   print_T2_prog result;
   (print_string "\nSimplifying and printing program...\n\n");
   let simpprog = simplify_prog result in
   print_prog simpprog;
   (print_string "\nGenerating and printing error term...\n\n");
   (let errresult = generate_err_prog simpprog in
    Log.verbosity_level := 1;
    let errresult = Bounds.add_bounds errresult in
    print_prog errresult;
    print_T2_prog errresult
   )



let _ =
  if Array.length Sys.argv <> 2 then
    Printf.fprintf stderr "usage: %s input_filename\n" Sys.argv.(0)
  else
    let  infile = open_in Sys.argv.(1) in
    read_and_process infile;
    close_in infile;
    Log.print_stats ()

