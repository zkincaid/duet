(*pp camlp4find deriving.syntax *)

open Ast
open Apak
open Ark
open ArkPervasives

exception NotHandled of string

include Log.Make(struct let name = "errgen" end)

(******* Printing a program *****************
*********************************************)

let eps_mach = Real_const (QQ.exp (QQ.of_int 2) (-53))
let neg_eps_mach = Real_const (QQ.negate (QQ.exp (QQ.of_int 2) (-53)))
let max_float = Real_const (QQ.exp (QQ.of_int 2) 53)
let min_float = Real_const (QQ.negate (QQ.exp (QQ.of_int 2) 53))

let print_prog (Prog s) =
  print_string "Printing program:\n\n";
  Format.printf "%a@\n" Show.format<stmt_type> s;
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

let primify_cmd = function
  | Skip -> Skip
  | Assign (x, e) -> Assign(primify x, primify_aexp e)
  | Assert (b) -> Assert (primify_bexp b)
  | Print (e) -> Print (primify_aexp e)
  | Assume (b) -> Assume (primify_bexp b)

let rec primify_stmt s =
  match s with
  | Cmd c -> Cmd (primify_cmd c)
  | Seq (s1, s2) -> Seq (primify_stmt s1, primify_stmt s2)
  | Ite (b, s1, s2) -> Ite (primify_bexp b, primify_stmt s1, primify_stmt s2)
  | While (b, s1, residual) -> While (primify_bexp b, primify_stmt s1, residual)

(* Residue computation *)

(* Mark all loops as residual *)
let rec mk_residue = function
  | Seq (x, y) -> Seq (mk_residue x, mk_residue y)
  | Ite (b, x, y) -> Ite (b, mk_residue x, mk_residue y)
  | While (b, s, _) -> While (b, mk_residue s, true)
  | atom -> atom

let mk_seq = function
  | [] -> Cmd Skip
  | xs -> BatList.reduce (fun x y -> Seq (x, y)) xs

let rec compute_residue_aux_1 vars =
  mk_seq (List.map (fun x ->
    mk_seq [
      Cmd (Assign (primify x, Var_exp x));
      Cmd (Assign (infify (epsify (primify x)), Var_exp (infify (epsify x))));
      Cmd (Assign (epsify (primify x), Var_exp (epsify x)))
    ]) vars)

let rec  compute_residue_aux_2 vars =
  mk_seq (List.map (fun x ->
    Seq (Cmd (Assign (epsify x,
                      Sum_exp(Var_exp (epsify (primify x)),
                              Diff_exp(Var_exp(primify x), (Var_exp x))))),
         Cmd (Assign (infify (epsify x),
                      Var_exp (infify (epsify (primify x))))))
  ) vars)

let compute_residue s1 s2 vars =
  mk_residue (mk_seq [
    compute_residue_aux_1 vars;
    s1;
    primify_stmt s2;
    compute_residue_aux_2 vars
  ])

(* Error term generation *)

type optype = Plus
          | Minus
          | Times

let errvar = freshvar ()
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
      let t = errvar in
      let s1 = Cmd (Assign (t,
                            opfunc (Sum_exp (e1, Var_exp (epsify y1)),
                                    Sum_exp (e2, Var_exp (epsify y2)))))
      in
      (* If we have uninterpreted function symbols, we should replace the variable __round_err by one *)
      let t_err = t ^ "__round_err" in
      let s_err_stmts =
        Seq (
         Cmd (Assign (t_err, Havoc_aexp)),
         Cmd (Assume (
           Or_exp(And_exp(Ge_exp (Var_exp (t_err),
                                  Mult_exp (Var_exp t, neg_eps_mach)),
                          Le_exp (Var_exp (t_err),
                                  Mult_exp (Var_exp t, eps_mach))),
                  And_exp(Le_exp (Var_exp (t_err),
                                  Mult_exp (Var_exp t, neg_eps_mach)),
                          (Ge_exp (Var_exp (t_err),
                                   Mult_exp (Var_exp t, eps_mach))))))))
      in
      let tmp1 = Sum_exp (Var_exp t, Var_exp t_err) in
      let s2 =
        Ite (And_exp (Ge_exp (tmp1, min_float),
                      Le_exp (tmp1, max_float)),
             Cmd Skip,
             Cmd (Assign (infify (epsify x), Real_const QQ.one)))
      in
      let s3 = Cmd (Assign (epsify x, Diff_exp (tmp1, opfunc (e1, e2)))) in
      Seq (s1,
           Seq (s_err_stmts,
                Seq (s2,
                     Seq (s3,
                          Cmd (Assign (x, e))))))
  | _ ->
      raise (NotHandled ("Expression in assignment not handled in error term generation: " ^ (aexp_to_string e)))



let generate_err_assign x e =
  match e with
    Real_const k ->
      (* eps_x = havoc(); inf_eps_x = 0; assume (eps_x >= k * eps_mach * -1 && eps_x <= k * eps_mach); *)
      if QQ.geq k QQ.zero then
        mk_seq [
          Cmd (Assign (epsify x, Havoc_aexp));
          Cmd (Assign (infify (epsify x), Real_const QQ.zero));
          Cmd (Assume (And_exp (Ge_exp (Var_exp (epsify x),
                                        Mult_exp (e, neg_eps_mach)),
                                Le_exp (Var_exp (epsify x),
                                        Mult_exp (e, eps_mach)))));
          Cmd (Assign (x, e))
        ]
      else
        mk_seq [
          Cmd (Assign (epsify x, Havoc_aexp));
          Cmd (Assign (infify (epsify x), Real_const QQ.zero));
          Cmd (Assume (And_exp (Le_exp (Var_exp (epsify x),
                                        Mult_exp (e, neg_eps_mach)),
                                Ge_exp (Var_exp (epsify x),
                                        Mult_exp (e, eps_mach)))));
          Cmd (Assign (x, e))
        ]
  | Var_exp y ->
    mk_seq [
      Cmd (Assign (infify (epsify x), Var_exp (infify (epsify y))));
      Cmd (Assign (epsify x, Var_exp (epsify y)));
      Cmd (Assign (x, e))
    ]
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
    Cmd Skip -> Cmd Skip
  | Cmd (Assign (var, e)) ->
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
              (compute_residue s0 (Cmd Skip) vars),
              (compute_residue
                 (Cmd Skip)
                 (While(Or_exp (And_exp (b, (generate_err_bexp b)),
                                And_exp (Not_exp b, Not_exp (generate_err_bexp b))),
                        (generate_err_stmt s vars),
                        true))
                 vars)))
  | Cmd (Assume b) -> Cmd (Assume b)
  | _ -> raise (NotHandled ("Error computation for statement " ^ Show.show<stmt_type> s0))

(* Reformat program to not use nested arithmetic expressions, and use 
   temporary variables instead *)
let rec simplify_aexp e =
  match e with
  | Var_exp _
  | Havoc_aexp
  | Sum_exp (Var_exp _, Var_exp _)
  | Diff_exp (Var_exp _, Var_exp _)
  | Mult_exp (Var_exp _, Var_exp _)
  | Unneg_exp (Var_exp _) -> (Cmd Skip, e)
  | Real_const k ->
    let t = freshvar () in
    (Cmd (Assign (t, Real_const k)), Var_exp t)
  | Sum_exp (e1, e2) ->
    let (prep1, e1') = simplify_aexp e1 in
    let (prep2, e2') = simplify_aexp e2 in
    let t = (freshvar ()) in
    (mk_seq [prep1; prep2; Cmd (Assign (t, Sum_exp (e1', e2')))], Var_exp t)
  | Diff_exp (e1, e2) ->
    let (prep1, e1') = simplify_aexp e1 in
    let (prep2, e2') = simplify_aexp e2 in
    let t = (freshvar ()) in
    (mk_seq [prep1; prep2; Cmd (Assign (t, Diff_exp (e1', e2')))], Var_exp t)
  | Mult_exp (e1, e2) ->
    let (prep1, e1') = simplify_aexp e1 in
    let (prep2, e2') = simplify_aexp e2 in
    let t = (freshvar ()) in
    (mk_seq [prep1; prep2; Cmd (Assign (t, Mult_exp (e1', e2')))], Var_exp t)
  | Unneg_exp e1 ->
    let (prep1, e1') = simplify_aexp e1 in
    let t = (freshvar ()) in
    (Seq (prep1, Cmd (Assign (t, e1'))), Var_exp t)

(* Constants are allowed at the top level, but not as sub-expressions *)
let simplify_aexp = function
  | Real_const k -> (Cmd Skip, Real_const k)
  | e -> simplify_aexp e

let rec simplify_aexp_bexp b =  
  match b with
    Bool_const bc -> (Cmd Skip, b)
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
  | Havoc_bexp -> (Cmd Skip, Havoc_bexp)

let rec simplify_aexp_prog s0 =
  match s0 with
    Cmd Skip -> Cmd Skip
  | Cmd (Assign (var, e)) ->
    let (prep, e') = simplify_aexp e in
    Seq (prep, Cmd (Assign(var, e')))
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
  | Cmd (Assert b) ->
    let (prep, b') = simplify_aexp_bexp b in
    Seq (prep, Cmd (Assert(b')))
  | Cmd (Assume b) ->
    let (prep, b') = simplify_aexp_bexp b in
    Seq (prep, Cmd (Assume(b')))
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
  let mk_guess vars = Cmd (Assert (List.fold_left f (Bool_const true) vars)) in
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
   | _ -> Show.show<cmd_type> (Assume s)

let rec convert_cfg s =
  match s with
    Cmd Skip
  | Cmd (Assign (_)) ->
    let en = inc () in
    let ex = inc () in
    (en, ex, [(en, Show.show<stmt_type> s, ex)])
  | Seq (s1, s2) ->
    let (en1, ex1, t1) = convert_cfg s1 in
    let (en2, ex2, t2) = convert_cfg s2 in
    (en1, ex2, t1 @  [(ex1, Show.show<cmd_type> Skip, en2)] @ t2 )
  | Ite (b, s1, s2) ->
    let en = inc () in
    let ex = inc () in
    let (en1, ex1, t1) = convert_cfg s1 in
    let (en2, ex2, t2) = convert_cfg s2 in
    let newedges =
      [(en, Show.show<cmd_type> (Assume b), en1);
       (en, Show.show<cmd_type> (Assume (Not_exp b)), en2)]
      @ t1 @ t2 @
        [(ex1, Show.show<cmd_type> Skip, ex);
         (ex2, Show.show<cmd_type> Skip, ex)]
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
       [(ex1, Show.show<cmd_type> Skip, en)]
    in
    (en, ex, newedges)
  | Cmd (Assert (b))
  | Cmd (Assume (b)) ->
    let en = inc () in
    let ex = inc () in
    (en, ex, [(en, bexp_to_assume_list b, ex)])
  | _ -> raise (NotHandled ("T2 Translation of " ^ (Show.show<stmt_type> s)))


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


module C = struct
  type t = cmd_type deriving (Show,Compare)
  let compare = Compare_t.compare
  let show = Show_t.show
  let format = Show_t.format
  let default = Skip
end

module Cfa = struct
  include ExtGraph.Persistent.Digraph.MakeBidirectionalLabeled(Putil.PInt)(C)
end
module CfaDisplay = ExtGraph.Display.MakeLabeled(Cfa)(Putil.PInt)(C)

let build_cfa s =
  let fresh =
    let m = ref (-1) in
    fun () -> (incr m; !m)
  in
  let add_edge cfa u lbl v =
    Cfa.add_edge_e cfa (Cfa.E.create u lbl v)
  in
  let rec go cfa entry = function
    | Cmd Skip -> (cfa, entry)
    | Cmd c ->
      let succ = fresh () in
      (add_edge cfa entry c succ, succ)
    | Seq (c, d) ->
      let (cfa, exit) = go cfa entry c in
      go cfa exit d
    | Ite (phi, c, d) ->
      let succ, enter_then, enter_else = fresh (), fresh (), fresh () in
      let cfa = add_edge cfa entry (Assume phi) enter_then in
      let cfa = add_edge cfa entry (Assume (Not_exp phi)) enter_else in
      let (cfa, exit_then) = go cfa enter_then c in
      let (cfa, exit_else) = go cfa enter_else d in
      (Cfa.add_edge (Cfa.add_edge cfa exit_then succ) exit_else succ, succ)
    | While (phi, body, _) ->
      let (cfa, enter_body) = go cfa entry (Cmd (Assume phi)) in
      let (cfa, exit_body) = go cfa enter_body body in
      let cfa = Cfa.add_edge cfa exit_body entry in
      go cfa entry (Cmd (Assume (Not_exp phi)))
  in
  let entry = fresh () in
  let (cfa, exit) = go (Cfa.add_vertex Cfa.empty entry) entry s in
  (cfa, entry, exit)

let primify_cfa g =
  let f e g =
    Cfa.add_edge_e
      g
      (Cfa.E.create (Cfa.E.src e) (primify_cmd (Cfa.E.label e)) (Cfa.E.dst e))
  in
  Cfa.fold_edges_e f g Cfa.empty

module Pair(M : Putil.Ordered) = struct
  type t = M.t * M.t deriving (Show)
  module Compare_t = struct
    type a = t
    let compare (a,b) (c,d) = match M.compare a c with
      | 0 -> M.compare b d
      | c -> c
  end
  let compare = Compare_t.compare
  let show = Show_t.show
  let format = Show_t.format
  let equal x y = compare x y = 0
  let hash = Hashtbl.hash
end

(* Tensor product *)
module TCfa = struct
  module VP = Pair(Putil.PInt)
  module CP = Pair(C)
  module G = ExtGraph.Persistent.Digraph.MakeBidirectionalLabeled
    (struct
      include VP
      module Set = Putil.Hashed.Set.Make(VP)
      module Map = Putil.Map.Make(VP)
      module HT = BatHashtbl.Make(VP)
     end)
    (struct
      include CP
      let default = (Skip, Skip)
     end)
  module D = ExtGraph.Display.MakeLabeled(G)(VP)(CP)
  include G
  include D
  let tensor (g,g_entry) (h, h_entry) =
    let add_vertex v (worklist, tensor) =
      if mem_vertex tensor v then (worklist, tensor)
      else (v::worklist, add_vertex tensor v)
    in
    let add_succ u (worklist, tensor) (e,f) =
      let v = Cfa.E.dst e, Cfa.E.dst f in
      let lbl = Cfa.E.label e, Cfa.E.label f in
      let (worklist, tensor) = add_vertex v (worklist, tensor) in
      (worklist, add_edge_e tensor (E.create u lbl v))
    in
    let rec fix (worklist, tensor) =
      match worklist with
      | [] -> tensor
      | ((u,v)::worklist) ->
        fix (BatEnum.fold
               (add_succ (u,v))
               (worklist, tensor)
               (Putil.cartesian_product
                  (Cfa.enum_succ_e g u)
                  (Cfa.enum_succ_e h v)))
    in
    let entry = (g_entry, h_entry) in
    fix ([entry], G.add_vertex empty entry)
end

module K = Bounds.K

module T = K.T
module F = K.F
module V = K.V
module D = T.D

let rec real_aexp = function
  | Real_const k -> T.const k
  | Sum_exp (s, t) -> T.add (real_aexp s) (real_aexp t)
  | Diff_exp (s, t) -> T.sub (real_aexp s) (real_aexp t)
  | Mult_exp (s, t) -> T.mul (real_aexp s) (real_aexp t)
  | Var_exp v -> T.var (K.V.mk_var v)
  | Unneg_exp t -> T.neg (real_aexp t)
  | Havoc_aexp -> T.var (K.V.mk_tmp "havoc" TyReal)
let rec real_bexp = function
  | Bool_const true -> F.top
  | Bool_const false -> F.bottom
  | Eq_exp (s, t) -> F.eq (real_aexp s) (real_aexp t)
  | Ne_exp (s, t) -> F.negate (F.eq (real_aexp s) (real_aexp t))
  | Gt_exp (s, t) -> F.gt (real_aexp s) (real_aexp t)
  | Lt_exp (s, t) -> F.lt (real_aexp s) (real_aexp t)
  | Ge_exp (s, t) -> F.geq (real_aexp s) (real_aexp t)
  | Le_exp (s, t) -> F.leq (real_aexp s) (real_aexp t)
  | And_exp (phi, psi) -> F.conj (real_bexp phi) (real_bexp psi)
  | Or_exp (phi, psi) -> F.disj (real_bexp phi) (real_bexp psi)
  | Not_exp phi -> F.negate (real_bexp phi)
  | Havoc_bexp -> F.leqz (T.var (K.V.mk_tmp "havoc" TyReal))

let eps_mach = QQ.exp (QQ.of_int 2) (-53)
let rec float_aexp = function
  | Real_const k -> (T.const (Mpqf.of_float (Mpqf.to_float k)), F.top)
  | Sum_exp (s, t) -> float_binop T.add s t
  | Diff_exp (s, t) -> float_binop T.sub s t
  | Mult_exp (s, t) -> float_binop T.mul s t
  | Var_exp v -> (T.var (K.V.mk_var v), F.top)
  | Unneg_exp t ->
    let (t, t_err) = float_aexp t in
    (T.neg t, t_err)
  | Havoc_aexp -> (T.var (K.V.mk_tmp "havoc" TyReal), F.top)
and float_binop op s t =
  let (s,s_err) = float_aexp s in
  let (t,t_err) = float_aexp t in
  let err = T.var (K.V.mk_tmp "err" TyReal) in
  let term = op s t in
  let err_magnitude = T.mul term (T.const eps_mach) in
  let err_constraint =
    F.disj
      (F.conj
         (F.leq (T.neg err_magnitude) err)
         (F.leq err err_magnitude))
      (F.conj
         (F.leq (T.neg err_magnitude) err)
         (F.leq err (T.neg err_magnitude)))
  in
  (T.add term err, F.conj err_constraint (F.conj s_err t_err))

let rec nnf = function
  | Bool_const true -> Bool_const true
  | Bool_const false -> Bool_const false
  | Eq_exp (s, t) -> Eq_exp (s, t)
  | Gt_exp (s, t) -> Gt_exp (s, t)
  | Lt_exp (s, t) -> Lt_exp (s, t)
  | Ge_exp (s, t) -> Ge_exp (s, t)
  | Le_exp (s, t) -> Le_exp (s, t)
  | And_exp (phi, psi) -> And_exp (nnf phi, nnf psi)
  | Or_exp (phi, psi) -> Or_exp (nnf phi, nnf psi)
  | Havoc_bexp -> Havoc_bexp
  | Ne_exp (s, t) -> Or_exp (Lt_exp (s, t), Gt_exp (s, t))
  | Not_exp phi -> negate phi
and negate = function
  | Bool_const true -> Bool_const false
  | Bool_const false -> Bool_const true
  | Eq_exp (s, t) -> Or_exp (Lt_exp (s, t), Gt_exp (s, t))
  | Gt_exp (s, t) -> Le_exp (s, t)
  | Lt_exp (s, t) -> Ge_exp (s, t)
  | Ge_exp (s, t) -> Lt_exp (s, t)
  | Le_exp (s, t) -> Gt_exp (s, t)
  | And_exp (phi, psi) -> Or_exp (negate phi, negate psi)
  | Or_exp (phi, psi) -> And_exp (negate phi, negate psi)
  | Havoc_bexp -> Havoc_bexp
  | Ne_exp (s, t) -> Eq_exp (s, t)
  | Not_exp phi -> nnf phi

let rec float_bexp = function
  | Bool_const true -> F.top
  | Bool_const false -> F.bottom
  | Eq_exp (s, t) -> float_bool_binop F.eq s t
  | Gt_exp (s, t) -> float_bool_binop F.gt s t
  | Lt_exp (s, t) -> float_bool_binop F.lt s t
  | Ge_exp (s, t) -> float_bool_binop F.geq s t
  | Le_exp (s, t) -> float_bool_binop F.leq s t
  | And_exp (phi, psi) -> F.conj (float_bexp phi) (float_bexp psi)
  | Or_exp (phi, psi) -> F.disj (float_bexp phi) (float_bexp psi)
  | Havoc_bexp -> F.leqz (T.var (K.V.mk_tmp "havoc" TyReal))
  | Ne_exp _ -> assert false
  | Not_exp _ -> assert false
and float_bool_binop op s t =
  let (s,s_err) = float_aexp s in
  let (t,t_err) = float_aexp t in
  F.conj (op s t) (F.conj s_err t_err)
let float_bexp bexp = float_bexp (nnf bexp)

let print_bounds vars formula =
  let f v =
    T.sub
      (T.var (V.mk_var (Bounds.StrVar.prime v)))
      (T.var (V.mk_var (Bounds.StrVar.prime (primify v))))
  in
  let g v bounds =
    let bound_str =
      match bounds with
      | (Some x, Some y) ->
        string_of_float (Mpqf.to_float (QQ.max (Mpqf.abs x) (Mpqf.abs y)))
      | (_, _) -> "oo"
    in
    Format.printf "  | %s - %s' | <= %s@\n" v v bound_str
  in
  List.iter2 g vars (F.optimize (List.map f vars) formula)

let man = Box.manager_alloc ()

module A = Fixpoint.MakeAnalysis(TCfa)(struct
  type t = Box.t D.t
  include Putil.MakeFmt(struct
    type a = t
    let format = D.format
  end)
  let join x y = D.join x y
  let widen x y = D.widen x y
  let bottom = D.bottom man (D.Env.of_list [])
  let equal = D.equal
end)

let float_post cmd prop =
  let project prop = D.exists man (fun p -> V.lower p != None) prop in
  (* Assumptions can be non-linear; Apron's linearization works better by
     iterating assumptions.  It's possible that this iteration won't terminate
     - it depends on the details of Apron's linearization. *)
  let rec assume prop phi =
    let next = F.abstract_assume man prop phi in
    if D.equal next prop then prop
    else assume next phi
  in
  match cmd with
  | Assign (v, rhs) ->
    let (rhs, rhs_err) = float_aexp rhs in
    project (F.abstract_assign man
               (assume prop rhs_err)
               (V.mk_var v)
               rhs)
  | Assume phi -> project (F.abstract_assume man prop (float_bexp phi))
  | Skip | Assert _ | Print _ -> prop

let real_post cmd prop =
  match cmd with
  | Assign (v, rhs) -> F.abstract_assign man prop (V.mk_var v) (real_aexp rhs)
  | Assume phi -> F.abstract_assume man prop (real_bexp phi)
  | Skip | Assert _ | Print _ -> prop

let tensor_post (fcmd, rcmd) prop =
  let post = float_post fcmd (real_post rcmd prop) in
  logf ~level:3 "pre:@\n %a@\ncmd: %a/%a@\npost:@\n %a"
    D.format prop
    C.format fcmd
    C.format rcmd
    D.format post;
  post

let iter_analyze tensor entry =
  let tr e prop =
    let (flbl, rlbl) = TCfa.E.label e in
    tensor_post (flbl, rlbl) prop
  in
  let vtr v prop =
    if v = entry then D.top man (D.Env.of_list []) else prop
  in
  let result =
    A.analyze_ldi vtr ~edge_transfer:tr ~delay:2 ~max_decrease:2 tensor
  in
  let print (u, v) =
    let prop = A.output result (u, v) in
    if D.is_bottom prop then Format.printf "At (%d, %d): unreachable@\n" u v
    else begin
      let sigma v = match V.lower v with
        | Some v -> T.var (V.mk_var (Bounds.StrVar.prime v))
        | None -> assert false
      in
      let phi = F.of_abstract prop in
      let vars =
        let f v = v.[String.length v - 1] != ''' in
        List.filter f (K.VarSet.elements (K.formula_free_program_vars phi))
      in

      Format.printf "At (%d, %d):@\n" u v;
(*      Format.printf "%a@\n@?" D.format prop;*)
      print_bounds vars (F.subst sigma phi)
    end
  in
  Format.printf "Error bounds (iterative analysis):@\n";
  TCfa.iter_vertex print tensor;
  Format.printf "==================================@\n";
  result

let float_weight cmd =
  match cmd with
  | Assign (v, rhs) ->
    let (rhs, rhs_err) = float_aexp rhs in
    { K.assign v rhs with K.guard = rhs_err }
  | Assume phi -> K.assume (float_bexp phi)
  | Skip -> K.one
  | Assert _ | Print _ -> K.one

let real_weight cmd =
  match cmd with
  | Assign (v, rhs) -> K.assign v (real_aexp rhs)
  | Assume phi -> K.assume (real_bexp phi)
  | Skip -> K.one
  | Assert _ | Print _ -> K.one

module P = Pathexp.MakeElim(TCfa)(K)

let tensor_weight result e =
  let (flbl, rlbl) = TCfa.E.label e in
  (* real & float operate on disjoint sets of variables, so sequential
     composition is non-interfering *)
  let weight = K.mul (float_weight flbl) (real_weight rlbl) in
  let inv = K.assume (F.of_abstract (A.output result (TCfa.E.src e))) in
  K.mul inv weight

let analyze tensor entry =
  let result = iter_analyze tensor entry in
  let pathexp = P.single_src tensor (tensor_weight result) entry in
  let print (u,v) =
    let pathexp = pathexp (u,v) in
    let vars =
      let f v = v.[String.length v - 1] != ''' in
      List.filter f (K.VarSet.elements (K.modifies pathexp))
    in
    let phi = K.to_formula pathexp in
    if F.is_sat phi then begin
      Format.printf "At (%d, %d):@\n" u v;
      print_bounds vars phi
    end else Format.printf "At (%d, %d): unreachable@\n" u v;
  in
  Format.printf "Error bounds (path expression analysis):@\n";
  TCfa.iter_vertex print tensor;
  Format.printf "========================================@\n"

(*********** Main function ****************
*******************************************)

let read_and_process infile =
   let lexbuf  = Lexing.from_channel infile in
   let Prog prog = Parser.main Lexer.token lexbuf in
   print_prog (Prog prog)

let _ =
  if Array.length Sys.argv <> 2 then
    Format.eprintf "usage: %s input_filename\n" Sys.argv.(0)
  else
    let  infile = open_in Sys.argv.(1) in
    read_and_process infile;
    close_in infile;
    Log.print_stats ()

