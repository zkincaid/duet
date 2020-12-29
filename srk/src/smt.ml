open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.smt" end)

module Solver = SrkZ3.Solver

let mk_solver ?(theory="") srk = SrkZ3.mk_solver ~theory srk

let get_model ?(symbols=[]) srk phi =
  let solver = mk_solver srk in
  Solver.add solver [phi];
  Solver.get_model ~symbols solver

let get_concrete_model srk symbols phi =
  let solver = mk_solver srk in
  Solver.add solver [phi];
  Solver.get_concrete_model solver symbols

let is_sat srk phi =
  let solver = mk_solver srk in
  Solver.add solver [phi];
  Solver.check solver []

let entails srk phi psi =
  match is_sat srk (mk_and srk [phi; mk_not srk psi]) with
  | `Sat -> `No
  | `Unsat -> `Yes
  | `Unknown -> `Unknown

let equiv srk phi psi =
  let equiv_formula =
    mk_or srk [mk_and srk [phi; mk_not srk psi];
               mk_and srk [mk_not srk phi; psi]]
  in
  match is_sat srk equiv_formula with
  | `Sat -> `No
  | `Unsat -> `Yes
  | `Unknown -> `Unknown

let affine_interpretation srk interp phi =
  (* Replace each function's interpretation f(x1,...,xn) = body with
     f(x1,...,xn) = a1*x1 + ... + an*xn + b; leave the interpretation of other
     symbols unchanged.  *)
  let fresh_real () =
    let sym = mk_symbol srk `TyReal in
    mk_const srk sym
  in
  let symbolic_affine_interp =
    Symbol.Set.fold
      (fun sym sai ->
         match Interpretation.value interp sym with
         | `Bool b -> Interpretation.add_bool sym b sai
         | `Real k -> Interpretation.add_real sym k sai
         | `Arr a -> Interpretation.add_array sym a interp
         | `Fun body ->
           match typ_symbol srk sym with
           | `TyFun (args, `TyReal) when List.for_all ((=) `TyReal) args ->
             let lin_body =
               (0 -- (List.length args - 1))
               /@ (fun i ->
                   mk_mul srk [mk_var srk i `TyReal; fresh_real ()])
               |> BatList.of_enum
             in
             let affine_body =
               (mk_add srk (fresh_real()::lin_body)
                :> ('a,typ_fo) expr)
             in
             Interpretation.add_fun sym affine_body sai
           | _ ->
             Interpretation.add_fun sym body sai)
      (symbols phi)
      (Interpretation.empty srk)
  in
  (* phi' is non-linear if there are nested function applications. *)
  let phi' = Interpretation.substitute symbolic_affine_interp phi in
  match get_model srk phi' with
  | `Unsat -> `Unsat
  | `Unknown -> `Unknown
  | `Sat coeff_interp ->
    let affine_interp =
      BatEnum.fold
        (fun interp (sym,sym_interp) ->
           match sym_interp with
           | `Bool b -> Interpretation.add_bool sym b interp
           | `Real k -> Interpretation.add_real sym k interp
           | `Arr a -> Interpretation.add_array sym a interp
           | `Fun body ->
             Interpretation.add_fun
               sym
               (Interpretation.substitute coeff_interp body)
               interp)
        (Interpretation.empty srk)
        (Interpretation.enum symbolic_affine_interp)
    in
    `Sat affine_interp
