open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.smt" end)

module StdSolver = SrkZ3.Solver

let get_model ?(symbols=[]) srk phi =
  let solver = StdSolver.make srk in
  StdSolver.add solver [phi];
  StdSolver.get_model ~symbols solver

let get_concrete_model srk symbols phi =
  let solver = StdSolver.make srk in
  StdSolver.add solver [phi];
  StdSolver.get_concrete_model solver symbols

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
           | `Fun body ->
             Interpretation.add_fun
               sym
               (Interpretation.substitute coeff_interp body)
               interp)
        (Interpretation.empty srk)
        (Interpretation.enum symbolic_affine_interp)
    in
    `Sat affine_interp

module Model = struct
  type 'a t =
    { m_sat : ('a formula) -> bool
    ; m_sign : ('a arith_term) -> [ `Zero | `Pos | `Neg | `Unknown ] }
  let sat m = m.m_sat
  let sign m = m.m_sign
end

module Solver = struct
  type 'a t =
    { s_add : ('a formula) list -> unit
    ; s_check : ('a formula) list -> [ `Sat | `Unsat | `Unknown ]
    ; s_get_model : unit -> [ `Sat of ('a Model.t) | `Unsat | `Unknown ]
    ; s_push : unit -> unit
    ; s_pop : int -> unit }

  let get_model s = s.s_get_model ()
  let check ?(assumptions=[]) s = s.s_check assumptions
  let add s = s.s_add
  let push s = s.s_push ()
  let pop s = s.s_pop

  let make srk =
    match get_theory srk with
    | `LIRA ->
      let s = StdSolver.make ~theory:"QF_LIRA" srk in
      let s_add xs = StdSolver.add s xs in
      let s_check assumptions = StdSolver.check ~assumptions s in
      let s_get_model () =
        match StdSolver.get_model s with
        | `Sat interp ->
          let m_sat phi = Interpretation.evaluate_formula interp phi in
          let m_sign term =
            match QQ.compare (Interpretation.evaluate_term interp term) QQ.zero with
            | 0 -> `Zero
            | c when c < 0 -> `Neg
            | _ -> `Pos
          in
          `Sat (Model.{ m_sat; m_sign })
        | `Unsat -> `Unsat
        | `Unknown -> `Unknown
      in
      let s_push () = StdSolver.push s in
      let s_pop = StdSolver.pop s in
      { s_add ; s_check ; s_get_model; s_push; s_pop }

    | `LIRR ->
      let s = LirrSolver.Solver.make srk in
      let s_add = LirrSolver.Solver.add s in
      let s_check assumptions =
        match LirrSolver.Solver.get_model ~assumptions s with
        | `Sat _ -> `Sat
        | `Unsat -> `Unsat
        | `Unknown -> `Unknown
      in
      let s_get_model () =
        match LirrSolver.Solver.get_model s with
        | `Sat m ->
          let m_sat phi = LirrSolver.Model.evaluate_formula srk m phi in
          let m_sign t = LirrSolver.Model.sign srk m t in
          `Sat (Model.{ m_sat; m_sign })
        | `Unsat -> `Unsat
        | `Unknown -> `Unknown
      in
      let s_push () = LirrSolver.Solver.push s in
      let s_pop = LirrSolver.Solver.pop s in
      { s_add ; s_check ; s_get_model; s_push; s_pop }
end

let is_sat srk phi =
  let solver = Solver.make srk in
  Solver.add solver [phi];
  Solver.check solver

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
