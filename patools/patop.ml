open Apak
open BatPervasives

module A = PredicateAutomata.Make(Putil.PString)(Putil.PString)

let pp_print_list = Apak.Putil.pp_print_list
let pp_formula phi = Formula.pp Putil.PString.pp Putil.PInt.pp phi
let show_formula = Putil.mk_show pp_formula

let exists x phi = Formula.const_exists ~name:(Some x) x phi

let forall x phi = Formula.const_forall ~name:(Some x) x phi

let of_cfa entry edges =
  let open Formula in
  let open A in
  let initial =
    mk_and (mk_atom "<!$>" []) (mk_forall (mk_atom "D" [Var 0]))
  in
  let sigma =
    List.fold_left
      (fun s (_, a, _) -> BatSet.add a s)
      BatSet.empty
      edges
    |> BatSet.elements
  in
  let mk_single x = "<" ^ x ^ ">" in
  let mk_pair x y = "<" ^ x ^ "," ^ y ^ ">" in
  let entry = mk_single entry in
  let pa = A.make ("$"::sigma) ["loc"; entry] initial in
  let ifeq x y phi psi =
    mk_or (mk_and (mk_eq x y) phi) (mk_and (mk_neq x y) psi)
  in
  let locations =
    List.fold_left
      (fun s (x, _, y) -> BatSet.add x (BatSet.add y s))
      BatSet.empty
      edges
    |> BatSet.elements
  in
  (* Stable actions *)
  ApakEnum.cartesian_product (BatList.enum locations) (BatList.enum locations)
  |> BatEnum.iter (fun (x, y) ->
      sigma |> BatList.iter (fun alpha ->
          add_transition
            pa
            (mk_pair x y)
            alpha (mk_and
                     (mk_neq (Var 0) (Var 1))
                     (mk_atom (mk_pair x y) [Var 1]))
        )
    );
  locations |> BatList.iter (fun x ->
      sigma |> BatList.iter (fun alpha ->
          add_transition
            pa
            (mk_single x)
            alpha
            (mk_and
               (mk_neq (Var 0) (Var 1))
               (mk_atom (mk_single x) [Var 1]))
        )
    );

  (* Initialization & movement*)
  edges |> List.iter (fun (src, a, tgt) ->
      add_transition pa "D" a (ifeq (Var 0) (Var 1)
                                 (mk_atom (mk_pair src tgt) [Var 1])
                                 (mk_atom "D" [Var 1]));
      add_transition pa "loc" a (ifeq (Var 0) (Var 1)
                                   (mk_atom (mk_pair src tgt) [Var 1])
                                   (mk_atom "loc" [Var 1]));

      add_transition pa (mk_single tgt) a (mk_and
                                             (mk_eq (Var 0) (Var 1))
                                             (mk_atom (mk_single src) [Var 1]));
      locations |> List.iter (fun old ->
          add_transition
            pa
            (mk_pair tgt old)
            a
            (mk_and
               (mk_eq (Var 0) (Var 1))
               (mk_atom (mk_pair src old) [Var 1]))
        )
    );

  (* Dollar *)
  locations |> BatList.iter (fun x ->
      add_transition pa (mk_pair x x) "$" (mk_atom (mk_single x) [Var 1])
    );
  add_transition pa "D" "$" (mk_atom "loc" [Var 1]);

  sigma |> List.iter (fun alpha ->
      add_transition pa "<!$>" alpha mk_true
    );
  pa
