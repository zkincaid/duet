open BatPervasives
open Srk

module PString = struct
  module I = struct
    type t = string
    let hash = Hashtbl.hash
    let equal = (=)
    let compare = Pervasives.compare
    let pp = Format.pp_print_string
  end
  include I
  module Set = BatSet.Make(I)
end

module Alphabet = PString
module A = PredicateAutomata.Make(Alphabet)(PString)
module Empty = PredicateAutomata.MakeEmpty(A)
module F = PaFormula

let pp_print_list = SrkUtil.pp_print_list
let pp_formula phi = F.pp Format.pp_print_string Format.pp_print_int phi
let show_formula = SrkUtil.mk_show pp_formula

let exists x phi = F.const_exists ~name:(Some x) x phi

let forall x phi = F.const_forall ~name:(Some x) x phi

let of_cfa entry edges =
  let open F in
  let open A in
  let initial =
    mk_and (mk_atom "<!$>" []) (mk_forall (mk_atom "D" [Var 0]))
  in
  let alphabet =
    List.fold_left
      (fun s (_, a, _) -> Alphabet.Set.add a s)
      Alphabet.Set.empty
      edges
  in
  let mk_single x = "<" ^ x ^ ">" in
  let mk_pair x y = "<" ^ x ^ "," ^ y ^ ">" in
  let entry = mk_single entry in
  let locations =
    List.fold_left
      (fun s (x, _, y) -> BatSet.add x (BatSet.add y s))
      BatSet.empty
      edges
    |> BatSet.elements
  in
  let pa =
    let alphabet = Alphabet.Set.add "$" alphabet in
    let vocabulary =
      let pairs =
        BatEnum.cartesian_product
          (BatList.enum locations)
          (BatList.enum locations)
        /@ (fun (x, y) -> (mk_pair x y, 1))
        |> BatList.of_enum
      in
      let singles =
        List.map (fun x -> (mk_single x, 1)) locations
      in
      [("D", 1); ("loc", 0); ("<!$>", 0)]@(singles@pairs)
    in
    A.make alphabet vocabulary initial ["loc"; entry]
  in
  let ifeq x y phi psi =
    mk_or (mk_and (mk_eq x y) phi) (mk_and (mk_neq x y) psi)
  in
  (* Stable actions *)
  SrkUtil.cartesian_product (BatList.enum locations) (BatList.enum locations)
  |> BatEnum.iter (fun (x, y) ->
      add_transition
        pa
        (mk_pair x y)
        alphabet
        (mk_and
           (mk_neq (Var 0) (Var 1))
           (mk_atom (mk_pair x y) [Var 1])));

  locations |> BatList.iter (fun x ->
      add_transition
        pa
        (mk_single x)
        alphabet
        (mk_and
           (mk_neq (Var 0) (Var 1))
           (mk_atom (mk_single x) [Var 1])));

  (* Initialization & movement*)
  edges |> List.iter (fun (src, a, tgt) ->
      let a = Alphabet.Set.singleton a in
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
  let dollar = Alphabet.Set.singleton "$" in
  locations |> BatList.iter (fun x ->
      add_transition pa (mk_pair x x) dollar (mk_atom (mk_single x) [Var 1])
    );
  add_transition pa "D" dollar (mk_atom "loc" [Var 1]);

  add_transition pa "<!$>" alphabet mk_true;

  pa
