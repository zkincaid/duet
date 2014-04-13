(*pp camlp4find deriving.syntax *)

open Apak
open BatPervasives
open OUnit

module Sigma = Putil.PString

module Predicate = struct
  include Putil.PString
  type alpha = string
  let stable _ _ _ _ = false
end

module A = Ipa.Make(Sigma)(Predicate)
open A

module Syntax = struct
  let (==) a b = Eq (a, b)
  let (!=) a b = Neq (a, b)
  let (&&) a b = And (a, b)
  let (||) a b = Or (a, b)
  let (@) p args = Atom (p, args)
  let k = 0
  let i = 1
  let j = 2
end

let ticket_delta = let open Syntax in [
    ("pc", "m := t++", "pc"@[] && "pc1"@[k]);
    ("pc", "[m <= s]", "pc"@[] && "pc2"@[k]);
    ("pc", "s++", "pc"@[] && "pc3"@[k]);

    ("pc1", "m := t++", i != k && "pc1"@[i]);
    ("pc1", "[m <= s]", i != k && "pc1"@[i]);
    ("pc1", "s++", i != k && "pc1"@[i]);

    ("pc2", "m := t++", (i == k && "pc1"@[i]) || (i != k && "pc2"@[i]));
    ("pc2", "[m <= s]", i != k && "pc2"@[i]);
    ("pc2", "s++", i != k && "pc2"@[i]);

    ("pc3", "m := t++", i != k && "pc3"@[i]);
    ("pc3", "[m <= s]", (i == k && "pc2"@[i]) || (i != k && "pc3"@[i]));
    ("pc3", "s++", i != k && "pc3"@[i]);
]

let short_ticket =
  let accept p = false in (*(p = "pc" || p = "pc1")*)
  let open Syntax in
  let delta = [
    ("pc", "m := t++", "pc"@[] && "pc1"@[k]);
    ("pc", "[m = s]", "pc"@[] && "pc2"@[k]);
    ("pc", "s++", "pc"@[] && "pc3"@[k]);

    ("pc1", "m := t++", i != k && "pc1"@[i]);
    ("pc1", "[m = s]", i != k && "pc1"@[i]);
    ("pc1", "s++", i != k && "pc1"@[i]);

    ("pc2", "m := t++", (i == k && "pc1"@[i]) || (i != k && "pc2"@[i]));
    ("pc2", "[m = s]", i != k && "pc2"@[i]);
    ("pc2", "s++", i != k && "pc2"@[i]);

    ("pc3", "m := t++", i != k && "pc3"@[i]);
    ("pc3", "[m = s]", (i == k && "pc2"@[i]) || (i != k && "pc3"@[i]));
    ("pc3", "s++", i != k && "pc3"@[i]);
  ]
  in
  let sigma = ["m := t++"; "[m = s]"; "s++"] in
  make
    ~delta:delta
    sigma
    accept
    ("pc"@[] && "pc3"@[0] && "pc3"@[1])

let short_ticket_proof =
  let open Syntax in
  let delta = [
    (* iPA *)
    ("root", "m := t++", "root"@[]);
    ("root", "[m = s]", "root"@[] || "mi_neq_s"@[k]);
    ("root", "s++", "root"@[]);

    ("mi_neq_s", "m := t++", i != k && "mi_neq_s"@[i]);
    ("mi_neq_s", "[m = s]", i != k && ("mi_neq_mj"@[i;k] || "mi_neq_mj"@[k;i]));
    ("mi_neq_s", "s++", False);

    ("mi_neq_mj", "m := t++", j == k && "mi_lt_t"@[i]);
    ("mi_neq_mj", "[m = s]", "mi_neq_mj"@[i;j]);
    ("mi_neq_mj", "s++", "mi_neq_mj"@[i;j]);

    ("mi_lt_t", "m := t++", i == k || "mi_lt_t"@[i]);
    ("mi_lt_t", "[m = s]", "mi_lt_t"@[i]);
    ("mi_lt_t", "s++", "mi_lt_t"@[i]);
  ]
  in
  let sigma = ["m := t++"; "[m = s]"; "s++"] in
  make ~delta:delta sigma (fun _ -> false) ("root"@[])

let test_accepting () =
  let pa =
    make
      ~delta:ticket_delta
      ["m := t++"; "[m <= s]"; "s++"]
      (fun p -> p = "pc" || p = "pc1")
      (And (Atom ("pc",[]), (And (Atom ("pc3",[0]), Atom ("pc2",[1])))))
  in
  let eps_pa =
    make
      ~delta:ticket_delta
      ["m := t++"; "[m <= s]"; "s++"]
      (fun p -> p = "pc")
      (Atom ("pc",[]))
  in
  "Ticket non-empty" @? ((empty pa) != None);
  "Epsilon" @? ((empty eps_pa) != None)

let test_empty () =
  let pa =
    make
      ~delta:ticket_delta
      ["m := t++"; "[m <= s]"; "s++"]
      (fun p -> p = "pc")
      (And (Atom ("pc",[]), (And (Atom ("pc3",[0]), Atom ("pc2",[1])))))
  in
  "Ticket empty" @? ((empty pa) == None)

let test_short_ticket () =
  let pa =
    intersect short_ticket (negate short_ticket_proof)
  in
  "Short ticket proof non-empty" @? ((empty short_ticket_proof) != None);
  assert_equal ~printer:(Show.show<(string*int) list option>) (empty pa) None

let suite = "Predicate automata" >::: [
  "Accepting" >:: test_accepting;
  "Empty" >:: test_empty;
  "Short ticket" >:: test_short_ticket;
]
