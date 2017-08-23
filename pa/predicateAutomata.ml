open BatPervasives
open PaFormula
open Ark

let sep formatter () = Format.fprintf formatter ",@ "
let pp_print_list ?(pp_sep=sep) pp_elt formatter xs =
    ArkUtil.pp_print_enum ~pp_sep pp_elt formatter (BatList.enum xs)

include Log.Make(struct let name = "pa" end)

module type Alphabet = sig
  type t
  val pp : Format.formatter -> t -> unit
  val hash : t -> int
  val equal : t -> t -> bool

  module Set : sig
    type elt = t
    type t
    val mem : elt -> t -> bool
    val inter : t -> t -> t
    val diff : t -> t -> t
    val enum : t -> elt BatEnum.t
    val choose : t -> elt
    val is_empty : t -> bool
    val equal : t -> t -> bool
  end
end

module type Predicate = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module F = PaFormula

module type S = sig
  type t
  type predicate
  type letter
  type letter_set
  type formula = (predicate, int) PaFormula.formula
  type config

  module Config : Struct.S with type predicate = predicate
                            and type t = config

  module LetterSet : sig
    type t = letter_set
    val mem : letter -> t -> bool
    val inter : t -> t -> t
    val enum : t -> letter BatEnum.t
    val choose : t -> letter
  end

  val pp : Format.formatter -> t -> unit
  val pp_letter : Format.formatter -> letter -> unit
  val pp_ground : int -> Format.formatter -> t -> unit
  val pp_formula : Format.formatter -> formula -> unit

  val make : letter_set ->
    (predicate * int) list ->
    formula ->
    predicate list ->
    t
  val add_predicate : t -> predicate -> int -> unit
  val add_accepting : t -> predicate -> unit
  val add_transition : t -> predicate -> letter_set -> formula -> unit
  val conjoin_transition : t -> predicate -> letter_set -> formula -> unit
  val alphabet : t -> letter_set
  val vocabulary : t -> (predicate * int) BatEnum.t
  val mem_vocabulary : t -> predicate -> bool
  val arity : t -> predicate -> int
  val initial : t -> formula
  val post : t -> formula -> letter -> formula
  val concrete_post : t -> formula -> (letter * int) -> formula
  val succs : t -> config -> (letter * int) -> config BatEnum.t
  val successors : t -> config -> int -> (letter * config) BatEnum.t
  val pred : t -> config -> (letter * int) -> config
  val accepting_formula : t -> formula -> bool
  val accepting : t -> config -> bool

  val negate : t -> t
  val union : t -> t -> t
  val intersect : t -> t -> t
end

module Make (A : Alphabet) (P : Predicate) = struct
  type predicate = P.t
  type letter = A.t [@@deriving show]
  type letter_set = A.Set.t
  type formula = (P.t, int) F.formula
  type atom = P.t * int list [@@deriving ord]

  module PSet = BatSet.Make(P)
  module PHT = BatHashtbl.Make(P)
  module LetterSet = A.Set

  let pp_atom formatter (p,args) =
    Format.fprintf formatter "@[%a(%a)@]"
      P.pp p
      (ArkUtil.pp_print_enum Format.pp_print_int) (BatList.enum args)


  (* A configuration is a finite structure over the vocabulary of the PA. *)
  module Config = Struct.Make(P)
  type config = Config.t

  type t =
    { arity : int PHT.t;

      (* Transition function is represented as a list of letter_set * formula
         pairs.  If a given letter has multiple applicable transition rules
         (i.e., belongs to more than one letter_set in the list), the rules
         are interpreted disjunctively. *)
      delta : ((letter_set * formula) list) PHT.t;

      alphabet : letter_set;
      mutable accepting : PSet.t;
      initial : formula; }

  let initial pa = pa.initial

  let mem_vocabulary pa predicate = PHT.mem pa.arity predicate

  let arity pa predicate = PHT.find pa.arity predicate

  let show_predicate = ArkUtil.mk_show P.pp

  let add_predicate pa predicate arity =
    if mem_vocabulary pa predicate then
      invalid_arg "PredicateAutomata.add_predicate: already belongs \
                   to the vocabulary of the input PA"
    else begin
      PHT.add pa.arity predicate arity;
      PHT.add pa.delta predicate []
    end

  let add_accepting pa predicate =
    if not (mem_vocabulary pa predicate) then
      invalid_arg "PredicateAutomata.add_accepting: predicate does not belong \
                   to the vocabulary of the input PA"
    else
      pa.accepting <- PSet.add predicate pa.accepting

  let transitions pa predicate =
    if not (mem_vocabulary pa predicate) then
      invalid_arg ("PredicateAutomata.transitions: predicate `"
                   ^ (show_predicate predicate)
                   ^ "' does not belong to the vocabulary of the input PA")
    else
      PHT.find pa.delta predicate

  let transition pa predicate letter =
    (* Find all applicable transition rules and take the disjunction *)
    List.fold_left (fun applicable (letters, rhs) ->
        if LetterSet.mem letter letters then rhs::applicable
        else applicable)
      []
      (transitions pa predicate)
    |> BatList.enum
    |> PaFormula.big_disj

  let add_transition pa predicate letters rhs =
    if not (mem_vocabulary pa predicate) then
      invalid_arg "PredicateAutomata.add_transition: predicate does not belong \
                   to the vocabulary of the input PA"
    else if not (LetterSet.is_empty letters) then
      PHT.replace
        pa.delta
        predicate
        ((letters, rhs)::(PHT.find pa.delta predicate))

  let conjoin_transition pa predicate letters rhs =
    List.fold_left (fun rules (r_letters, r_rhs) ->
        let intersect = LetterSet.inter letters r_letters in
        if LetterSet.is_empty intersect then
          (r_letters, r_rhs)::rules
        else
          let diff = LetterSet.diff r_letters letters in
          let rules =
            if LetterSet.is_empty diff then
              rules
            else
              (diff, r_rhs)::rules
          in
          (intersect, PaFormula.mk_and r_rhs rhs)::rules)
      []
      (transitions pa predicate)
    |> PHT.replace pa.delta predicate

  let make alphabet vocabulary initial accepting =
    let pa =
      { delta = PHT.create 991;
        arity = PHT.create 991;
        alphabet = alphabet;
        accepting = PSet.empty;
        initial = initial }
    in
    List.iter (fun (q,ar) -> add_predicate pa q ar) vocabulary;
    List.iter (add_accepting pa) accepting;
    pa

  let vocabulary pa = PHT.enum pa.arity

  let alphabet pa = pa.alphabet

  let same_alphabet pa qa = A.Set.equal pa.alphabet qa.alphabet

  let predicates pa = PHT.keys pa.arity |> PSet.of_enum
      
  let disjoint_predicates pa qa =
    PSet.is_empty (PSet.inter (predicates pa) (predicates qa))

  let union pa qa =
    if not (PSet.is_empty (PSet.inter (predicates pa) (predicates qa))) then
      invalid_arg "PredicateAutomata.union: input automata must have disjoint \
                   predicates";
    if not (PSet.is_empty (PSet.inter (predicates pa) (predicates qa))) then
      invalid_arg "PredicateAutomata.union: input automata must have equal \
                   alphabets";
    let union =
      { delta = PHT.copy pa.delta;
        arity = PHT.copy pa.arity;
        alphabet = pa.alphabet;
        accepting = PSet.union pa.accepting qa.accepting;
        initial = mk_or pa.initial qa.initial }
    in
    qa.arity |> PHT.iter (fun q arity -> add_predicate union q arity);
    qa.delta |> PHT.iter (fun q rules -> PHT.replace union.delta q rules);

    union

  let intersect pa qa =
    if not (PSet.is_empty (PSet.inter (predicates pa) (predicates qa))) then
      invalid_arg "PredicateAutomata.union: input automata must have disjoint \
                   predicates";
    if not (PSet.is_empty (PSet.inter (predicates pa) (predicates qa))) then
      invalid_arg "PredicateAutomata.union: input automata must have equal \
                   alphabets";
    let inter =
      { delta = PHT.copy pa.delta;
        arity = PHT.copy pa.arity;
        alphabet = pa.alphabet;
        accepting = PSet.union pa.accepting qa.accepting;
        initial = mk_and pa.initial qa.initial }
    in
    qa.arity |> PHT.iter (fun q arity -> add_predicate inter q arity);
    qa.delta |> PHT.iter (fun q rules -> PHT.replace inter.delta q rules);
    inter

  (* Negates a formula, except that atomic (non-equality) propositions are
     left untouched. *)
  let negate_formula phi =
    let f = function
      | `And (phi, psi) -> mk_or phi psi
      | `Or (phi, psi) -> mk_and phi psi
      | `Atom (p, args) -> mk_atom p args
      | `Eq (i, j) -> mk_neq i j
      | `Neq (i, j) -> mk_eq i j
      | `T -> mk_false
      | `F -> mk_true
      | `Exists (hint, phi) -> construct (`Forall (hint, phi))
      | `Forall (hint, phi) -> construct (`Exists (hint, phi))
    in
    eval f phi

  let negate pa =
    let accepting =
      BatEnum.filter (not % flip PSet.mem pa.accepting) (PHT.keys pa.arity)
      |> PSet.of_enum
    in
    let neg_pa =
      { arity = PHT.copy pa.arity;
        delta = PHT.create 991;
        alphabet = pa.alphabet;
        accepting = accepting;
        initial = negate_formula pa.initial; }
    in

    PHT.keys pa.arity |> BatEnum.iter (fun q ->
        PHT.add neg_pa.delta q [(pa.alphabet, mk_true)]);

    pa.delta |> PHT.iter (fun q rules ->
        rules |> List.iter (fun (letters, rhs) ->
            conjoin_transition neg_pa q letters (negate_formula rhs)));
    neg_pa

  let post pa phi letter =
    let rec go depth phi =
      match F.destruct phi with
      | `And (phi, psi) -> mk_and (go depth phi) (go depth psi)
      | `Or (phi, psi) -> mk_or (go depth phi) (go depth psi)
      | `Atom (head, args) ->
        let rhs = transition pa head letter in
        let subs n =
          if n = 0 then Var depth
          else
            try List.nth args (n - 1)
            with Invalid_argument _ -> invalid_arg "post"
        in
        F.var_substitute subs rhs
      | `Forall (name, phi) ->
        mk_forall ~name:name (go (depth + 1) phi)
      | `Exists (name, phi) ->
        mk_exists ~name:name (go (depth + 1) phi)
      | `Eq (x, y) -> mk_eq x y
      | `Neq (x, y) -> mk_neq x y
      | `T -> mk_true
      | `F -> mk_false
    in
    mk_exists (go 0 phi)

  let concrete_post pa phi (letter,i) =
    match F.destruct (post pa phi letter) with
    | `Exists (_, psi) ->
      let f = function
        | 0 -> Const i
        | _ -> assert false
      in
      F.simplify (F.var_substitute f psi)
    | `F -> mk_false
    | `T -> mk_true
    | _ -> assert false

  let accepting_formula pa phi =
    let alg = function
      | `And (x, y) -> x && y
      | `Or (x, y) -> x || y
      | `Atom (rel, _) -> PSet.mem rel pa.accepting
      | `T -> true
      | `F -> false
      | `Forall (_, _) | `Exists (_, _) | `Eq (_, _) | `Neq (_, _) ->
        invalid_arg "accepting_formula: argument must be free of quantifiers \
                     and equalities"
    in
    eval alg phi

  let mem pa word =
    let universe =
      List.fold_left (fun m (_, k) -> max m k) 1 word
    in
    let start =
      F.instantiate_quantifiers
        pa.initial
        (BatList.of_enum (1 -- universe))
    in
    List.fold_right
      (fun (letter, i) phi -> concrete_post pa phi (letter, i))
      word
      start
    |> accepting_formula pa

  let pp_formula phi = F.pp P.pp Format.pp_print_int phi

  let pp formatter pa =
    let free_name i = Char.escaped (Char.chr (i + (Char.code 'i'))) in
    Format.fprintf formatter "start: %a.@\n" pp_formula pa.initial;
    if PSet.is_empty pa.accepting then
      Format.pp_print_string formatter "final: none.@\n"
    else
      Format.fprintf formatter "final: %a.@\n"
        (ArkUtil.pp_print_enum P.pp) (PSet.enum pa.accepting);
    vocabulary pa |> BatEnum.iter (fun (p, k) ->
        let arg_names =
          (0 -- (k-1)) /@ free_name |> BatList.of_enum
        in
        pa.alphabet |> LetterSet.enum |> BatEnum.iter (fun letter ->
            let rhs =
              transition pa p letter
              (* Constant symbols shouldn't exist *)
              |> F.substitute undefined
              |> F.var_substitute (fun i ->
                  if i = 0 then Const (free_name k)
                  else Const (free_name (k - 1))
                )
            in
            Format.fprintf formatter "%a(%a) --( %a : %s )-> %a.@\n"
              P.pp p
              (pp_print_list Format.pp_print_string) arg_names
              A.pp letter
              (free_name k)
              (F.pp P.pp Format.pp_print_string) rhs
          );
        Format.pp_print_newline formatter ()
      )

  module AHT = BatHashtbl.Make(struct
      type t = atom
      let hash (p, args) = Hashtbl.hash (P.hash p, args)
      let equal (p, pargs) (q, qargs) = P.equal p q && pargs = qargs
    end)

  let rec pp_ground_formula prop formatter phi =
    let open F in
    let open Format in
    match destruct_flatten phi with
    | `And conjuncts ->
      fprintf formatter "(@[%a@])"
        (pp_print_list
           ~pp_sep:(fun formatter () -> fprintf formatter "@ & ")
           (pp_ground_formula prop))
        conjuncts
    | `Or disjuncts ->
      fprintf formatter "(@[%a@])"
        (pp_print_list
           ~pp_sep:(fun formatter () -> fprintf formatter "@ | ")
           (pp_ground_formula prop))
        disjuncts
    | `Atom (p, tuple) ->
      let lower = function
        | Const k -> k
        | Var i -> assert false
      in
      pp_print_int formatter (prop (p, (List.map lower tuple)))
    | `T -> pp_print_string formatter "true"
    | `F -> pp_print_string formatter "false"
    | _ -> assert false

  let pp_ground size formatter pa =
    let open Format in
    let mk_tuples k =
      ArkUtil.tuples (BatList.of_enum ((1 -- k) /@ (fun _ -> (1 -- size))))
    in
    let props = AHT.create 991 in
    let next = ref (-1) in
    let (pp_bit_rep, bits) =
      let next = ref (-1) in
      let ht = Hashtbl.create 991 in
      BatEnum.iter (fun (letter,i) ->
          incr next; Hashtbl.add ht (letter,i) (!next)
        ) (ArkUtil.cartesian_product (LetterSet.enum pa.alphabet) (1 -- size));
      let nb_bits =
        let rec lg index n =
          if n = 0 then index else lg (index + 1) (n / 2)
        in
        lg 0 (!next)
      in

      let pp_bit_rep formatter (letter, k) =
        let rec go index id =
          let p = "p" ^ (string_of_int index) in
          if index == nb_bits then []
          else if id mod 2 = 1 then p::(go (index + 1) (id / 2))
          else ("!" ^ p)::(go (index + 1) (id / 2))
        in
        pp_print_list
          ~pp_sep:(fun formatter () -> fprintf formatter "@ & ")
          pp_print_string
          formatter
          (go 0 (Hashtbl.find ht (letter, k)))
      in
      (pp_bit_rep, nb_bits)
    in
    let get_prop_id (p, tuple) =
      try AHT.find props (p, tuple)
      with Not_found ->
        incr next;
        AHT.add props (p, tuple) (!next);
        !next
    in
    fprintf formatter "(@\n @[";
    fprintf formatter "automaton_type = \"sAFW\",@\n";
    vocabulary pa |> BatEnum.iter (fun (p, k) ->
        mk_tuples k |> BatEnum.iter (fun tuple ->
            ignore (get_prop_id (p, tuple))
          )
      );
    fprintf formatter "locations = [%a],@\n"
      (ArkUtil.pp_print_enum Format.pp_print_int)
      (0 -- (AHT.length props - 1));
    fprintf formatter "propositions = [%a],@\n"
      (ArkUtil.pp_print_enum
         (fun formatter i -> fprintf formatter "\"p%d\"" i))
      (0 -- (bits - 1));
    fprintf formatter "initial_constraint = \"%a\",@\n"
      (pp_ground_formula get_prop_id)
      ((F.instantiate_quantifiers
          pa.initial
          (BatList.of_enum (1 -- size)))
       |> F.simplify);
    let pp_tr formatter (p, tuple) =
      let pp_atr formatter (letter, k) =
        let rhs =
          F.instantiate_quantifiers
            ~env:(k::tuple)
            (transition pa p letter)
            (BatList.of_enum (1 -- size))
          |> F.simplify
        in
        match F.destruct rhs with
        | `F -> pp_print_string formatter "false"
        | _ ->
          fprintf formatter "%a@ & %a"
            pp_bit_rep (letter, k)
            (pp_ground_formula get_prop_id) rhs
      in
      fprintf formatter "%d : \"\"\"%a\"\"\""
        (get_prop_id (p, tuple))
        (ArkUtil.pp_print_enum
           ~pp_sep:(fun formatter () -> fprintf formatter "@ | ")
           pp_atr)
        (ArkUtil.cartesian_product (LetterSet.enum pa.alphabet) (1 -- size))
    in
    fprintf formatter "transition_function = {@\n  %a@\n},@\n"
      (ArkUtil.pp_print_enum
         ~pp_sep:(fun formatter () -> fprintf formatter "@\n,")
         pp_tr)
      ((vocabulary pa)
       /@ (fun (p, k) -> mk_tuples k /@ (fun tup -> (p, tup)))
       |> BatEnum.concat);

    fprintf formatter "accepting_locations = [%a]@\n"
      (ArkUtil.pp_print_enum Format.pp_print_int)
      (vocabulary pa |> BatEnum.filter_map (fun (p, k) ->
           if PSet.mem p pa.accepting then
             Some (mk_tuples k /@ (fun tuple -> get_prop_id (p, tuple)))
           else
             None) |> BatEnum.concat);
    fprintf formatter "@]@\n)@\n"
    
  (* A configuration is accepting if it contains only accepting predicates *)
  let accepting pa config =
    BatEnum.for_all (fun (x,_) -> PSet.mem x pa.accepting) (Config.props config)

  exception No_succs
  let succs pa config (letter, i) =
    let succ_size = max (Config.universe_size config) i in
    let next_prop (head, args) =
      let rhs = transition pa head letter in
      let min_models = Config.min_models ~env:(i::args) succ_size rhs in
      if BatEnum.is_empty min_models then begin
        (* logf ~level:`trace "   %a has no successors" pp_atom (head, args);*)
        raise No_succs
      end;
      min_models
    in
    let combine x y =
      ArkUtil.cartesian_product x y /@ (uncurry Config.union)
    in
    try
      Config.props config /@ next_prop
      |> BatEnum.reduce combine
    with No_succs -> BatEnum.empty ()

  let pred pa config (letter, i) =
    let universe = Config.universe_size config in
    vocabulary pa
    /@ (fun (p, k) ->
        BatList.of_enum ((1 -- k) /@ (fun _ -> (1 -- universe)))
        |> ArkUtil.tuples
        |> BatEnum.filter_map (fun tuple ->
            if Config.models
                ~env:(i::tuple)
                config
                (transition pa p letter)
            then
              Some (p, tuple)
            else
              None
          )
        |> Config.make ~size:universe)
    |> BatEnum.fold Config.union (Config.empty universe)

  let successors pa config index =
    let combine_one (letters, succ) (letters', succ') =
      let combined_letters = LetterSet.inter letters letters' in
      if LetterSet.is_empty combined_letters then None
      else Some (combined_letters, Config.union succ succ')
    in
    let combine transitions transitions' =
      List.concat
        (List.map (fun (letters, succ) ->
             BatList.filter_map (combine_one (letters, succ)) transitions')
            transitions)
    in
    let succ_size = max (Config.universe_size config) index in
    Config.props config
    /@ (fun (q, tuple) ->
        let f (letter_set, rhs) =
          Config.min_models ~env:(index::tuple) succ_size rhs
          /@ (fun m -> (letter_set, m))
          |> BatList.of_enum
        in
        List.concat (List.map f (transitions pa q)))
    |> BatEnum.fold combine [(alphabet pa, Config.empty succ_size)]
    |> BatList.enum
    |> BatEnum.map (fun (letters, config) -> (LetterSet.choose letters, config))
end

module MakeReachabilityGraph (A : sig
    type t
    type letter
    type config
    type predicate
    module Config : Struct.S with type predicate = predicate
                              and type t = config
    val pp_letter : Format.formatter -> letter -> unit
    val vocabulary : t -> (predicate * int) BatEnum.t
    val successors : t -> config -> int -> (letter * config) BatEnum.t
  end)
  (PredicateTreeMake : functor (B : SearchTree.Element) (C: SearchTree.Element) ->
                       SearchTree.S with type baseSet = BatSet.Make(B).t and type elt = C.t) = struct
  open A
  type id = int
  module DA = BatDynArray

  (* Set of vertices, weighted by some heuristic value *)
  module Worklist = struct
    module H = BatHeap.Make(struct
        type t = int * int
        let compare (a,b) (c,d) =
          match compare a c with
          | 0 -> compare b d
          | r -> r
      end)
    type t = H.t
    let empty = H.empty
    let pick worklist =
      if worklist = H.empty then
        None
      else
        Some (H.find_min worklist, H.del_min worklist)
    let insert h v worklist =
      H.insert worklist (h, v)
  end

  module PredicateTree = PredicateTreeMake(Config.Predicate)(ArkUtil.Int)

  type arg =
    { mutable worklist : Worklist.t;
      pa : t;
      max_index : int;
      label : config DA.t;
      parent : ((letter * int * id) option) DA.t; (* Invariant: label & parent
                                                    should always have the
                                                    same length *)
      cover : (id,id) Hashtbl.t; (* partial maps a vertex v to a vertex u such
                                    that v is covered by u *)
      mutable searchTree : PredicateTree.t (* to ensure that covering is
                                              acyclic, searchTree should
                                              include only those vertices that
                                              have already been expanded. *)
    }

  let label arg vertex =
    let nb_vertex = DA.length arg.label in
    if 0 <= vertex && vertex < nb_vertex then
      DA.get arg.label vertex
    else 
      Log.invalid_argf "label: vertex %d does not exist" vertex

  module PSet = BatSet.Make(Config.Predicate)
  let make pa max_index =
    let preds pa =
      let f (p, ar) preds =
        PSet.add p preds
      in BatSet.fold f (BatSet.of_enum (A.vocabulary pa)) PSet.empty
    in
    let arg =
    { worklist = Worklist.empty;
      pa = pa;
      max_index = max_index;
      label = DA.make 2048;
      parent = DA.make 2048;
      cover = Hashtbl.create 991;
      searchTree = PredicateTree.empty (preds pa) (fun _ -> PSet.empty)
    }
    in
    arg.searchTree <- PredicateTree.empty (preds pa) (fun x -> PSet.of_enum (Config.preds (label arg x)));
    arg

  let parent arg vertex =
    let nb_vertex = DA.length arg.parent in
    if 0 <= vertex && vertex < nb_vertex then
      DA.get arg.parent vertex
    else 
      Log.invalid_argf "parent: vertex %d does not exist" vertex

  let rec path_to_root arg v path =
    match parent arg v with
    | Some (a,i,p) ->
      path_to_root arg p ((a,i)::path)
    | None -> List.rev path

  let rec print_path_to_root arg v =
    logf "%a" Config.pp (label arg v);
    match parent arg v with
    | Some (a,i,p) ->
      logf "  <%a : %d>" pp_letter a i;
      print_path_to_root arg p
    | None -> ()

  (* Heuristic value = max thread id on path to v *)
  let hval arg v =
    let rec go hval v =
      match parent arg v with
      | Some (_, i, p) ->
        go (max i hval) p
      | None -> hval
    in
    go 0 v

  let add_worklist arg v =
    arg.worklist <- Worklist.insert (hval arg v) v arg.worklist

  let pick_worklist arg =
    match Worklist.pick arg.worklist with
    | None -> None
    | Some ((_, v), worklist) ->
      arg.worklist <- worklist;
      Some v

  (* Add a new vertex to an ARG, with a given parent and label, and add it to
     the worklist.  Returns an identifier for that vertex. *)
  let add_vertex arg ?(parent=None) label =
    let id = DA.length arg.label in
    DA.add arg.label label;
    DA.add arg.parent parent;
    add_worklist arg id;
    id

  let expand arg vertex =
    let config = label arg vertex in
    logf ~level:`trace ~attributes:[`Blue;`Bold] "Expanding vertex:";
    logf ~level:`trace "@[[%d] %a" vertex Config.pp config;
    PredicateTree.insert arg.searchTree vertex;
    let add_succ k (letter, config) =
      let succ_vertex =
        add_vertex arg ~parent:(Some (letter, k, vertex)) config
      in
      logf ~level:`trace " --(%d : %a)->@\n  @[[%d] %a@]"
        k
        pp_letter letter
        succ_vertex
        Config.pp config
    in
    let max_index =
      if arg.max_index >= 0 then
        min arg.max_index (Config.universe_size config + 1)
      else
        (Config.universe_size config + 1)
    in
    (1 -- max_index)
    |> BatEnum.iter (fun i ->
        BatEnum.iter (add_succ i) (successors arg.pa config i));
    logf ~level:`trace ~attributes:[`Blue;`Bold] "@]"

  (* u covers v *)
  let add_cover arg u v =
    Hashtbl.add arg.cover v u

  (* Given a vertex v, try to find another vertex u which covers v.  If such a
     vertex is found, add the cover relation and return true.  Only look at
     ancestors of v in the ARG. *)
  let close_ancestor arg vertex =
    let config = label arg vertex in
    let rec find_covering_ancestor v =
      match parent arg v with
      | Some (a,i,p) ->
        if Config.embeds (label arg p) config then begin
          add_cover arg p vertex;
          logf ~level:`trace ~attributes:[`Green;`Bold] "Covered vertex:";
          logf ~level:`trace " [%d] %a" vertex Config.pp config;
          logf ~level:`trace "by ancestor@\n [%d] %a" p Config.pp (label arg p);
          true
        end else find_covering_ancestor p
      | None -> false
    in
    find_covering_ancestor vertex

  (* Same as close_ancestor, except search through all vertices with lower
     id's *)
  let close_all arg vertex =
    let config = label arg vertex in
    let rec find_cover u =
      if u >= vertex then
        false
      else if Config.embeds (DA.get arg.label u) config then
        begin
          add_cover arg u vertex;
          logf ~level:`trace ~attributes:[`Green;`Bold]
            "Covered vertex: [%d] %a"
            vertex
            Config.pp config;
          logf ~level:`trace " by [%d] %a" u Config.pp (label arg u);
          true
        end
      else
        find_cover (u + 1)
    in
    find_cover 0

  let close_all arg vertex =
    let embeds x y = Config.embeds (label arg x) (label arg y) in
    match PredicateTree.covered embeds arg.searchTree vertex with
      None -> false
    | Some u ->
       begin
         let config = label arg vertex in
         add_cover arg u vertex;
         logf ~level:`trace ~attributes:[`Green;`Bold]
           "Covered vertex: [%d] %a"
           vertex
           Config.pp config;
         logf ~level:`trace " by [%d] %a" u Config.pp (label arg u);
         true
       end
end

(* Signature of MakeEmpty Module (when applied to an A and PredicateTreeMake module) *)
module type MakeEmptySig = sig
  type solver
  type pa
  type predicate
  type formula
  type letter
  type letter_set
  val pp : Format.formatter -> solver -> unit
  val mk_solver : pa -> solver
  val conjoin_transition : solver -> predicate -> letter_set -> formula -> unit
  val add_predicate : solver -> predicate -> int -> unit
  val add_accepting_predicate : solver -> predicate -> int -> unit
  val mem_vocabulary : solver -> predicate -> bool
  val find_word : ?max_index:int -> solver -> ((letter * int) list) option
  val alphabet : solver -> letter_set
  val vocabulary : solver -> (predicate * int) BatEnum.t
end

module MakeEmpty (A : sig
    type t
    type letter
    type letter_set
    type config
    type predicate
    type formula = (predicate, int) PaFormula.formula
    module Config : Struct.S with type predicate = predicate
                              and type t = config
    module LetterSet : sig
      type t = letter_set
      val choose : t -> letter
    end
    val pp_letter : Format.formatter -> letter -> unit
    val alphabet : t -> letter_set
    val successors : t -> config -> int -> (letter * config) BatEnum.t
    val accepting : t -> config -> bool
    val initial : t -> formula
    val conjoin_transition : t -> predicate -> letter_set -> formula -> unit
    val add_transition : t -> predicate -> letter_set -> formula -> unit
    val add_predicate : t -> predicate -> int -> unit
    val add_accepting : t -> predicate -> unit
    val mem_vocabulary : t -> predicate -> bool
    val vocabulary : t -> (predicate * int) BatEnum.t
    val pp : Format.formatter -> t -> unit
  end)
  (PredicateTreeMake : functor (B : SearchTree.Element) (C: SearchTree.Element) ->
                       SearchTree.S with type baseSet = BatSet.Make(B).t and type elt = C.t) =
  struct
  open A

  module Arg = MakeReachabilityGraph(A)(PredicateTreeMake)

  (* Trivial incremental solver: just re-run the emptiness query from
     scratch *)
  type solver = A.t
  type pa = A.t
  type predicate = A.predicate
  type formula = A.formula
  type letter = A.letter
  type letter_set = A.letter_set


  let mk_solver pa = pa
  let pp = A.pp

  let add_predicate pa predicate arity =
    A.add_predicate pa predicate arity;
    A.add_transition pa predicate (A.alphabet pa) PaFormula.mk_true

  let add_accepting_predicate pa predicate arity =
    add_predicate pa predicate arity;
    A.add_accepting pa predicate

  let conjoin_transition = A.conjoin_transition

  let mem_vocabulary = A.mem_vocabulary

  let alphabet = A.alphabet

  let vocabulary = A.vocabulary

  let find_word ?(max_index=(-1)) pa =
    let rec fix arg =
      match Arg.pick_worklist arg with
      | Some v ->
        if accepting pa (Arg.label arg v) then begin
            Arg.print_path_to_root arg v;
            Some (Arg.path_to_root arg v [])
        end else begin
          if not (Arg.close_all arg v) then
            Arg.expand arg v;
          fix arg
        end
      | None -> None
    in
    let arg = Arg.make pa max_index in

    (* Add initial configurations to the ARG *)
    Config.min_models 1 (initial pa) |> BatEnum.iter (fun config ->
           ignore (Arg.add_vertex arg config));

    fix arg
end

module MakeBounded (A : S) (PredicateTreeMake : functor (B : SearchTree.Element) (C: SearchTree.Element) ->
                                                SearchTree.S with type baseSet = BatSet.Make(B).t and type elt = C.t) = struct
  open A

  module Arg = MakeReachabilityGraph(A)(PredicateTreeMake)

  (* Find a reachable configuration that satisfies the predicate p *)
  let bounded_search pa size p =
    let rec fix arg =
      match Arg.pick_worklist arg with
      | Some v ->
        if p (Arg.label arg v) then begin
            Arg.print_path_to_root arg v;
            Some (Arg.path_to_root arg v [])
        end else begin
          if not (Arg.close_all arg v) then
            Arg.expand arg v;
          fix arg
        end
      | None -> None
    in
    let arg = Arg.make pa size in

    (* Add initial configurations to the ARG *)
    Config.min_models size (initial pa) |> BatEnum.iter (fun config ->
        ignore (Arg.add_vertex arg config));

    fix arg

  let bounded_empty pa size = bounded_search pa size (accepting pa)
  let bounded_invariant pa size phi =
    bounded_search pa size (not % flip Config.models phi)
end
