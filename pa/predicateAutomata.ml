open BatPervasives
open PaFormula
open Apak

let pp_print_list = Apak.Putil.pp_print_list

include Log.Make(struct let name = "pa" end)

module type Sigma = sig
  type t
  val pp : Format.formatter -> t -> unit
  val hash : t -> int
  val equal : t -> t -> bool
end

module type Predicate = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module F = PaFormula

module Make (A : Sigma) (P : Predicate) = struct
  type predicate = P.t
  type alpha = A.t
  type formula = (P.t, int) F.formula
  type atom = P.t * int list [@@deriving ord]

  let pp_atom formatter (p,args) =
    Format.fprintf formatter "@[%a(%a)@]"
      P.pp p
      (ApakEnum.pp_print_enum Format.pp_print_int) (BatList.enum args)

  module PSet = BatSet.Make(P)
  module HT = BatHashtbl.Make(struct
      type t = P.t * A.t
      let equal (p, a) (q, b) = P.equal p q && A.equal a b
      let hash (p, a) = Hashtbl.hash (P.hash p, A.hash a)
    end)

  type t =
    { delta : formula HT.t;
      sigma : A.t list;
      accepting : PSet.t;
      initial : formula; }

  (* A configuration is a finite structure over the vocabulary of the PA. *)
  module Config = Struct.Make(P)
  type config = Config.t

  (* A configuration is accepting if it contains only accepting predicates *)
  let accept pa config =
    BatEnum.for_all (fun (x,_) -> PSet.mem x pa.accepting) (Config.props config)

  let initial pa = pa.initial

  let find_transition pa predicate alpha =
    try HT.find pa.delta (predicate, alpha)
    with Not_found -> mk_false

  let add_transition pa predicate alpha formula =
    try
      let old = HT.find pa.delta (predicate, alpha) in
      HT.replace pa.delta (predicate, alpha) (mk_or old formula)
    with Not_found -> HT.add pa.delta (predicate, alpha) formula

  let make sigma accepting initial =
    { delta = HT.create 991;
      sigma = sigma;
      accepting = PSet.of_enum (BatList.enum accepting);
      initial = initial }

  module PHT = BatHashtbl.Make(P)
  let vocabulary pa =
    let ht = PHT.create 991 in
    let add_predicate p arity =
      try
        if PHT.find ht p != arity then
          failwith "Predicate used with different arities"
      with Not_found -> PHT.add ht p arity
    in
    let add_formula phi =
      let f = function
        | `Atom (p, args) -> add_predicate p (List.length args)
        | _ -> ()
      in
      eval f phi
    in
    add_formula pa.initial;
    BatEnum.iter add_formula (HT.values pa.delta);
    PHT.enum ht

  let formula_predicates phi =
    let f = function
      | `Eq (_, _) | `Neq (_, _) -> PSet.empty
      | `Atom (p, _) -> PSet.singleton p
      | `Forall (_, x) | `Exists (_, x) -> x
      | `And (x, y) | `Or (x, y) -> PSet.union x y
      | `T | `F -> PSet.empty
    in
    eval f phi

  (* Get the set of all predicates which are used by a given PA *)
  let predicates pa =
    let formulas = HT.values pa.delta in
    BatEnum.push formulas pa.initial;
    BatEnum.fold
      (fun set phi -> PSet.union (formula_predicates phi) set)
      (PSet.of_enum (HT.keys pa.delta /@ fst))
      formulas

  let alphabet pa = BatList.enum pa.sigma

  let complete pa =
    ApakEnum.cartesian_product
      (PSet.enum (predicates pa))
      (BatList.enum pa.sigma)
    |> BatEnum.iter (fun (predicate, letter) ->
        if not (HT.mem pa.delta (predicate, letter))
        then HT.add pa.delta (predicate, letter) mk_false)


  let same_alphabet pa qa =
    BatList.for_all2 (fun a b -> A.equal a b) pa.sigma qa.sigma
      
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
      { delta = HT.copy pa.delta;
        sigma = pa.sigma;
        accepting = PSet.union pa.accepting qa.accepting;
        initial = mk_or pa.initial qa.initial }
    in
    qa.delta |> HT.iter (fun (q, alpha) rhs ->
        add_transition union q alpha rhs);
    union

  let intersect pa qa =
    if not (PSet.is_empty (PSet.inter (predicates pa) (predicates qa))) then
      invalid_arg "PredicateAutomata.union: input automata must have disjoint \
                   predicates";
    if not (PSet.is_empty (PSet.inter (predicates pa) (predicates qa))) then
      invalid_arg "PredicateAutomata.union: input automata must have equal \
                   alphabets";
    let inter =
      { delta = HT.copy pa.delta;
        sigma = pa.sigma;
        accepting = PSet.union pa.accepting qa.accepting;
        initial = mk_and pa.initial qa.initial }
    in
    qa.delta |> HT.iter (fun (q, alpha) rhs ->
        add_transition inter q alpha rhs);
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
    let predicates = predicates pa in
    let neg_pa =
      { delta = HT.create 991;
        sigma = pa.sigma;
        accepting = PSet.filter (not % flip PSet.mem pa.accepting) predicates;
        initial = negate_formula pa.initial; }
    in
    ApakEnum.cartesian_product (PSet.enum predicates) (BatList.enum pa.sigma)
    |> BatEnum.iter (fun (p, a) ->
        add_transition neg_pa p a (negate_formula (find_transition pa p a)));
    neg_pa

  let post pa phi alpha =
    let rec go depth phi =
      match F.destruct phi with
      | `And (phi, psi) -> mk_and (go depth phi) (go depth psi)
      | `Or (phi, psi) -> mk_or (go depth phi) (go depth psi)
      | `Atom (head, args) ->
        let rhs = find_transition pa head alpha in
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

  let concrete_post pa phi (alpha,i) =
    match F.destruct (post pa phi alpha) with
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
      (fun (alpha, i) phi -> concrete_post pa phi (alpha, i))
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
        (ApakEnum.pp_print_enum P.pp) (PSet.enum pa.accepting);
    vocabulary pa |> BatEnum.iter (fun (p, k) ->
        let arg_names =
          (0 -- (k-1)) /@ free_name |> BatList.of_enum
        in
        pa.sigma |> List.iter (fun alpha ->
            let rhs =
              find_transition pa p alpha
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
              A.pp alpha
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
      ApakEnum.tuples (BatList.of_enum ((1 -- k) /@ (fun _ -> (1 -- size))))
    in
    let props = AHT.create 991 in
    let next = ref (-1) in
    let (pp_bit_rep, bits) =
      let next = ref (-1) in
      let ht = Hashtbl.create 991 in
      BatEnum.iter (fun (alpha,i) ->
          incr next; Hashtbl.add ht (alpha,i) (!next)
        ) (ApakEnum.cartesian_product (BatList.enum pa.sigma) (1 -- size));
      let nb_bits =
        let rec lg index n =
          if n = 0 then index else lg (index + 1) (n / 2)
        in
        lg 0 (!next)
      in

      let pp_bit_rep formatter (alpha, k) =
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
          (go 0 (Hashtbl.find ht (alpha, k)))
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
      (ApakEnum.pp_print_enum Format.pp_print_int)
      (0 -- (AHT.length props - 1));
    fprintf formatter "propositions = [%a],@\n"
      (ApakEnum.pp_print_enum
         (fun formatter i -> fprintf formatter "\"p%d\"" i))
      (0 -- (bits - 1));
    fprintf formatter "initial_constraint = \"%a\",@\n"
      (pp_ground_formula get_prop_id)
      ((F.instantiate_quantifiers
          pa.initial
          (BatList.of_enum (1 -- size)))
       |> F.simplify);
    let pp_tr formatter (p, tuple) =
      let pp_atr formatter (alpha, k) =
        let rhs =
          F.instantiate_quantifiers
            ~env:(k::tuple)
            (find_transition pa p alpha)
            (BatList.of_enum (1 -- size))
          |> F.simplify
        in
        match F.destruct rhs with
        | `F -> pp_print_string formatter "false"
        | _ ->
          fprintf formatter "%a@ & %a"
            pp_bit_rep (alpha, k)
            (pp_ground_formula get_prop_id) rhs
      in
      fprintf formatter "%d : \"\"\"%a\"\"\""
        (get_prop_id (p, tuple))
        (ApakEnum.pp_print_enum
           ~pp_sep:(fun formatter () -> fprintf formatter "@ | ")
           pp_atr)
        (ApakEnum.cartesian_product (BatList.enum pa.sigma) (1 -- size))
    in
    fprintf formatter "transition_function = {@\n  %a@\n},@\n"
      (ApakEnum.pp_print_enum
         ~pp_sep:(fun formatter () -> fprintf formatter "@\n,")
         pp_tr)
      ((vocabulary pa)
       /@ (fun (p, k) -> mk_tuples k /@ (fun tup -> (p, tup)))
       |> BatEnum.concat);

    fprintf formatter "accepting_locations = [%a]@\n"
      (ApakEnum.pp_print_enum Format.pp_print_int)
      (vocabulary pa |> BatEnum.filter_map (fun (p, k) ->
           if PSet.mem p pa.accepting then
             Some (mk_tuples k /@ (fun tuple -> get_prop_id (p, tuple)))
           else
             None) |> BatEnum.concat);
    fprintf formatter "@]@\n)@\n"
    
  (* Emptiness ****************************************************************)
  module CHT = BatHashtbl.Make(Config)

  (* Reachability graph *)
  type rg =
    { mutable worklist : Config.t list;
      parent : ((A.t * int * Config.t) option) CHT.t;
      cover : Config.t CHT.t }

  let vertices rg = CHT.keys rg.parent

  let accepting pa config =
    BatEnum.for_all (fun (x,_) -> PSet.mem x pa.accepting) (Config.props config)

  exception No_succs
  let succs pa config (alpha, i) =
    let succ_size = max (Config.universe_size config) i in
    let next_prop (head, args) =
      let rhs = find_transition pa head alpha in
      let min_models = Config.min_models ~env:(i::args) succ_size rhs in
      if BatEnum.is_empty min_models then begin
        logf ~level:`trace "   %a has no successors" pp_atom (head, args);
        raise No_succs
      end;
      min_models
    in
    let combine x y =
      ApakEnum.cartesian_product x y /@ (uncurry Config.union)
    in
    try
      Config.props config /@ next_prop
      |> BatEnum.reduce combine
    with No_succs -> BatEnum.empty ()

  let pred pa config (alpha, i) =
    let universe = Config.universe_size config in
    vocabulary pa
    /@ (fun (p, k) ->
        BatList.of_enum ((1 -- k) /@ (fun _ -> (1 -- universe)))
        |> ApakEnum.tuples 
        |> BatEnum.filter_map (fun tuple ->
            if Config.models
                ~env:(i::tuple)
                config
                (find_transition pa p alpha)
            then
              Some (p, tuple)
            else
              None
          )
        |> Config.make ~size:universe)
    |> BatEnum.fold Config.union (Config.empty universe)

  let close_trivial rg pa config =
    CHT.mem rg.parent config

  let close_ancestor rg pa config parent =
    let rec find_covering_ancestor v =
      match CHT.find rg.parent v with
      | Some (a,i,p) ->
        if Config.embeds p config then begin
          CHT.add rg.cover config p;
          logf ~level:`trace ~attributes:[`Green;`Bold]
            "Covered vertex: %a"
            Config.pp config;
          logf ~level:`trace " by ancestor %a" Config.pp p;
          true
        end else find_covering_ancestor p
      | None -> false
    in
    find_covering_ancestor parent

  let close_all rg pa config =
    try
      let cover = BatEnum.find (flip Config.embeds config) (vertices rg) in
      CHT.add rg.cover config cover;
      logf ~level:`trace ~attributes:[`Green;`Bold] "Covered vertex: %a"
        Config.pp config;
      logf ~level:`trace " by %a" Config.pp cover;
      true
    with Not_found -> false

  exception Accepting of Config.t
  let expand rg pa config p =
    logf ~level:`trace ~attributes:[`Blue;`Bold] "Expanding vertex:";
    logf ~level:`trace "@[%a" Config.pp config;
    let add_succs (alpha, k) =
      logf ~level:`trace " + Action: <%d : %a>" k A.pp alpha;
      let succs = succs pa config (alpha, k) in
      let add_succ succ =
        if not (CHT.mem rg.parent succ) then begin
          if not (close_all rg pa succ) then begin
            rg.worklist <- succ::rg.worklist;
            logf ~level:`trace "   - Added successor: %a" Config.pp succ
          end;
          CHT.add rg.parent succ (Some (alpha, k, config));
          if p succ then raise (Accepting succ)
        end
      in
      BatEnum.iter add_succ succs
    in
    let result =
      ApakEnum.cartesian_product
        (BatList.enum pa.sigma)
        (Config.universe config)
      |> BatEnum.iter add_succs
    in
    logf ~level:`trace "@]";
    result

  let expand_interuniversal rg pa config p =
    logf ~level:`trace ~attributes:[`Blue;`Bold]
      "Expanding vertex [inter-universal]: %a" Config.pp config;
    let k = Config.universe_size config + 1 in
    BatList.enum pa.sigma |> BatEnum.iter (fun alpha ->
      logf ~level:`trace " + Action: <%d : %a>" k A.pp alpha;
      let succs = succs pa config (alpha, k) in
      let add_succ succ =
        if not (CHT.mem rg.parent succ) then begin
          if not (close_all rg pa succ) then begin
            rg.worklist <- succ::rg.worklist;
            logf ~level:`trace "   - Added successor: %a" Config.pp succ
          end;
          CHT.add rg.parent succ (Some (alpha, k, config));
          if p succ then raise (Accepting succ)
        end
      in
      BatEnum.iter add_succ succs)

  let rec path_to_root rg v path =
    match CHT.find rg.parent v with
    | Some (a,i,p) ->
      path_to_root rg p ((a,i)::path)
    | None -> List.rev path

  let rec print_path_to_root rg v =
    logf "%a" Config.pp v;
    match CHT.find rg.parent v with
    | Some (a,i,p) ->
      logf "  <%a : %d>" A.pp a i;
      print_path_to_root rg p
    | None -> ()

  (* Find a reachable configuration that satisfies the predicate p *)
  let bounded_search pa size p =
    let rec fix rg =
      match List.rev rg.worklist with
      | (config::rest) ->
        rg.worklist <- List.rev rest;
        expand rg pa config p;
        fix rg
      | [] -> ()
    in
    let rg =
      { worklist = BatList.of_enum (Config.min_models size pa.initial);
        parent = CHT.create 991;
        cover = CHT.create 991 }
    in
    List.iter (fun s -> CHT.add rg.parent s None) rg.worklist;
    let rec path_to_root v path =
      match CHT.find rg.parent v with
      | Some (a,i,p) ->
        path_to_root p ((a,i)::path)
      | None -> path
    in
    let rec print_path_to_root v =
      logf "%a" Config.pp v;
      match CHT.find rg.parent v with
      | Some (a,i,p) ->
        logf "  <%a : %d>" A.pp a i;
        print_path_to_root p
      | None -> ()
    in
    try
      let config = List.find p rg.worklist in
      logf "Accepting initial configuration:@\n%a" Config.pp config;
      Some []
    with Not_found ->
      try
        (fix rg); None
      with Accepting v ->
        (logf "Accepting path:";
         print_path_to_root v;
         Some (path_to_root v []))

  let bounded_empty pa size = bounded_search pa size (accepting pa)
  let bounded_invariant pa size phi =
    bounded_search pa size (not % flip Config.models phi)

  let empty pa =
    let accept = accepting pa in
    let rec fix rg =
      match List.rev rg.worklist with
      | (config::rest) ->
        rg.worklist <- List.rev rest;
        expand rg pa config accept;
        expand_interuniversal rg pa config accept;
        fix rg
      | [] -> ()
    in
    let initial_configurations =
      BatList.of_enum (Config.min_models 1 pa.initial)
    in
    let rg =
      { worklist = [];
        parent = CHT.create 991;
        cover = CHT.create 991 }
    in
    try
      let config = List.find accept rg.worklist in
      logf "Accepting initial configuration:@\n%a" Config.pp config;
      Some []
    with Not_found ->
      try
        List.iter (fun s -> CHT.add rg.parent s None) initial_configurations;
        List.iter (fun c -> expand rg pa c accept) initial_configurations;
        fix rg;
        None
      with Accepting v ->
        (logf "Accepting path:";
         print_path_to_root rg v;
         Some (path_to_root rg v []))
end
