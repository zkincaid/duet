open BatPervasives
open PaFormula
open Apak

let sep formatter () = Format.fprintf formatter ",@ "
let pp_print_list ?(pp_sep=sep) pp_elt formatter xs =
    ApakEnum.pp_print_enum ~pp_sep pp_elt formatter (BatList.enum xs)

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

module type S = sig
  type t
  type predicate
  type alpha
  type formula = (predicate, int) PaFormula.formula
  type config

  module Config : Struct.S with type predicate = predicate
                            and type t = config

  val pp : Format.formatter -> t -> unit
  val pp_alpha : Format.formatter -> alpha -> unit
  val pp_ground : int -> Format.formatter -> t -> unit
  val pp_formula : Format.formatter -> formula -> unit
  val make : alpha list -> predicate list -> formula -> t
  val add_transition : t -> predicate -> alpha -> formula -> unit
  val alphabet : t -> alpha BatEnum.t
  val vocabulary : t -> (predicate * int) BatEnum.t
  val initial : t -> formula
  val negate : t -> t
  val intersect : t -> t -> t
  val union : t -> t -> t
  val post : t -> formula -> alpha -> formula
  val concrete_post : t -> formula -> (alpha * int) -> formula
  val succs : t -> config -> (alpha * int) -> config BatEnum.t
  val pred : t -> config -> (alpha * int) -> config
(*
  val bounded_empty : t -> int -> ((alpha * int) list) option
  val bounded_invariant : t -> int -> formula -> ((alpha * int) list) option
*)
  val accepting_formula : t -> formula -> bool
  val accepting : t -> config -> bool
end

module Make (A : Sigma) (P : Predicate) = struct
  type predicate = P.t
  type alpha = A.t [@@deriving show]
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
    
  let accepting pa config =
    BatEnum.for_all (fun (x,_) -> PSet.mem x pa.accepting) (Config.props config)

  exception No_succs
  let succs pa config (alpha, i) =
    let succ_size = max (Config.universe_size config) i in
    let next_prop (head, args) =
      let rhs = find_transition pa head alpha in
      let min_models = Config.min_models ~env:(i::args) succ_size rhs in
      if BatEnum.is_empty min_models then begin
        (*        logf ~level:`trace "   %a has no successors" pp_atom (head, args);*)
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
end

module MakeReachabilityGraph (A : sig
    type t
    type alpha
    type config
    type predicate
    module Config : Struct.S with type predicate = predicate
                              and type t = config
    val pp_alpha : Format.formatter -> alpha -> unit
    val successors : t -> config -> (alpha * int * config) BatEnum.t
  end) = struct
  open A
  type id = int
  module DA = BatDynArray

  (* Set of vertices, weighted by some heuristic value *)
  module WVSet = Set.Make(struct
      type t = int * int
      let compare (a,b) (c,d) =
        match compare a c with
        | 0 -> compare b d
        | r -> r
    end)

  type arg =
    { mutable worklist : WVSet.t;
      pa : t;
      label : config DA.t;
      parent : ((alpha * int * id) option) DA.t; (* Invariant: label & parent
                                                    should always have the
                                                    same length *)
      cover : (id,id) Hashtbl.t (* partial maps a vertex v to a vertex u such
                                   that v is covered by u *)
    }

  let make pa =
    { worklist = WVSet.empty;
      pa = pa;
      label = DA.make 2048;
      parent = DA.make 2048;
      cover = Hashtbl.create 991 }

  let label arg vertex =
    let nb_vertex = DA.length arg.label in
    if 0 <= vertex && vertex < nb_vertex then
      DA.get arg.label vertex
    else 
      Log.invalid_argf "label: vertex %d does not exist" vertex

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
      logf "  <%a : %d>" pp_alpha a i;
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
    arg.worklist <- WVSet.add (hval arg v, v) arg.worklist

  let pick_worklist arg =
    if WVSet.is_empty arg.worklist then
      None
    else
      let (h, v) = WVSet.min_elt arg.worklist in
      arg.worklist <- WVSet.remove (h, v) arg.worklist;
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
    let add_succ (alpha, k, config) =
      let succ_vertex =
        add_vertex arg ~parent:(Some (alpha, k, vertex)) config
      in
      logf ~level:`trace " --(%d : %a)->@\n  @[[%d] %a@]"
        k
        pp_alpha alpha
        succ_vertex
        Config.pp config
    in
    successors arg.pa (label arg vertex) |> BatEnum.iter add_succ;
    logf ~level:`trace ~attributes:[`Blue;`Bold] "@]"

  (* u covers v *)
  let add_cover arg u v =
    assert (u < v);
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
          logf ~level:`trace ~attributes:[`Green;`Bold]
            "Covered vertex: [%d] %a"
            vertex
            Config.pp config;
          logf ~level:`trace " by ancestor [%d] %a" p Config.pp (label arg p);
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
end

module MakeEmpty (A : sig
    type t
    type alpha
    type config
    type predicate
    type formula = (predicate, int) PaFormula.formula
    module Config : Struct.S with type predicate = predicate
                              and type t = config
    val pp_alpha : Format.formatter -> alpha -> unit
    val alphabet : t -> alpha BatEnum.t
    val succs : t -> config -> (alpha * int) -> config BatEnum.t
    val accepting : t -> config -> bool
    val initial : t -> formula
  end) = struct
  open A

  module Arg = MakeReachabilityGraph(struct
      include A
      let successors pa config =
        ApakEnum.cartesian_product
          (alphabet pa)
          (1 -- (Config.universe_size config + 1))
        /@ (fun (alpha, k) ->
            succs pa config (alpha, k)
            /@ (fun s -> (alpha, k, s)))
        |> BatEnum.concat
    end)

  let empty pa =
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
    let arg = Arg.make pa in

    (* Add initial configurations to the ARG *)
    Config.min_models 1 (initial pa) |> BatEnum.iter (fun config ->
        ignore (Arg.add_vertex arg config));

    fix arg
end


module MakeBounded (A : S) = struct
  open A

  module Arg = MakeReachabilityGraph(struct
      include A
      let successors pa config =
        ApakEnum.cartesian_product
          (alphabet pa)
          (Config.universe config)
        /@ (fun (alpha, k) ->
            succs pa config (alpha, k)
            /@ (fun s -> (alpha, k, s)))
        |> BatEnum.concat
    end)

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
    let arg = Arg.make pa in

    (* Add initial configurations to the ARG *)
    Config.min_models size (initial pa) |> BatEnum.iter (fun config ->
        ignore (Arg.add_vertex arg config));

    fix arg

  let bounded_empty pa size = bounded_search pa size (accepting pa)
  let bounded_invariant pa size phi =
    bounded_search pa size (not % flip Config.models phi)

end
