(*pp camlp4of *)

open Camlp4.PreCast
open DatalogCore

let program = Gram.Entry.mk "program"

(* Declarations on if the relation should be read from / written to disk *)
type tuple_io = InputTuples | OutputTuples | RegularTuples

(* Non-Negation-Normal-Form logic statements;
   get transformed to NNF; don't get exposed *)
type unf_arith_expr =
    | UNFAtom of string
    | UNFUnion of unf_arith_expr * unf_arith_expr
    | UNFIntersection of unf_arith_expr * unf_arith_expr
    | UNFComplement of unf_arith_expr

let rec arith_of_unf e = match e with
    (* Push negations in *)
    | UNFComplement (UNFUnion (a, b)) ->
      arith_of_unf (UNFIntersection (UNFComplement a, UNFComplement b))
    | UNFComplement (UNFIntersection (a, b)) ->
      arith_of_unf (UNFUnion (UNFComplement a, UNFComplement b))
    | UNFComplement (UNFComplement a) -> arith_of_unf a
    (* Push conversion in *)
    | UNFUnion (a, b) ->
      BinaryOp (OperatorUnion, arith_of_unf a, arith_of_unf b)
    | UNFIntersection (a, b) ->
      BinaryOp (OperatorIntersection, arith_of_unf a, arith_of_unf b)
    (* Until we reach the tips, when we coalesce the negations if they are present *)
    | UNFAtom x -> Atom x
    | UNFComplement (UNFAtom x) -> NegatedAtom x

(* To aid type inference *)
let domaindecl_name domain =
  ":domain:"^domain

let create_domaindecls domains variables =
  List.map2
    (fun domain variable ->
      let domain_relation = domaindecl_name domain in
        Rel (domain_relation, [variable]))
    domains
    variables

(* Actual usage API *)
let program_with_declared_domains p =
  if false then p else
  let new_rules = List.map
    (fun (relname, formals, foralls, body) ->
      let body = 
        try
          let _, domains = (List.find (fun (rkey, _) -> rkey = relname) p.relations) in
          let domaindecls = create_domaindecls domains formals in
            domaindecls@body
        with Not_found -> body
      in
        (relname, formals, foralls, body))
    p.rules
  in
  let additional_relations =
    List.map (fun (d, _) -> (domaindecl_name d, [d])) p.domains
  in
  let additional_rules =
    List.map (fun (d,_) -> (domaindecl_name d, ["cast_param"], [], [])) p.domains
  in
  let _ = (print_endline "p_w_d_d 42") in
    {p with
      rules=additional_rules@new_rules;
      relations = additional_relations@p.relations}

type expr =
    | Relation of tuple_io * rel
    | Rule of rul
    | VarOrderDecl of (string*int) list
    | Domain of (string * int)
    | DomainPowerset of (string * string) (* Powerset of a previously defined domain *)

  EXTEND Gram
  GLOBAL: program;

  program:
    [ [ y = LIST1 expr ->
        program_with_declared_domains (
        List.fold_left (fun p r -> match r with
            | Relation (tupleio, ((x,y) as rel)) ->
                (* relation is only added for non-input tuples. *)
                let newp = {p with relations = rel::p.relations} in
                  (match tupleio with
                   | InputTuples -> {p with input_rels = x::p.input_rels}
                   | OutputTuples -> {newp with output_rels = x::newp.output_rels}
                   | RegularTuples -> newp);
            | Rule x -> {p with rules = x::p.rules}
            | VarOrderDecl order -> {p with varorder = p.varorder@order}
            | Domain d -> {p with domains = d::p.domains}
            | DomainPowerset (name, ofset) ->
                let domainpsets = ref p.domainpsets in
                let ofsetsize =
                  if (is_int ofset) then
                    (int_of_string ofset)
                  else let (_, size) = (List.find (function (name, _) -> name = ofset) p.domains) in begin
                      domainpsets := (name, ofset)::!domainpsets;
                      size
                  end
                in
                  {p with domains = (name, 1 lsl ofsetsize)::p.domains;
                          domainpsets = !domainpsets})
          { varorder = [];
            domains = [];
            domainpsets = [];
            relations = [];
            rules = [];
            input_rels = [];
            output_rels = []}
          y )] ];

  expr:
    [ [ ".";"bddvarorder"; vars = ident ->
            let vardescs = (Str.split (Str.regexp (Str.quote "_")) vars) in
            VarOrderDecl (List.map (fun s ->
                let name = Str.first_chars s (String.length s -1) in
		let num = Str.last_chars s 1 in
                  (name, int_of_string num))
                vardescs)
      | name = variable; size = INT -> Domain (name, int_of_string size)
      | name = variable; "P"; "("; baseset = variable ;")" -> DomainPowerset (name, baseset)
      | x = variable; "("; variable; ":"; first_y = variable; y = LIST0 [","; variable; ":"; t = variable -> t ]; ")"; iospec = tuple_io -> Relation (iospec, (x,first_y::y))
      | x = variable; "("; first_y = variable; y = LIST0 [","; v = variable -> v]; ")"; fvs = forall_vars; z = ruletail -> Rule (x, first_y::y, fvs, z)]];

  tuple_io:
    [[ decl = OPT declared_tuple_io -> match decl with
                               | None -> RegularTuples
                               | Some io -> io ]];

  declared_tuple_io:
    [[ "outputtuples" -> OutputTuples
     | "inputtuples" -> InputTuples ]];

  ruletail:
    [[ ":";"-"; z = body; "." -> z
     | "." -> []]];

  body:
    [ [ x = LIST1 inbody SEP "," -> x ]];

  forall_vars:
    [ [ vars = OPT forall_quant ->
        (match vars with
        | None -> []
        | Some vars -> vars) ] ];

  forall_quant:
    [ [ "{"; x = LIST0 variable SEP ","; "}" -> x ] ];

  inbody:
    [ [ x = variable ; "="; y = variable -> EQ (x,y)
      | x = variable ; "in"; y = arith_expr -> In (x,y) (* Should make EQ and IN, but "IN" is a camlp4 syntax. *)
      | x = variable ; "not"; "in"; y = arith_expr -> Nin (x,y)
      | x = variable ; "is"; y = arith_expr -> SetRelation (SetEq,x,y)
      | x = variable ; "is"; "<="; y = arith_expr -> SetRelation (SetSubset,x,y)
      | x = variable ; "is"; ">="; y = arith_expr -> SetRelation (SetSuperset,x,y)
      | x = variable ; y = lst_of_vars -> Rel (x,y)
      | "!"; x = variable ; y = lst_of_vars -> Neg (x,y) ] ];

  lst_of_vars:
    [ ["("; v = LIST1 variable SEP ","; ")" -> v]];

  arith_expr:
    [[ x = unf_arith_expr -> arith_of_unf x ]];

  unf_arith_expr:
    [[ "("; x = unf_arith_expr; ")" -> x ]
    |[ x = unf_arith_expr; "&"; y = unf_arith_expr -> UNFIntersection (x, y)
     | x = unf_arith_expr; "|"; y = unf_arith_expr -> UNFUnion (x, y)]
    |[ "~"; x = unf_arith_expr -> UNFComplement x
     | x = variable -> UNFAtom x]];

  variable:
    [[ x = LIDENT ;y = INT -> x ^ y
     | x = LIDENT -> x
     | x = INT -> x
     | x = UIDENT -> x]];
  
  ident:
    [[ x = LIDENT -> x | x = UIDENT -> x ]];

  END

let _loc = Loc.mk "<string>"

let lex string = Gram.filter (Gram.lex_string (Loc.mk "<string>") string)

let print_lex s =
        let stream = lex s in
        let get_token = (function () ->
                match Stream.next stream with
                | (t, _) -> (Gram.Token.to_string t)) in
        let tok = ref (get_token ()) in
        while !tok <> "EOI" do
                print_string (!tok^"\n");
                tok := get_token ()
        done

let parse string =
  try Gram.parse_string program (Loc.mk "<string>") string
  with
  | exn ->
      (print_endline string;
       Format.eprintf "%a@." Camlp4.ErrorHandler.print exn;
       raise exn)

