%{
open Srk
open PaFormula
open PredicateAutomata
open Patop

let pp_pos formatter pos =
  let open Lexing in
  Format.fprintf formatter "File \"%s\", line %d, position %d"
    pos.pos_fname
    pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

%}

%token EOF
%token <string> ID
%token <int> INT
%token AND OR EQ NEQ
%token FORALL EXISTS DOT COMMA COLON
%token START FINAL TRUE FALSE
%token LPAREN RPAREN
%token ARROWHEAD ARROWTAIL
%token IF THEN ELSE
%token LET IN
%left DOT
%left OR
%left AND
%start main
%type <Patop.A.t> main
%start main_formula
%type <(string, string) PaFormula.formula> main_formula
%type <(string, string) PaFormula.formula> ext_formula
%start word
%type <(string*int) list> word                      
%start cfa
%type <Patop.A.t> cfa
%%

main:
  | START; COLON; start = formula; DOT;
    FINAL; COLON; final = separated_list(COMMA, ID); DOT;
    transitions = list(transition);
    EOF
      {
        let module StringSet = Patop.PString.Set in
        let alphabet =
          let f set (_, (letter,_), _) = StringSet.add letter set in
          List.fold_left f StringSet.empty transitions
        in
        let start =
          PaFormula.substitute
            (BatPervasives.undefined ~message:"Start formula should be a sentence")
            start
        in
        let pa = A.make alphabet [] start [] in
        let add_transition ((lhs,lhs_params),(letter,index),rhs) =
          let rhs' =
            let params = index::lhs_params in
            let subst k =
              match BatList.index_of k params with
              | Some idx -> Var idx
              | None ->
                Log.errorf "Variable `%s' unbound in transition:" k;
                Log.errorf "  @[%s(%a) --( %s : %s )-> %a@]"
                  lhs
                  (pp_print_list Format.pp_print_string) lhs_params
                  letter
                  index
                  (PaFormula.pp Format.pp_print_string Format.pp_print_string)
                  rhs;
                failwith ("Unbound variable")
            in
            PaFormula.substitute subst rhs
          in
          if not (A.mem_vocabulary pa lhs) then
            A.add_predicate pa lhs (List.length lhs_params);
          A.add_transition pa lhs (StringSet.singleton letter) rhs'
        in
        List.iter add_transition transitions;
        List.iter (fun q ->
            if not (A.mem_vocabulary pa q) then
              A.add_predicate pa q 0;
            A.add_accepting pa q)
          final;
        pa
      }
;
main_formula:
  | LET; rel = ID; LPAREN; params = separated_list(COMMA, ID); RPAREN; EQ; rhs = ext_formula; IN; body = main_formula
     {
       let rhs' =
         let subst k =
           match BatList.index_of k params with
           | Some idx -> Var idx
           | None ->
             Log.errorf "Variable `%s' unbound in definition of `%s'" k rel;
             failwith ("Unbound variable")
         in
         PaFormula.substitute subst rhs
       in
       let replace_rel p k =
         if p = rel then
           rhs'
         else
           (let open BatPervasives in
           mk_atom p (BatList.of_enum ((0 -- (k - 1)) /@ (fun i -> Var i))))
       in
       PaFormula.atom_substitute replace_rel body
     }
  | phi = formula; EOF { phi }
;
ext_formula:
  | phi = formula { phi }
  | IF; x = term; EQ y = term; THEN; phi = formula; ELSE; psi = formula
    { mk_or (mk_and (mk_eq x y) phi) (mk_and (mk_neq x y) psi) }
;
formula:
  | LPAREN; phi = formula; RPAREN { phi }
  | rel = ID; LPAREN; args = params; RPAREN { mk_atom rel args }
  | phi = formula; AND; psi = formula { mk_and phi psi }
  | phi = formula; OR; psi = formula { mk_or phi psi }
  | FORALL; vars = list(ID); DOT; phi = formula
     { List.fold_right (fun x y -> forall x y) vars phi }
  | EXISTS; vars = list(ID); DOT; phi = formula
     { List.fold_right (fun x y -> exists x y) vars phi }
  | x = term; EQ; y = term { mk_eq x y }
  | x = term; NEQ; y = term { mk_neq x y }
  | TRUE { mk_true }
  | FALSE { mk_false }
;
term:
  | x = ID { Const x }
;
transition:
  | lhs = ID; LPAREN; lhs_params = separated_list(COMMA,ID); RPAREN;
   ARROWTAIL; letter = ID; COLON; index = ID; ARROWHEAD;
   rhs = ext_formula; DOT
     { ((lhs,lhs_params),(letter,index),rhs) }
;
params:
  p = separated_list(COMMA, term) { p }
;
word:
  | w = list(indexed_letter); EOF { w }
;
indexed_letter:
  | LPAREN; letter = ID; COLON; index = INT; RPAREN { (letter, index) }
;
cfa:
  | START; COLON; start = state; DOT; edges = list(edge); EOF {
     of_cfa start edges
  }
;
state:
  | id = ID { id }
  | id = INT { string_of_int id }
;
edge:
  | left = state; ARROWTAIL; letter = ID; ARROWHEAD; right = state; DOT
     { (left, letter, right) }
;
