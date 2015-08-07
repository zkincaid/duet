%{
  open Printf
  open CbpAst	     
%}

/* Ocamlyacc Declarations */

%token <string> IDENTIFIER
%token <int> INTEGER
%token HAVOC TERNARY ASSIGN EQ NEQ IMPL SEMI
%token SINGLE_QUOTE
%token COMMA COLON
%token LPAREN RPAREN LBRACKET RBRACKET
%token AND OR NOT XOR
/* %token TILDE */
%token LANGLE RANGLE

%token RETURN GOTO SKIP
// %token DEAD /* ? */
%token DFS  /* ? */
%token WHILE DO OD
%token IF THEN ELSIF ELSE FI
%token DECL
%token BOOL VOID
%token ASSERT ASSUME
%token BEGIN END
%token ATOMIC_BEGIN ATOMIC_END
%token START_THREAD END_THREAD
// %token PRINT /* ? */
%token ENFORCE /* ? */
%token CONSTRAIN
%token SCHOOSE
%token ABORTIF /* ? */
// %token SYNC

%token EOF

/* %left AND OR EQ NEQ IMPL */

%type <CbpAst.program> program
%start program

%%

program:
  | vardec_list fun_list EOF
      { set_vars { vars=List.map mk_var $1;
		   funcs=$2 } }
;

/* Variable declarations */
vardec_list:
  | DECL id_list SEMI vardec_list { $2 @ $4 }
  | { [] }
;
id_list:
  | IDENTIFIER COMMA id_list { $1::$3 }
  | IDENTIFIER { [$1] }
;

/* Function definitions */
fun_list:
  | fundef fun_list { $1::$2 }
  | fundef { [$1] }
;
fundef:
  | fun_search_order
      fun_type IDENTIFIER LPAREN id_list0 RPAREN BEGIN
      vardec_list
      enforce
      abortif
      stmt_list
      END
      { { name    = $3;
	  returns = $2;
	  formals = List.map mk_var $5;
	  locals  = List.map mk_var $8;
	  body    = $11;

	  enforce = $9;
	  abortif = $10;
	  dfs     = $1 } }
;
/* number of returns */
fun_type:
  | BOOL LANGLE INTEGER RANGLE { $3 }
  | BOOL { 1 }
  | VOID { 0 }
;

/* ? */
fun_search_order:
  | DFS { true }
  | { false }
;
enforce:
  | ENFORCE exp SEMI { Some $2 }
  | { None }
;
abortif:
  | ABORTIF exp SEMI { Some $2 }
  | { None }
;

/* possibly empty id_list */
id_list0:
  | id_list { $1 }
  | { [] }
;

/* Statements */
stmt_list:
  | stmt_list_impl { $1 }
  | { [] }
;
stmt_list_impl:
  | IDENTIFIER COLON stmt_list_impl { (mk_lstmt [$1] Skip)::$3 }
  | stmt stmt_list { (mk_lstmt [] $1)::$2 }
;

/*
stmt_list:
  | lbl_stmt stmt_list { $1::$2 }
  | { [] }
;
lbl_stmt:
  | lbl_stmt_impl { let (lbls, stmt) = $1 in mk_lstmt lbls stmt }
;
lbl_stmt_impl:
  | IDENTIFIER COLON lbl_stmt_impl { let (lbls, stmt) = $3 in ($1::lbls, stmt) }
  | stmt { ([], $1) }
;
*/
stmt:
  | normal_stmt SEMI          { $1 }
  | WHILE exp DO stmt_list OD { While ($2, $4) }
  | if_stmt opt_semi          { $1 }
;
opt_semi:
  | SEMI {}
  | {}
;
normal_stmt:
  | START_THREAD start_thread_stmt { $2 }
  | END_THREAD { EndThread }
//  | SYNC { Sync }
  | ATOMIC_BEGIN { AtomicBegin }
  | ATOMIC_END { AtomicEnd }

//  | DEAD id_list { Dead $2 }
  | id_list ASSIGN exp_list constrain_opt 
      { Assign (List.map2 (fun x y -> ({ vname=x; vid=(-1) },y)) $1 $3, $4) }
  | ASSERT LPAREN exp RPAREN { Assert $3 }
  | ASSUME LPAREN exp RPAREN { Assume $3 }
//  | PRINT LPAREN exp_list RPAREN { Print $3 }
  | IDENTIFIER LPAREN exp_list0 RPAREN { Call ([], $1, $3) }
  | id_list ASSIGN IDENTIFIER LPAREN exp_list0 RPAREN
      { Call (List.map (fun v -> {vname=v; vid=(-1)}) $1, $3, $5) }

  | RETURN exp_list0 { Return $2 }
  | SKIP { Skip }
  | GOTO id_list { Goto $2 }
;

constrain_opt:
  | CONSTRAIN exp { Some $2 }
  | { None }
;

if_stmt:
  | IF exp THEN stmt_list elsif_list { If ($2, $4, $5) }
;
elsif_list:
  | FI { [] }
  | ELSE stmt_list FI { $2 }
  | ELSIF exp THEN stmt_list elsif_list { [mk_lstmt [] (If ($2, $4, $5))] }
;

start_thread_stmt:
  | GOTO IDENTIFIER { StartThreadGoto $2 }
  | IDENTIFIER LPAREN RPAREN { StartThread $1 } 
;

/* Expressions */
exp_list:
  | exp COMMA exp_list { $1::$3 }
  | exp { [$1] }
;
exp_list0:
  | exp_list { $1 }
  | { [] }
;
primary_exp:
  | const                 { $1 }
  | HAVOC                 { Havoc }
  | IDENTIFIER            { Var { vname = $1; vid = -1 } }
  | SINGLE_QUOTE IDENTIFIER { PrimeVar { vname = $2; vid = -1 } }
  | LPAREN exp RPAREN     { $2 }
  | SCHOOSE LBRACKET exp COMMA exp RBRACKET { Binop (Choose, $3, $5) }
;
const:
  | INTEGER { if $1 = 1 then True
	      else if $1 = 0 then False
	      else failwith "Non-Boolean constant" }
;
unary_exp:
  | primary_exp { $1 }
  | NOT primary_exp { Not $2 }
//  | TILDE primary_exp { Tilde $2 } /* ? */
;
eq_exp:
  | unary_exp { $1 }
  | eq_exp EQ unary_exp  { Binop (Eq, $1, $3) }
  | eq_exp NEQ unary_exp { Binop (Neq, $1, $3) }
;
and_exp:
  | eq_exp { $1 }
  | and_exp AND eq_exp { Binop (And, $1, $3) }
;
xor_exp:
  | and_exp { $1 }
  | xor_exp XOR and_exp { Binop (Xor, $1, $3) }
;
or_exp:
  | xor_exp { $1 }
  | or_exp OR xor_exp { Binop (Or, $1, $3) }
  | or_exp IMPL xor_exp { Binop (Implies, $1, $3) }
;
exp:
  | or_exp { $1 }
  | exp TERNARY exp COLON or_exp { Ternary ($1, $3, $5) }
;

%%
