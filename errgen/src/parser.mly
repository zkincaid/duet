 /* File parser.mly */

        %{
          open Ast;;
          open Ark;;
          open ArkPervasives;;
        %}

        %token EOF
        %token <Ark.ArkPervasives.QQ.t> REAL
        %token <string> VAR
        %token PLUS MINUS TIMES DIV
        %token TRUE FALSE 
        %token AND OR NOT
        %token EQ NE GT LT LE GE
        %token ASSIGN SEMI
        %token IF WHILE ELSE SKIP PRINT ASSERT ASSUME NONDET
        %token LPAREN RPAREN LBRACE RBRACE
        %left SEMI
        %left PLUS MINUS OR        /* lowest precedence */
        %left TIMES DIV AND         /* medium precedence */
        %nonassoc UMINUS NOT       /* highest precedence */
        %start main             /* the entry point */
        %type <Ast.prog_type> main
        %%
        main:
            prog EOF             {  
            $1}
        ;

        prog:
          stmt                   { Prog($1)  } 
        ;

        stmt:
                              {  Cmd Skip  }
         | SKIP                { Cmd Skip }
         |  VAR ASSIGN aexp       { Cmd (Assign($1,$3)) }
         |  stmt SEMI stmt         { Seq($1, $3) }
         |  IF LPAREN bexp RPAREN LBRACE stmt RBRACE ELSE LBRACE stmt RBRACE { Ite($3,$6,$10) }
         |  IF LPAREN bexp RPAREN LBRACE stmt RBRACE   { Ite($3,$6,Cmd Skip) }
         |  WHILE LPAREN bexp RPAREN LBRACE stmt RBRACE { While($3, $6, false) }
         |  ASSERT LPAREN bexp RPAREN   { Cmd (Assert($3)) }
         |  ASSUME LPAREN bexp RPAREN   { Cmd (Assume($3)) }
         |  PRINT LPAREN aexp RPAREN    { Cmd (Print($3)) }
             
        aexp:
            REAL                    { Real_const($1) }
          | VAR                     { Var_exp($1) }
          | LPAREN aexp RPAREN      { $2 }
          | aexp PLUS aexp          { Sum_exp($1, $3) }
          | aexp MINUS aexp         { Diff_exp($1, $3) }
          | aexp TIMES aexp         { Mult_exp($1, $3) }
          | aexp DIV aexp         { Div_exp($1, $3) }
          | MINUS aexp %prec UMINUS { Unneg_exp($2) }
          | NONDET LPAREN RPAREN    { Havoc_aexp }
        ;

        bexp:
             TRUE                   { Bool_const(true) }
          |  FALSE                  { Bool_const(false)}
          |  aexp GT aexp           { Gt_exp($1, $3) }
          |  aexp GE aexp           { Ge_exp($1, $3) }
          |  aexp LT aexp           { Lt_exp($1, $3) }
          |  aexp LE aexp           { Le_exp($1, $3) }
          |  aexp EQ aexp           { Eq_exp($1, $3) }
          |  aexp NE aexp           { Ne_exp($1, $3) }
          |  bexp OR bexp           { Or_exp($1, $3) }
          |  bexp AND bexp          { And_exp($1, $3) }
          |  NOT bexp               { Not_exp ($2) }
          |  NONDET LPAREN RPAREN   { Havoc_bexp }
        ;    
