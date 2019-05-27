%{
  open Pv_ast
%}

(* Keywords *)
%token AMONG
%token CHANNEL
%token CHOICE
%token CLAUSES
%token CONST
%token DEF
%token DIFF
%token DO
%token ELIMTRUE
%token ELSE
%token EQUATION
%token EQUIVALENCE
%token EVENT
%token EXPAND
%token FAIL
%token FORALL
%token FREE
%token FUN
%token GET
%token IF
%token IMPLEMENTATION
%token IN
%token INJ_EVENT
%token INSERT
%token LET
%token LETFUN
%token NEW
%token NONINTERF
%token NOT
%token NOUNIF
%token OR
%token OTHERWISE
%token OUT
%token PARAM
%token PHASE
%token PRED
%token PROBA
%token PROCESS
%token PROOF
%token PUBLIC_VARS
%token PUTBEGIN
%token QUERY
%token REDUC
%token SECRET
%token SET
%token SUCHTHAT
%token SYNC
%token TABLE
%token THEN
%token TYPE
%token WEAKSECRET
%token YIELD

%left AMONG
%left CHANNEL
%left CHOICE
%left CLAUSES
%left CONST
%left DEF
%left DIFF
%left DO
%left ELIMTRUE
%left ELSE
%left EQUATION
%left EQUIVALENCE
%left EVENT
%left EXPAND
%left FAIL
%left FORALL
%left FREE
%left FUN
%left GET
%left IF
%left IMPLEMENTATION
%left IN
%left INJ_EVENT
%left INSERT
%left LET
%left LETFUN
%left NEW
%left NONINTERF
%left NOT
%left NOUNIF
%left OR
%left OTHERWISE
%left OUT
%left PARAM
%left PHASE
%left PRED
%left PROBA
%left PROCESS
%left PROOF
%left PUBLIC_VARS
%left PUTBEGIN
%left QUERY
%left REDUC
%left SECRET
%left SET
%left SUCHTHAT
%left SYNC
%left TABLE
%left THEN
%left TYPE
%left WEAKSECRET
%left YIELD

%token NULL_PROC
%left  NULL_PROC

%token LEFT_PAREN
%token RIGHT_PAREN
%token COMMA
%token LEFT_BRACK
%token RIGHT_BRACK
%token COLON
%token SEMICOLON

%left LEFT_PAREN
%left RIGHT_PAREN
%left COMMA
%left LEFT_BRACK
%left RIGHT_BRACK
%left COLON
%left SEMICOLON

%token EQ
%token NEQ
%token AND
%left EQ
%left NEQ
%left AND

%token PARALLEL
%left  PARALLEL

%token REPLICATE
%left  REPLICATE

%token <string> NAME

%token EOF

%start <Pv_ast.decl list> parse_decls

%%

parse_decls:
  | l = list(decl); EOF { l }

decl:
  | PROCESS; p = process { Decl_proc p }

process:
  | NULL_PROC                                     { Proc_null }
  | p1 = process; PARALLEL; p2 = process          { Proc_parallel(p1, p2) }
  | REPLICATE; p = process                        { Proc_replicate p }
  | NEW; name = NAME; COLON; ty = NAME
  | NEW; name = NAME; COLON; ty = NAME; SEMICOLON
    { Proc_new { new_name = { name; ty }
               ; next = Proc_null } }
  | NEW; name = NAME; COLON; ty = NAME; SEMICOLON; next = process
    { Proc_new { new_name = { name; ty }
               ; next } }
  | IN; LEFT_PAREN; channel = term; COMMA; message = pattern; RIGHT_PAREN
  | IN; LEFT_PAREN; channel = term; COMMA; message = pattern; RIGHT_PAREN; SEMICOLON
    { Proc_in { channel; message; next = Proc_null } }
  | IN; LEFT_PAREN; channel = term; COMMA; message = pattern; RIGHT_PAREN; SEMICOLON; next = process
    { Proc_in { channel; message; next } }
  | OUT; LEFT_PAREN; channel = term; COMMA; message = term; RIGHT_PAREN
  | OUT; LEFT_PAREN; channel = term; COMMA; message = term; RIGHT_PAREN; SEMICOLON
    { Proc_out { channel, message; next = Proc_null } }
  | OUT; LEFT_PAREN; channel = term; COMMA; message = term; RIGHT_PAREN; SEMICOLON; next = process
    { Proc_out { channel, message; next } }

term:
  | name = NAME { T_name name }
  | LEFT_PAREN; terms = separated_list(COMMA, enriched_term); RIGHT_PAREN
    { T_tuple terms }
  | f = NAME; LEFT_PAREN; args = separated_list(COMMA, enriched_term); RIGHT_PAREN
    { T_app (f, args) }
  | t1 = term; EQ; t2 = term
    { T_binaryOp (Eq, t1, t2) }
  | t1 = term; NEQ; t2 = term
    { T_binaryOp (Neq, t1, t2) }
  | t1 = term; AND; t2 = term
    { T_binaryOp (And, t1, t2) }
  | t1 = term; OR; t2 = term
    { T_binaryOp (Or, t1, t2) }
  | NOT; LEFT_PAREN; t = term; RIGHT_PAREN
    { T_unaryOp (Not, t) }

pattern:
  | name = NAME; COLON; ty = NAME { Pat_typed_var { name; ty } }
  | name = NAME                   { Pat_var name }
  | LEFT_PAREN; l = separated_list(COMMA, pattern); RIGHT_PAREN
    { Pat_tuple l }
  | EQ; t = term                  { Pat_eq t }

enriched_term:
  | name = NAME { ET_name name }
  | LEFT_PAREN; terms = separated_list(COMMA, enriched_term); RIGHT_PAREN
    { ET_tuple terms }
  | f = NAME; LEFT_PAREN; args = separated_list(COMMA, enriched_term); RIGHT_PAREN
    { ET_app (f, args) }
