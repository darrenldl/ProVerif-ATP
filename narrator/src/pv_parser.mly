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
  | NEW; name = NAME; COLON; ty = NAME; SEMICOLON
  | NEW; name = NAME; COLON; ty = NAME
    { Proc_new { new_name = { name; ty }
               ; next = Proc_null } }
  | NEW; name = NAME; COLON; ty = NAME; SEMICOLON; next = process
    { Proc_new { new_name = { name; ty }
               ; next } }

term:
  | name = NAME { Name name }

enriched_term:
  | name = NAME { Name name }
  | LEFT_PAREN; terms = separated_list(COMMA, enriched_term); RIGHT_PAREN
    { Tuple terms }
  | f = NAME; LEFT_PAREN; args = separated_list(COMMA, enriched_term); RIGHT_PAREN
    { App (f, args) }
