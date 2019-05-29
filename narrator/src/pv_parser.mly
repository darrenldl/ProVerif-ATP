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
%token GPT
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
%token LITERAL_OR
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
%token SECRPT
%token SPT
%token SUCHTHAT
%token SYNC
%token TABLE
%token THEN
%token TYPE
%token WEAKSECRPT
%token YIELD

%token GET

%token NULL_PROC

%token LEFT_PAREN
%token RIGHT_PAREN
%token COMMA
%token LEFT_BRACK
%token RIGHT_BRACK
%token COLON
%token SEMICOLON

%token EQ
%token NEQ
%token AND

%left EQ
%left NEQ
%left OR
%left AND

%token PARALLEL
%left  PARALLEL

%token REPLICATE
%left  REPLICATE

%token <string> NAME

%token EOF

%start <Pv_ast.decl list> parse_decls

%nonassoc PROC_NEW
%nonassoc PROC_IN
%nonassoc PROC_OUT
%nonassoc PROC_IF
%nonassoc PROC_LET
%nonassoc PROC_INSERT
%nonassoc PROC_EVENT
%nonassoc PROC_GET
%nonassoc PROC_PARALLEL

%nonassoc PT_NEW
%nonassoc PT_IF
%nonassoc PT_LET
%nonassoc PT_GET
%nonassoc PT_INSERT
%nonassoc PT_EVENT

%nonassoc IN
%nonassoc ELSE

%%

parse_decls:
  | l = list(decl); EOF { l }

options:
  |                                         { [] }
  | LEFT_BRACK; l = list(NAME); RIGHT_BRACK
    { l }

term:
  | name = NAME { T_name name }
  | LEFT_PAREN; terms = separated_nonempty_list(COMMA, term); RIGHT_PAREN
    { T_tuple terms }
  | f = NAME; LEFT_PAREN; args = separated_nonempty_list(COMMA, term); RIGHT_PAREN
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

pterm:
  | name = NAME { PT_name name }
  | LEFT_PAREN; terms = separated_nonempty_list(COMMA, pterm); RIGHT_PAREN
    { PT_tuple terms }
  | f = NAME; LEFT_PAREN; args = separated_nonempty_list(COMMA, pterm); RIGHT_PAREN
    { PT_app (f, args) }
  | t1 = pterm; EQ; t2 = pterm
    { PT_binaryOp (Eq, t1, t2) }
  | t1 = pterm; NEQ; t2 = pterm
    { PT_binaryOp (Neq, t1, t2) }
  | t1 = pterm; AND; t2 = pterm
    { PT_binaryOp (And, t1, t2) }
  | t1 = pterm; OR; t2 = pterm
    { PT_binaryOp (Or, t1, t2) }
  | NOT; LEFT_PAREN; t = pterm; RIGHT_PAREN
    { PT_unaryOp (Not, t) }
  | NEW; name = NAME; COLON; ty = NAME; SEMICOLON; next = pterm                                            %prec PT_NEW
    { PT_new { name = { name; ty }
             ; next } }
  | IF; cond = pterm; THEN; true_branch = pterm                                                    %prec PT_IF
    { PT_conditional { cond; true_branch; false_branch = None } }
  | IF; cond = pterm; THEN; true_branch = pterm; ELSE; false_branch = pterm
    { PT_conditional { cond; true_branch; false_branch = Some false_branch } }
  | LET; pat = pattern; EQ; t = pterm; IN; true_branch = pterm                                     %prec PT_LET
    { PT_eval { let_bind_pat = pat
              ; let_bind_term = t
              ; true_branch
              ; false_branch = None } }
  | LET; pat = pattern; EQ; t = pterm; IN; true_branch = pterm; ELSE; false_branch = pterm
    { PT_eval { let_bind_pat = pat
              ; let_bind_term = t
              ; true_branch
              ; false_branch = Some false_branch } }
  | INSERT; name = NAME; LEFT_PAREN; terms = separated_nonempty_list(COMMA, pterm); RIGHT_PAREN; SEMICOLON; next = pterm %prec PT_INSERT
    { PT_insert { name; terms; next } }
  | GET; name = NAME; LEFT_PAREN; pats = separated_nonempty_list(COMMA, pattern); RIGHT_PAREN                          %prec PT_GET
    { PT_get { name; pats; next = None } }
  | GET; name = NAME; LEFT_PAREN; pats = separated_nonempty_list(COMMA, pattern); RIGHT_PAREN; IN; true_branch = pterm %prec PT_GET
    { PT_get { name; pats; next = Some (true_branch, None) } }
  | GET; name = NAME; LEFT_PAREN; pats = separated_nonempty_list(COMMA, pattern); RIGHT_PAREN; IN; true_branch = pterm; ELSE; false_branch = pterm
    { PT_get { name; pats; next = Some (true_branch, Some false_branch) } }
  | EVENT; name = NAME
    { PT_event { name; terms = []; next = None } }
  | EVENT; name = NAME; SEMICOLON; next = pterm                                                                         %prec PT_EVENT
    { PT_event { name; terms = []; next = Some next } }
  | EVENT; name = NAME; LEFT_PAREN; terms = separated_nonempty_list(COMMA, pterm); RIGHT_PAREN
    { PT_event { name; terms; next = None } }
  | EVENT; name = NAME; LEFT_PAREN; terms = separated_nonempty_list(COMMA, pterm); RIGHT_PAREN; SEMICOLON; next = pterm %prec PT_EVENT
    { PT_event { name; terms; next = Some next } }

pattern:
  | name = NAME; COLON; ty = NAME { Pat_typed_var { name; ty } }
  | name = NAME                   { Pat_var name }
  | LEFT_PAREN; l = separated_nonempty_list(COMMA, pattern); RIGHT_PAREN
    { Pat_tuple l }
  | name = NAME; LEFT_PAREN; l = separated_nonempty_list(COMMA, pattern); RIGHT_PAREN
    { Pat_app (name, l) }
  | EQ; t = term                  { Pat_eq t }

mayfailterm:
  | t = term { MFT_term t }
  | FAIL     { MFT_fail }

typedecl:
  | ts = typedecl; COMMA; name = NAME; COLON; ty = NAME  { {name; ty} :: ts }

or_fail:
  | OR; FAIL { () }

failtypedecl:
  | ts = failtypedecl; COMMA; name = NAME; COLON; ty = NAME; fail = option(or_fail)
    { ({ name; ty }, match fail with None -> false | Some _ -> true) :: ts }

decl:
  | TYPE; name = NAME; opts = options
    { Decl_ty (name, opts) }
  | CHANNEL; l = nonempty_list(NAME)
    { Decl_channel l }
  | FREE; names = nonempty_list(NAME); COLON; ty = NAME; options = options
    { Decl_free { names; ty; options } }
  | CONST; names = nonempty_list(NAME); COLON; ty = NAME; options = options
    { Decl_const { names; ty; options } }
  | PROCESS; p = process
    { Decl_proc p }

process:
  | NULL_PROC                                     { Proc_null }
  | name = NAME; LEFT_PAREN; args = separated_nonempty_list(COMMA, pterm); RIGHT_PAREN
    { Proc_macro (name, args) }
  | LEFT_PAREN; p = process; RIGHT_PAREN
    { p }
  | p1 = process; PARALLEL; p2 = process          { Proc_parallel(p1, p2) }                                          %prec PROC_PARALLEL
  | REPLICATE; p = process                        { Proc_replicate p }
  | NEW; names = nonempty_list(NAME); COLON; ty = NAME; SEMICOLON; next = process                                                    %prec PROC_NEW
    { Proc_new { names
               ; ty
               ; next } }
  | IF; cond = pterm; THEN; true_branch = process                                                            %prec PROC_IF
    { Proc_conditional { cond; true_branch; false_branch = Proc_null } }
  | IF; cond = pterm; THEN; true_branch = process; ELSE; false_branch = process
    { Proc_conditional { cond; true_branch; false_branch } }
  | IN; LEFT_PAREN; channel = pterm; COMMA; message = pattern; RIGHT_PAREN
  | IN; LEFT_PAREN; channel = pterm; COMMA; message = pattern; RIGHT_PAREN; SEMICOLON
    { Proc_in { channel; message; next = Proc_null } }
  | IN; LEFT_PAREN; channel = pterm; COMMA; message = pattern; RIGHT_PAREN; SEMICOLON; next = process        %prec PROC_IN
    { Proc_in { channel; message; next } }
  | OUT; LEFT_PAREN; channel = pterm; COMMA; message = pterm; RIGHT_PAREN
  | OUT; LEFT_PAREN; channel = pterm; COMMA; message = pterm; RIGHT_PAREN; SEMICOLON
    { Proc_out { channel; message; next = Proc_null } }
  | OUT; LEFT_PAREN; channel = pterm; COMMA; message = pterm; RIGHT_PAREN; SEMICOLON; next = process %prec PROC_OUT
    { Proc_out { channel; message; next } }
  | LET; pat = pattern; EQ; t = pterm; IN; true_branch = process                                             %prec PROC_LET
    { Proc_eval { let_bind_pat = pat; let_bind_term = t; true_branch; false_branch = Proc_null } }
  | LET; pat = pattern; EQ; t = pterm; IN; true_branch = process; ELSE; false_branch = process
    { Proc_eval { let_bind_pat = pat; let_bind_term = t; true_branch; false_branch } }
  | INSERT; name = NAME; LEFT_PAREN; terms = separated_nonempty_list(COMMA, pterm); RIGHT_PAREN
    { Proc_insert { name; terms; next = Proc_null } }
  | INSERT; name = NAME; LEFT_PAREN; terms = separated_nonempty_list(COMMA, pterm); RIGHT_PAREN; SEMICOLON; next = process %prec PROC_INSERT
    { Proc_insert { name; terms; next } }
  | GET; name = NAME; LEFT_PAREN; pats = separated_nonempty_list(COMMA, pattern); RIGHT_PAREN                          
    { Proc_get { name; pats; next = None } }
  | GET; name = NAME; LEFT_PAREN; pats = separated_nonempty_list(COMMA, pattern); RIGHT_PAREN; IN; true_branch = process %prec PROC_GET
    { Proc_get { name; pats; next = Some (true_branch, None) } }
  | GET; name = NAME; LEFT_PAREN; pats = separated_nonempty_list(COMMA, pattern); RIGHT_PAREN; IN; true_branch = process; ELSE; false_branch = process
    { Proc_get { name; pats; next = Some (true_branch, Some false_branch) } }
  | EVENT; name = NAME
    { Proc_event { name; terms = []; next = None } }
  | EVENT; name = NAME; SEMICOLON; next = process                                                                         %prec PROC_EVENT
    { Proc_event { name; terms = []; next = Some next } }
  | EVENT; name = NAME; LEFT_PAREN; terms = separated_nonempty_list(COMMA, pterm); RIGHT_PAREN
    { Proc_event { name; terms; next = None } }
  | EVENT; name = NAME; LEFT_PAREN; terms = separated_nonempty_list(COMMA, pterm); RIGHT_PAREN; SEMICOLON; next = process %prec PROC_EVENT
    { Proc_event { name; terms; next = Some next } }
