type token =
  | CHOICE
  | STAR
  | COMMA
  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | BAR
  | SEMI
  | NEW
  | OUT
  | IN
  | IDENT of (Pitptree.ident)
  | ATIDENT of (Pitptree.ident)
  | STRING of (Pitptree.ident)
  | PROJECTION of (Pitptree.ident)
  | INT of (int)
  | REPL
  | IF
  | THEN
  | ELSE
  | EQUAL
  | FUN
  | EQUATION
  | REDUCTION
  | PREDICATE
  | PROCESS
  | SLASH
  | DOT
  | EOF
  | LET
  | QUERY
  | BEFORE
  | PUTBEGIN
  | NONINTERF
  | EVENT
  | NOT
  | ELIMTRUE
  | FREE
  | SUCHTHAT
  | CLAUSES
  | RED
  | EQUIV
  | EQUIVEQ
  | WEDGE
  | DIFF
  | COLON
  | NOUNIF
  | PHASE
  | BARRIER
  | AMONG
  | WEAKSECRET
  | PARAM
  | ORTEXT
  | FAIL
  | LESS
  | GREATER
  | TYPE
  | SET
  | FORALL
  | CONST
  | INJEVENT
  | OR
  | CHANNEL
  | LETFUN
  | DEFINE
  | EXPAND
  | YIELD
  | LEQ
  | PROBA
  | LBRACE
  | RBRACE
  | PROOF
  | IMPLEMENTATION
  | EQUIVALENCE
  | OTHERWISE
  | FOREACH
  | DO
  | SECRET
  | PUBLICVARS
  | RANDOM
  | LEFTARROW
  | TABLE
  | INSERT
  | GET

val all :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Pitptree.tdecl list * Pitptree.tprocess * Pitptree.tprocess option
val lib :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Pitptree.tdecl list
val permut :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Pitptree.ident list list
val order :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Pitptree.ident list
val term :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Pitptree.term_e
