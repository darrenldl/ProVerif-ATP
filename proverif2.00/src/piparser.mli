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
  | IDENT of (Piptree.ident)
  | STRING of (Piptree.ident)
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
  | CANTEXT
  | FAIL
  | WHERE
  | OTHERWISE
  | DATA
  | PARAM
  | PRIVATE

val all :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Piptree.decl list * Piptree.process
