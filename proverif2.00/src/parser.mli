type token =
  | COMMA
  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | SEMI
  | COLON
  | IDENT of (Ptree.ident)
  | INT of (int)
  | RED
  | EQUIV
  | EQUIVEQ
  | EQUAL
  | FUN
  | EQUATION
  | QUERY
  | NOUNIF
  | SLASH
  | STAR
  | DOT
  | WEDGE
  | EOF
  | NOT
  | ELIMTRUE
  | DIFF
  | PREDICATE
  | REDUCTION
  | DATA
  | PARAM
  | CLAUSES
  | CONST
  | SET
  | NAME
  | TYPE
  | FORALL

val all :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ptree.decl list
val tall :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ptree.tdecl list
