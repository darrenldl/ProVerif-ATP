{
  open Lexing
  open Pv_parser

  exception SyntaxError of string

  let get = Lexing.lexeme

  let strip_front_end front_count end_count s =
    let last_index = String.length s - 1 in
    String.sub s front_count (last_index - end_count)
}

(* Characters *)
let white                = [' ' '\t']+
let newline              = '\r' | '\n' | "\r\n"

let printable_char   = ['\032'-'\126']

let upper_alpha       = ['A'-'Z']
let lower_alpha       = ['a'-'z']
let numeric           = ['0'-'9']
let alpha_numeric     = (lower_alpha | upper_alpha | numeric | ['_'])*
let other_name_symbol = ['\'']

let name = (alpha_numeric | other_name_symbols)+

rule read =
  parse
  (* Ignore spaces *)
  | white      { read lexbuf }
  | newline    { new_line lexbuf; read lexbuf }

  (* Keywords *)
  | "among"          { AMONG }
  | "channel"        { CHANNEL }
  | "choice"         { CHOICE }
  | "clauses"        { CLAUSES }
  | "const"          { CONST }
  | "def"            { DEF }
  | "diff"           { DIFF }
  | "do"             { DO }
  | "elimtrue"       { ELIMTRUE }
  | "else"           { ELSE }
  | "equation"       { EQUATION }
  | "equivalence"    { EQUIVALENCE }
  | "event"          { EVENT }
  | "expand"         { EXPAND }
  | "fail"           { FAIL }
  | "forall"         { FORALL }
  | "free"           { FREE }
  | "fun"            { FUN }
  | "get"            { GET }
  | "if"             { IF }
  | "implementation" { IMPLEMENTATION }
  | "in"             { IN }
  | "inj-event"      { INJ_EVENT }
  | "insert"         { INSERT }
  | "let"            { LET }
  | "letfun"         { LETFUN }
  | "new"            { NEW }
  | "noninterf"      { NONINTERF }
  | "not"            { NOT }
  | "nounif"         { NOUNIF }
  | "or"             { OR }
  | "otherwise"      { OTHERWISE }
  | "out"            { OUT }
  | "param"          { PARAM }
  | "phase"          { PHASE }
  | "pred"           { PRED }
  | "proba"          { PROBA }
  | "process"        { PROCESS }
  | "proof"          { PROOF }
  | "public_vars"    { PUBLIC_VARS }
  | "putbegin"       { PUTBEGIN }
  | "query"          { QUERY }
  | "reduc"          { REDUC }
  | "secret"         { SECRET }
  | "set"            { SET }
  | "suchthat"       { SUCHTHAT }
  | "sync"           { SYNC }
  | "table"          { TABLE }
  | "then"           { THEN }
  | "type"           { TYPE }
  | "weaksecret"     { WEAKSECRET }
  | "yield"          { YIELD }

  | '0'              { NULL_PROC }

  (* Symbols *)
  | '('        { LEFT_PAREN }
  | ')'        { RIGHT_PAREN }
  | ','        { COMMA }
  | '['        { LEFT_BRACK }
  | ']'        { RIGHT_BRACK }
  | ':'        { COLON }
  | ';'        { SEMICOLON }

  (* Operators *)
  | '='        { EQ }
  | "<>"       { NEQ }
  | "&&"       { AND }
  | "||"       { OR }

  | '|'        { PARALLEL }
  | '!'        { REPLICATE }

  (* name *)
  | name       { NAME name }

  | _                    { raise (SyntaxError ("Unexpected char: " ^ get lexbuf)) }
  | eof { EOF }
