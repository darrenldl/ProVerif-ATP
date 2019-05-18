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

let upper_alpha      = ['A'-'Z']
let lower_alpha      = ['a'-'z']
let numeric          = ['0'-'9']
let alpha_numeric    = (lower_alpha | upper_alpha | numeric | ['_'])*

let term     = alpha_numeric+
let variable = alpha_numeric+

rule read =
  parse
  (* Ignore spaces *)
  | white      { read lexbuf }
  | newline    { new_line lexbuf; read lexbuf }

  (* Keywords *)
  | "fun"      { FUN }
  | "equation" { EQUATION }
  | "reduc"    { REDUC }
  | "forall"   { FORALL }
  | "new"      { NEW }
  | "out"      { OUT }
  | "let"      { LET }
  | "in"       { IN }
  | "if"       { IF }
  | "then"     { THEN }
  | "else"     { ELSE }
  | '0'        { NULL_PROC }

  (* Symbols *)
  | '('        { LEFT_PAREN }
  | ')'        { RIGHT_PAREN }
  | ','        { COMMA }
  | '['        { LEFT_BRACK }
  | ']'        { RIGHT_BRACK }
  | ':'        { COLON }

  (* Operators *)
  | '='        { EQ }
  | '<>'       { NEQ }
  | "&&"       { AND }
  | "||"       { OR }
  | "not"      { NOT }

  | '|'        { PARALLEL }
  | '!'        { REPLICATE }
