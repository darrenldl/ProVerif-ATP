{
  open Lexing
  open Tptp_parser

  exception SyntaxError of string

  let get = Lexing.lexeme

  let strip_front_end front_count end_count s =
    let last_index = String.length s - 1 in
    String.sub s front_count (last_index - end_count)
}

let white                = [' ' '\t']+
let newline              = '\r' | '\n' | "\r\n"

(* Space and visible characters upto ~, except ' and \ *)
let viewble_char     = ['.' '\n']
let printable_char   = ['\032'-'\126']
let dollar           = ['$']
let upper_alpha      = ['A'-'Z']
let lower_alpha      = ['a'-'z']
let numeric          = ['0'-'9']
let alpha_numeric    = (lower_alpha | upper_alpha | numeric | ['_'])*
let non_zero_numeric = ['1'-'9']
let zero_numeric     = ['0']
let slash            = ['/']
let exponent         = ['E' 'e']
let dot              = ['.']
let sign             = ['+' '-']
let sq_char          = (['\032'-'\038' '\040'-'\091' '\093'-'\126'] | ['\\']['\'' '\\'])

(* Character classes *)
let single_quote     = ['\'']
let do_char          = (['\032'-'\033' '\035'-'\091' '\093'-'\126'] | ['\\']['\"' '\\'])
let double_quote     = ['\"']
let percentage_sign  = ['%']

(* Numbers. Signs are made part of the same token here. *)
let unsigned_exp_integer = numeric numeric*
let signed_exp_integer   = sign unsigned_exp_integer
let exp_integer          = signed_exp_integer | unsigned_exp_integer
let dot_decimal          = dot numeric numeric*

let positive_decimal     = non_zero_numeric | numeric*
let decimal              = zero_numeric | positive_decimal
let decimal_fraction     = decimal dot_decimal
let decimal_exponent     = (decimal | decimal_fraction) exponent exp_integer

let unsigned_integer     = decimal
let signed_integer       = sign unsigned_integer
let integer              = signed_integer | unsigned_integer

let unsigned_rational    = decimal slash positive_decimal
let signed_rational      = sign unsigned_rational
let rational             = signed_rational | unsigned_rational

let unsigned_real        = decimal_fraction | decimal_exponent
let signed_real          = sign unsigned_real
let real                 = signed_real | unsigned_real

(* Tokens used in syntax, and cannot be character classes *)
let less_sign            = ['<']
let arrow                = ['>']
let plus                 = ['+']
let star                 = ['*']
let vline                = ['|']

let lower_word           = lower_alpha alpha_numeric*
let upper_word           = upper_alpha alpha_numeric*
let dollar_dollar_word   = dollar dollar lower_word
let dollar_word          = dollar lower_word

let distinct_object      = double_quote do_char* double_quote

let single_quoted        = single_quote sq_char sq_char* single_quote

let not_star_slash       = ([^'*']*['*']['*']*[^ '/' '*'])*[^'*']*

(* For lex/yacc there cannot be spaces on either side of the | here *)
let not_star_slash       = ([^'*']*['*']['*']*[^'/''*'])*[^'*']*
let comment_block        = ['/']['*'] not_star_slash ['*']['*']*['/']
let comment_line         = ['%'] printable_char*
let comment              = comment_line | comment_block

let file_name            = single_quoted

rule read =
  parse
  (* Spaces, outside of TPTP grammar, but are allowed in between tokens *)
  | white                { read lexbuf }
  | newline              { new_line lexbuf; read lexbuf }

  (* Keywords *)
  | "fof"                { FOF }
  (* | "cnf"                { CNF }
  | "thf"                { THF }
  | "tff"                { TFF } *)
  | "include"            { INCLUDE }

  (* Punctuation *)
  | '('                  { LEFT_PAREN }
  | ')'                  { RIGHT_PAREN }
  | ','                  { COMMA }
  | '.'                  { DOT }
  | '['                  { LEFT_BRACK }
  | ']'                  { RIGHT_BRACK }
  | ':'                  { COLON }

  (* Operators *)
  | '!'                  { FORALL }
  | '?'                  { EXISTS }
  | '~'                  { NOT }
  | '&'                  { AND }
  | '|'                  { VLINE }
  | "<=>"                { IFF }
  | "=>"                 { IMPLY }
  | "<="                 { LEFT_IMPLY }
  | "<~>"                { XOR }
  | "~|"                 { NOTVLINE }
  | "~&"                 { NOTAND }
  | '*'                  { STAR }
  | '+'                  { PLUS }

  (* Predicates *)
  | '='                  { EQ }
  | "!="                 { NEQ }
  (* | "$true"              { TRUE } *)
  (* | "$false"             { FALSE } *)

  | comment              { read lexbuf }

  | single_quoted        { SINGLE_QUOTED   (get lexbuf |> strip_front_end 1 1) }
  | distinct_object      { DISTINCT_OBJECT (get lexbuf) }

  | dollar_word          { DOLLAR_WORD (get lexbuf) }
  | dollar_dollar_word   { DOLLAR_DOLLAR_WORD (get lexbuf) }
  | upper_word           { UPPER_WORD (get lexbuf) }
  | lower_word           { LOWER_WORD (get lexbuf) }

  (* Tokens used in syntax, and cannot be character classes *)
  (* | less_sign            { LESS_SIGN }
  | arrow                { ARROW } *)
  | plus                 { PLUS }
  | star                 { STAR }
  | vline                { VLINE }

  (* Numbers *)
  | integer              { INTEGER  (get lexbuf) }
  | rational             { RATIONAL (get lexbuf) }
  | real                 { REAL     (get lexbuf) }

  | _                    { raise (SyntaxError ("Unexpected char: " ^ get lexbuf)) }
  | eof { EOF }
