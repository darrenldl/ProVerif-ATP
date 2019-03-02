open Lexing

let lexbuf_to_pos_str lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol - 1)

let parse_with_error lexbuf =
  try Ok (Tptp_parser.parse_decls Tptp_lexer.read lexbuf) with
  | Tptp_lexer.SyntaxError msg ->
    Error (Printf.sprintf "%s: %s" (lexbuf_to_pos_str lexbuf) msg)
  | Tptp_parser.Error ->
    Error (Printf.sprintf "%s: syntax error" (lexbuf_to_pos_str lexbuf))
  | Tptp_ast.ErrorWithMsg s ->
    Error (Printf.sprintf "%s: %s" (lexbuf_to_pos_str lexbuf) s)
