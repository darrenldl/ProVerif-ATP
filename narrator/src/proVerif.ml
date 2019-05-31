open Lexing

let lexbuf_to_pos_str lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "%s:%d:%d" pos.pos_fname pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol - 1)

let parse_with_error lexbuf =
  try Ok (Pv_parser.parse_decls Pv_lexer.read lexbuf) with
  | Tptp_lexer.SyntaxError msg ->
    Error (Printf.sprintf "%s: %s" (lexbuf_to_pos_str lexbuf) msg)
  | Tptp_parser.Error ->
    Error (Printf.sprintf "%s: syntax error" (lexbuf_to_pos_str lexbuf))
  | Tptp_ast.ErrorWithMsg s ->
    Error (Printf.sprintf "%s: %s" (lexbuf_to_pos_str lexbuf) s)

let parse_pv_code (input : string) :
  (Pv_ast.decl list, string) result =
  let lexbuf = Lexing.from_string input in
  parse_with_error lexbuf

let process_string s =
  match parse_pv_code s with
  | Ok l -> Ok (String.concat "\n" (List.map Pv_ast.decl_to_string_debug l))
  | Error s -> Error s

let str =
  {|
const ZERO : bitstring.

free c : channel.

fun h(bitstring) : bitstring.

fun xor(bitstring, bitstring) : bitstring.

(* associativity *)
equation forall x:bitstring, y:bitstring, z:bitstring; xor(x, xor(y, z)) = xor(xor(x, y), z).

(* commutativity *)
equation forall x:bitstring, y:bitstring; xor(x, y) = xor(y, x).

(* neutral element *)
equation forall x:bitstring; xor(x, ZERO) = x.

(* nilpotence *)
equation forall x:bitstring; xor(x, x) = ZERO.

fun rotate(bitstring, bitstring) : bitstring.

fun split_L(bitstring) : bitstring.
fun split_R(bitstring) : bitstring.

free k  : bitstring [private].
free ID : bitstring [private].

free objective : bitstring [private].

query attacker(objective).

let R =
  new r1:bitstring;
  out(c, r1);                           (* 1. send r1 R -> T *)
  in(c, (r2             : bitstring,
         left_xor_ID2_g : bitstring));  (* 2. recv left(xor(ID2, g))
                                           T -> R *)
  let g     = h(xor(xor(r1, r2), k)) in
  let ID2   = rotate(ID, g) in
  let left  = split_L(xor(ID2, g)) in
  let right = split_R(xor(ID2, g)) in
  if left = left_xor_ID2_g then (
    out(c, right);                      (* 3. send right(xor(ID2, g))
                                           R -> T *)
    (* authenticated, send out objective *)
    out(c, objective)
  ).

|}

let () =
  match process_string str with
  | Ok s ->
    Js_utils.console_log s
  | Error e ->
    Js_utils.console_log e
