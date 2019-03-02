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

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
(*************************************************************
 *                                                           *
 *  Cryptographic protocol verifier                          *
 *                                                           *
 *  Bruno Blanchet, Vincent Cheval, and Marc Sylvestre       *
 *                                                           *
 *  Copyright (C) INRIA, CNRS 2000-2018                      *
 *                                                           *
 *************************************************************)

(*

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details (in file LICENSE).

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

*)
# 31 "parser.mly"

open Parsing_helper
open Ptree
exception Syntax

# 75 "parser.ml"
let yytransl_const = [|
  257 (* COMMA *);
  258 (* LPAREN *);
  259 (* RPAREN *);
  260 (* LBRACKET *);
  261 (* RBRACKET *);
  262 (* SEMI *);
  263 (* COLON *);
  266 (* RED *);
  267 (* EQUIV *);
  268 (* EQUIVEQ *);
  269 (* EQUAL *);
  270 (* FUN *);
  271 (* EQUATION *);
  272 (* QUERY *);
  273 (* NOUNIF *);
  274 (* SLASH *);
  275 (* STAR *);
  276 (* DOT *);
  277 (* WEDGE *);
    0 (* EOF *);
  278 (* NOT *);
  279 (* ELIMTRUE *);
  280 (* DIFF *);
  281 (* PREDICATE *);
  282 (* REDUCTION *);
  283 (* DATA *);
  284 (* PARAM *);
  285 (* CLAUSES *);
  286 (* CONST *);
  287 (* SET *);
  288 (* NAME *);
  289 (* TYPE *);
  290 (* FORALL *);
    0|]

let yytransl_block = [|
  264 (* IDENT *);
  265 (* INT *);
    0|]

let yylhs = "\255\255\
\003\000\003\000\003\000\003\000\005\000\005\000\004\000\004\000\
\006\000\006\000\007\000\007\000\007\000\007\000\007\000\009\000\
\009\000\008\000\008\000\010\000\010\000\011\000\011\000\012\000\
\012\000\013\000\013\000\013\000\013\000\014\000\014\000\015\000\
\015\000\016\000\017\000\017\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\018\000\
\018\000\018\000\019\000\019\000\019\000\019\000\020\000\020\000\
\021\000\022\000\022\000\023\000\023\000\024\000\024\000\025\000\
\025\000\026\000\026\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\000\000\000\000"

let yylen = "\002\000\
\004\000\003\000\004\000\001\000\003\000\001\000\001\000\000\000\
\003\000\001\000\004\000\003\000\004\000\001\000\002\000\003\000\
\001\000\001\000\000\000\002\000\000\000\001\000\000\000\003\000\
\003\000\003\000\001\000\003\000\003\000\003\000\001\000\003\000\
\002\000\003\000\003\000\005\000\006\000\006\000\004\000\004\000\
\005\000\004\000\004\000\007\000\006\000\006\000\003\000\004\000\
\001\000\003\000\003\000\001\000\003\000\003\000\003\000\001\000\
\004\000\005\000\003\000\003\000\000\000\004\000\003\000\003\000\
\000\000\004\000\006\000\004\000\006\000\010\000\007\000\005\000\
\006\000\004\000\007\000\005\000\006\000\004\000\006\000\004\000\
\008\000\005\000\006\000\006\000\003\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\086\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\087\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\007\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\033\000\
\000\000\000\000\000\000\047\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\085\000\
\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\
\000\000\000\000\039\000\024\000\025\000\040\000\000\000\000\000\
\000\000\000\000\034\000\018\000\020\000\000\000\042\000\043\000\
\000\000\000\000\030\000\032\000\026\000\028\000\029\000\000\000\
\000\000\000\000\022\000\000\000\000\000\064\000\000\000\000\000\
\000\000\000\000\050\000\074\000\000\000\000\000\000\000\000\000\
\000\000\078\000\000\000\080\000\000\000\000\000\000\000\060\000\
\000\000\000\000\063\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\068\000\000\000\005\000\001\000\003\000\000\000\
\000\000\000\000\000\000\015\000\000\000\041\000\000\000\000\000\
\000\000\000\000\000\000\009\000\000\000\072\000\000\000\000\000\
\000\000\057\000\076\000\000\000\000\000\000\000\000\000\082\000\
\000\000\055\000\062\000\051\000\053\000\054\000\000\000\000\000\
\000\000\000\000\037\000\036\000\012\000\000\000\000\000\016\000\
\000\000\038\000\045\000\046\000\000\000\000\000\058\000\073\000\
\000\000\077\000\079\000\000\000\000\000\083\000\084\000\069\000\
\011\000\013\000\044\000\000\000\000\000\075\000\000\000\071\000\
\000\000\067\000\081\000\000\000\070\000"

let yydgoto = "\003\000\
\014\000\027\000\051\000\071\000\072\000\155\000\138\000\139\000\
\140\000\082\000\156\000\041\000\042\000\043\000\044\000\037\000\
\032\000\052\000\118\000\119\000\055\000\053\000\063\000\064\000\
\049\000\099\000"

let yysindex = "\062\000\
\234\255\191\255\000\000\027\255\035\255\105\255\046\255\105\255\
\105\255\071\255\105\255\147\255\148\255\000\000\151\255\015\255\
\112\255\159\255\112\255\112\255\163\255\130\255\172\255\181\255\
\182\255\185\255\000\000\178\255\035\255\042\255\184\255\179\255\
\101\255\176\255\183\255\205\255\197\255\213\255\221\255\200\255\
\196\255\011\255\124\255\202\000\201\255\222\255\232\255\236\255\
\130\255\156\255\218\255\225\255\247\255\070\255\197\255\248\255\
\235\255\002\000\238\255\003\000\117\255\244\255\121\255\010\001\
\007\000\004\000\008\000\254\255\010\000\015\000\017\000\000\000\
\035\255\035\255\035\255\234\255\035\255\035\255\234\255\031\255\
\013\000\005\000\234\255\234\255\014\000\105\255\105\255\000\000\
\105\255\105\255\105\255\000\000\018\000\081\255\236\255\023\000\
\021\000\035\255\009\000\035\255\022\000\035\255\191\255\121\255\
\031\255\011\000\024\000\191\255\121\255\191\255\121\255\236\255\
\016\000\026\000\028\000\164\255\019\000\039\255\175\255\000\000\
\027\000\123\255\029\000\191\255\025\000\035\255\000\000\035\000\
\034\000\036\000\000\000\000\000\000\000\000\000\031\255\174\255\
\033\000\042\000\000\000\000\000\000\000\234\255\000\000\000\000\
\236\255\196\255\000\000\000\000\000\000\000\000\000\000\030\000\
\031\000\032\000\000\000\041\000\236\255\000\000\040\000\191\255\
\043\000\046\000\000\000\000\000\037\000\045\000\191\255\047\000\
\197\255\000\000\038\000\000\000\039\000\051\000\191\255\000\000\
\121\255\130\255\000\000\121\255\121\255\121\255\015\255\044\000\
\048\000\049\000\000\000\234\255\000\000\000\000\000\000\035\255\
\052\000\031\255\031\255\000\000\031\255\000\000\050\000\234\255\
\234\255\234\255\053\000\000\000\035\255\000\000\000\000\244\255\
\191\255\000\000\000\000\054\000\191\255\191\255\015\255\000\000\
\019\000\000\000\000\000\000\000\000\000\000\000\055\000\191\255\
\191\255\191\255\000\000\000\000\000\000\058\000\057\000\000\000\
\234\255\000\000\000\000\000\000\059\000\060\000\000\000\000\000\
\191\255\000\000\000\000\056\000\191\255\000\000\000\000\000\000\
\000\000\000\000\000\000\015\255\130\255\000\000\191\255\000\000\
\061\000\000\000\000\000\191\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\028\255\
\000\000\000\000\000\000\000\000\000\000\122\255\000\000\000\000\
\000\000\000\000\000\000\000\000\068\000\141\255\000\000\000\000\
\063\000\000\000\000\000\000\000\064\000\000\000\000\000\000\000\
\106\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\122\255\068\255\000\000\000\000\000\000\000\000\064\000\000\000\
\000\000\000\000\000\000\000\000\065\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\055\255\000\000\000\000\
\068\000\067\000\000\000\000\000\226\255\000\000\000\000\125\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\070\000\048\255\
\000\000\000\000\000\000\068\000\000\000\000\000\000\000\000\000\
\074\000\000\000\000\000\000\000\000\000\000\000\000\000\070\000\
\000\000\000\000\000\000\171\255\001\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\066\000\000\000\000\000\000\000\000\000\074\000\037\255\
\000\000\075\255\000\000\000\000\000\000\000\000\000\000\000\000\
\069\000\199\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\072\000\000\000\000\000\000\000\000\000\000\000\000\000\
\064\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\122\255\000\000\000\000\000\000\000\000\065\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\074\000\075\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\219\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\065\000\000\000\
\216\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\071\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\065\000\122\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\195\255\180\255\252\255\203\255\158\000\214\255\000\000\162\255\
\115\000\215\255\160\255\020\000\000\000\233\000\234\000\000\000\
\143\000\249\255\000\000\161\000\232\000\246\255\207\255\166\000\
\198\255\093\000"

let yytablesize = 347
let yytable = "\098\000\
\031\000\034\000\113\000\034\000\034\000\097\000\034\000\056\000\
\058\000\060\000\166\000\057\000\059\000\106\000\131\000\174\000\
\087\000\134\000\048\000\128\000\129\000\143\000\144\000\132\000\
\070\000\035\000\164\000\038\000\039\000\065\000\088\000\170\000\
\135\000\172\000\028\000\065\000\029\000\014\000\136\000\014\000\
\193\000\014\000\030\000\073\000\178\000\074\000\161\000\187\000\
\199\000\137\000\010\000\115\000\010\000\036\000\014\000\117\000\
\014\000\006\000\179\000\006\000\006\000\065\000\001\000\002\000\
\006\000\006\000\006\000\010\000\070\000\070\000\130\000\105\000\
\070\000\133\000\006\000\006\000\101\000\017\000\040\000\017\000\
\198\000\034\000\034\000\206\000\034\000\034\000\034\000\049\000\
\153\000\154\000\211\000\004\000\017\000\159\000\017\000\070\000\
\165\000\163\000\216\000\230\000\231\000\171\000\073\000\173\000\
\074\000\146\000\029\000\077\000\149\000\150\000\151\000\027\000\
\033\000\029\000\204\000\031\000\031\000\031\000\112\000\050\000\
\048\000\070\000\029\000\061\000\223\000\027\000\227\000\212\000\
\116\000\061\000\184\000\185\000\240\000\089\000\090\000\091\000\
\242\000\243\000\234\000\235\000\236\000\004\000\019\000\004\000\
\019\000\004\000\004\000\246\000\247\000\248\000\004\000\004\000\
\004\000\004\000\045\000\046\000\244\000\100\000\047\000\074\000\
\004\000\004\000\101\000\062\000\254\000\100\000\054\000\074\000\
\000\001\217\000\061\000\251\000\220\000\221\000\222\000\194\000\
\049\000\195\000\003\001\065\000\049\000\049\000\049\000\005\001\
\180\000\181\000\182\000\031\000\066\000\067\000\049\000\049\000\
\068\000\001\001\004\000\069\000\075\000\239\000\076\000\078\000\
\238\000\092\000\079\000\098\000\015\000\016\000\017\000\018\000\
\031\000\031\000\031\000\080\000\019\000\020\000\081\000\021\000\
\086\000\085\000\093\000\022\000\023\000\024\000\025\000\026\000\
\048\000\056\000\056\000\056\000\048\000\048\000\048\000\008\000\
\083\000\095\000\094\000\008\000\008\000\008\000\048\000\048\000\
\084\000\102\000\001\000\096\000\103\000\008\000\008\000\004\000\
\005\000\006\000\007\000\114\000\104\000\107\000\108\000\008\000\
\009\000\110\000\010\000\011\000\012\000\013\000\052\000\109\000\
\111\000\120\000\056\000\056\000\056\000\121\000\123\000\126\000\
\122\000\124\000\125\000\127\000\052\000\141\000\145\000\157\000\
\142\000\158\000\152\000\189\000\160\000\162\000\167\000\168\000\
\101\000\176\000\183\000\175\000\186\000\190\000\191\000\177\000\
\196\000\192\000\197\000\203\000\188\000\207\000\208\000\210\000\
\105\000\200\000\201\000\202\000\205\000\215\000\229\000\232\000\
\209\000\213\000\214\000\237\000\249\000\250\000\147\000\224\000\
\148\000\253\000\252\000\225\000\226\000\233\000\008\000\008\000\
\023\000\241\000\245\000\255\000\019\000\059\000\228\000\019\000\
\004\001\218\000\169\000\021\000\065\000\035\000\004\000\219\000\
\023\000\002\001\066\000"

let yycheck = "\049\000\
\005\000\006\000\061\000\008\000\009\000\048\000\011\000\018\000\
\019\000\020\000\105\000\019\000\020\000\055\000\076\000\112\000\
\006\001\079\000\004\001\073\000\074\000\083\000\084\000\077\000\
\029\000\006\000\103\000\008\000\009\000\002\001\020\001\108\000\
\002\001\110\000\008\001\008\001\002\001\001\001\008\001\003\001\
\135\000\005\001\008\001\002\001\006\001\004\001\100\000\124\000\
\145\000\019\001\003\001\062\000\005\001\008\001\018\001\063\000\
\020\001\003\001\020\001\005\001\006\001\034\001\001\000\002\000\
\010\001\011\001\012\001\020\001\073\000\074\000\075\000\002\001\
\077\000\078\000\020\001\021\001\007\001\003\001\008\001\005\001\
\142\000\086\000\087\000\160\000\089\000\090\000\091\000\020\001\
\008\001\009\001\167\000\024\001\018\001\098\000\020\001\100\000\
\104\000\102\000\175\000\194\000\195\000\109\000\002\001\111\000\
\004\001\086\000\002\001\007\001\089\000\090\000\091\000\006\001\
\008\001\002\001\157\000\010\001\011\001\012\001\002\001\008\001\
\004\001\126\000\002\001\002\001\183\000\020\001\188\000\169\000\
\008\001\008\001\008\001\009\001\209\000\010\001\011\001\012\001\
\213\000\214\000\200\000\201\000\202\000\001\001\018\001\003\001\
\020\001\005\001\006\001\224\000\225\000\226\000\010\001\011\001\
\012\001\013\001\008\001\008\001\215\000\002\001\008\001\004\001\
\020\001\021\001\007\001\034\001\241\000\002\001\008\001\004\001\
\245\000\177\000\008\001\233\000\180\000\181\000\182\000\002\001\
\006\001\004\001\255\000\008\001\010\001\011\001\012\001\004\001\
\010\001\011\001\012\001\192\000\008\001\008\001\020\001\021\001\
\008\001\252\000\024\001\018\001\013\001\208\000\020\001\024\001\
\205\000\000\000\020\001\253\000\014\001\015\001\016\001\017\001\
\010\001\011\001\012\001\007\001\022\001\023\001\018\001\025\001\
\021\001\018\001\018\001\029\001\030\001\031\001\032\001\033\001\
\006\001\010\001\011\001\012\001\010\001\011\001\012\001\006\001\
\020\001\002\001\013\001\010\001\011\001\012\001\020\001\021\001\
\020\001\024\001\024\001\008\001\020\001\020\001\021\001\014\001\
\015\001\016\001\017\001\008\001\006\001\006\001\020\001\022\001\
\023\001\020\001\025\001\026\001\027\001\028\001\006\001\006\001\
\006\001\000\000\010\001\011\001\012\001\007\001\007\001\001\001\
\013\001\020\001\009\001\003\001\020\001\009\001\009\001\001\001\
\020\001\005\001\009\001\126\000\020\001\008\001\020\001\008\001\
\007\001\006\001\008\001\020\001\008\001\003\001\005\001\021\001\
\008\001\006\001\001\001\003\001\020\001\003\001\001\001\003\001\
\002\001\020\001\020\001\020\001\013\001\003\001\003\001\197\000\
\020\001\020\001\020\001\007\001\003\001\005\001\086\000\020\001\
\087\000\006\001\008\001\020\001\020\001\020\001\003\001\005\001\
\003\001\020\001\020\001\020\001\003\001\006\001\192\000\005\001\
\020\001\177\000\107\000\020\001\020\001\020\001\024\001\178\000\
\020\001\253\000\020\001"

let yynames_const = "\
  COMMA\000\
  LPAREN\000\
  RPAREN\000\
  LBRACKET\000\
  RBRACKET\000\
  SEMI\000\
  COLON\000\
  RED\000\
  EQUIV\000\
  EQUIVEQ\000\
  EQUAL\000\
  FUN\000\
  EQUATION\000\
  QUERY\000\
  NOUNIF\000\
  SLASH\000\
  STAR\000\
  DOT\000\
  WEDGE\000\
  EOF\000\
  NOT\000\
  ELIMTRUE\000\
  DIFF\000\
  PREDICATE\000\
  REDUCTION\000\
  DATA\000\
  PARAM\000\
  CLAUSES\000\
  CONST\000\
  SET\000\
  NAME\000\
  TYPE\000\
  FORALL\000\
  "

let yynames_block = "\
  IDENT\000\
  INT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : Ptree.ident) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'termseq) in
    Obj.repr(
# 93 "parser.mly"
 ( PFunApp (_1, _3) )
# 402 "parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'termseq) in
    Obj.repr(
# 95 "parser.mly"
 ( PTuple _2 )
# 409 "parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : Ptree.ident) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'termseq) in
    Obj.repr(
# 97 "parser.mly"
 ( PName(_1, _3) )
# 417 "parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ptree.ident) in
    Obj.repr(
# 99 "parser.mly"
 ( PIdent (_1) )
# 424 "parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'netermseq) in
    Obj.repr(
# 103 "parser.mly"
 ( _1 :: _3 )
# 432 "parser.ml"
               : 'netermseq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 105 "parser.mly"
 ( [_1] )
# 439 "parser.ml"
               : 'netermseq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'netermseq) in
    Obj.repr(
# 109 "parser.mly"
        ( _1 )
# 446 "parser.ml"
               : 'termseq))
; (fun __caml_parser_env ->
    Obj.repr(
# 111 "parser.mly"
 ( [] )
# 452 "parser.ml"
               : 'termseq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ptree.ident) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'neidentseq) in
    Obj.repr(
# 115 "parser.mly"
        ( _1 :: _3 )
# 460 "parser.ml"
               : 'neidentseq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ptree.ident) in
    Obj.repr(
# 117 "parser.mly"
 ( [_1] )
# 467 "parser.ml"
               : 'neidentseq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : Ptree.ident) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'formatseq) in
    Obj.repr(
# 121 "parser.mly"
 ( PFFunApp (_1, _3) )
# 475 "parser.ml"
               : 'format))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'formatseq) in
    Obj.repr(
# 123 "parser.mly"
 ( PFTuple _2 )
# 482 "parser.ml"
               : 'format))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : Ptree.ident) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'formatseq) in
    Obj.repr(
# 125 "parser.mly"
 ( PFName(_1, _3) )
# 490 "parser.ml"
               : 'format))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ptree.ident) in
    Obj.repr(
# 127 "parser.mly"
 ( PFIdent (_1) )
# 497 "parser.ml"
               : 'format))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ptree.ident) in
    Obj.repr(
# 129 "parser.mly"
        ( PFAny (_2) )
# 504 "parser.ml"
               : 'format))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'format) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'neformatseq) in
    Obj.repr(
# 133 "parser.mly"
 ( _1 :: _3 )
# 512 "parser.ml"
               : 'neformatseq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'format) in
    Obj.repr(
# 135 "parser.mly"
 ( [_1] )
# 519 "parser.ml"
               : 'neformatseq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'neformatseq) in
    Obj.repr(
# 139 "parser.mly"
        ( _1 )
# 526 "parser.ml"
               : 'formatseq))
; (fun __caml_parser_env ->
    Obj.repr(
# 141 "parser.mly"
 ( [] )
# 532 "parser.ml"
               : 'formatseq))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 145 "parser.mly"
        ( _2 )
# 539 "parser.ml"
               : 'optint))
; (fun __caml_parser_env ->
    Obj.repr(
# 147 "parser.mly"
        ( -1 )
# 545 "parser.ml"
               : 'optint))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'neidentseq) in
    Obj.repr(
# 151 "parser.mly"
        ( _1 )
# 552 "parser.ml"
               : 'identseq))
; (fun __caml_parser_env ->
    Obj.repr(
# 153 "parser.mly"
        ( [] )
# 558 "parser.ml"
               : 'identseq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ptree.ident) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'termseq) in
    Obj.repr(
# 159 "parser.mly"
 ( PSimpleFact(_1,_3), parse_extent() )
# 566 "parser.ml"
               : 'fact))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 161 "parser.mly"
        ( PSNeq(_1,_3), parse_extent() )
# 574 "parser.ml"
               : 'fact))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'termand) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'fact) in
    Obj.repr(
# 165 "parser.mly"
        ( Clause(_1,_3) )
# 582 "parser.ml"
               : 'rule))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'fact) in
    Obj.repr(
# 167 "parser.mly"
        ( Clause([],_1) )
# 589 "parser.ml"
               : 'rule))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'termand) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'fact) in
    Obj.repr(
# 169 "parser.mly"
        ( Equiv(_1,_3,true) )
# 597 "parser.ml"
               : 'rule))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'termand) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'fact) in
    Obj.repr(
# 171 "parser.mly"
        ( Equiv(_1,_3,false) )
# 605 "parser.ml"
               : 'rule))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'fact) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'termand) in
    Obj.repr(
# 175 "parser.mly"
 ( _1 :: _3 )
# 613 "parser.ml"
               : 'termand))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'fact) in
    Obj.repr(
# 177 "parser.mly"
 ( [_1] )
# 620 "parser.ml"
               : 'termand))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'rule) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'reduc) in
    Obj.repr(
# 181 "parser.mly"
 ( _1 :: _3 )
# 628 "parser.ml"
               : 'reduc))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'rule) in
    Obj.repr(
# 183 "parser.mly"
 ( [_1] )
# 635 "parser.ml"
               : 'reduc))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ptree.ident) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formatseq) in
    Obj.repr(
# 187 "parser.mly"
 ( (_1,_3) )
# 643 "parser.ml"
               : 'factformat))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 193 "parser.mly"
        ( [(_1, _3)] )
# 651 "parser.ml"
               : 'eqlist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'eqlist) in
    Obj.repr(
# 195 "parser.mly"
 ( (_1, _3) :: _5 )
# 660 "parser.ml"
               : 'eqlist))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : Ptree.ident) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ptree.decl list) in
    Obj.repr(
# 199 "parser.mly"
        ( (FunDecl(_2, _4)) :: _6 )
# 669 "parser.ml"
               : Ptree.decl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : Ptree.ident) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ptree.decl list) in
    Obj.repr(
# 201 "parser.mly"
        ( (DataFunDecl(_2, _4)) :: _6 )
# 678 "parser.ml"
               : Ptree.decl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'eqlist) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ptree.decl list) in
    Obj.repr(
# 203 "parser.mly"
        ( (Equation(_2)) :: _4 )
# 686 "parser.ml"
               : Ptree.decl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'fact) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ptree.decl list) in
    Obj.repr(
# 205 "parser.mly"
        ( (Query _2) :: _4 )
# 694 "parser.ml"
               : Ptree.decl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'factformat) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'optint) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : Ptree.decl list) in
    Obj.repr(
# 207 "parser.mly"
        ( (NoUnif (_2,_3)) :: _5 )
# 703 "parser.ml"
               : Ptree.decl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'fact) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ptree.decl list) in
    Obj.repr(
# 209 "parser.mly"
        ( (Not _2) :: _4 )
# 711 "parser.ml"
               : Ptree.decl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'fact) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ptree.decl list) in
    Obj.repr(
# 211 "parser.mly"
        ( (Elimtrue _2) :: _4 )
# 719 "parser.ml"
               : Ptree.decl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : Ptree.ident) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : int) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'identseq) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ptree.decl list) in
    Obj.repr(
# 213 "parser.mly"
        ( (PredDecl(_2, _4, _5)) :: _7 )
# 729 "parser.ml"
               : Ptree.decl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : Ptree.ident) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ptree.ident) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ptree.decl list) in
    Obj.repr(
# 215 "parser.mly"
        ( (Param(_2,S _4)) :: _6 )
# 738 "parser.ml"
               : Ptree.decl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : Ptree.ident) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ptree.decl list) in
    Obj.repr(
# 217 "parser.mly"
        ( (Param(_2,I _4)) :: _6 )
# 747 "parser.ml"
               : Ptree.decl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'reduc) in
    Obj.repr(
# 219 "parser.mly"
 ( [Reduc(_2)] )
# 754 "parser.ml"
               : Ptree.decl list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : Ptree.ident) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'termseq) in
    Obj.repr(
# 225 "parser.mly"
 ( PSimpleFact(_1,_3), parse_extent() )
# 762 "parser.ml"
               : 'tfact))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ptree.ident) in
    Obj.repr(
# 227 "parser.mly"
        ( PSimpleFact(_1,[]), parse_extent() )
# 769 "parser.ml"
               : 'tfact))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 229 "parser.mly"
        ( PSNeq(_1,_3), parse_extent() )
# 777 "parser.ml"
               : 'tfact))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ttermand) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'tfact) in
    Obj.repr(
# 233 "parser.mly"
        ( Clause(_1,_3) )
# 785 "parser.ml"
               : 'trule))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'tfact) in
    Obj.repr(
# 235 "parser.mly"
        ( Clause([],_1) )
# 792 "parser.ml"
               : 'trule))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ttermand) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'tfact) in
    Obj.repr(
# 237 "parser.mly"
        ( Equiv(_1,_3,true) )
# 800 "parser.ml"
               : 'trule))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ttermand) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'tfact) in
    Obj.repr(
# 239 "parser.mly"
        ( Equiv(_1,_3,false) )
# 808 "parser.ml"
               : 'trule))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'tfact) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'ttermand) in
    Obj.repr(
# 243 "parser.mly"
 ( _1 :: _3 )
# 816 "parser.ml"
               : 'ttermand))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'tfact) in
    Obj.repr(
# 245 "parser.mly"
 ( [_1] )
# 823 "parser.ml"
               : 'ttermand))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : Ptree.ident) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'formatseq) in
    Obj.repr(
# 249 "parser.mly"
 ( (_1,_3) )
# 831 "parser.ml"
               : 'tfactformat))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : Ptree.ident) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ptree.ident) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'nevartype) in
    Obj.repr(
# 253 "parser.mly"
        ( (_1,_3)::_5 )
# 840 "parser.ml"
               : 'nevartype))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ptree.ident) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ptree.ident) in
    Obj.repr(
# 256 "parser.mly"
        ( [(_1,_3)] )
# 848 "parser.ml"
               : 'nevartype))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'nevartype) in
    Obj.repr(
# 260 "parser.mly"
        ( _2 )
# 855 "parser.ml"
               : 'forallvartype))
; (fun __caml_parser_env ->
    Obj.repr(
# 262 "parser.mly"
        ( [] )
# 861 "parser.ml"
               : 'forallvartype))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'forallvartype) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'trule) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'treduc) in
    Obj.repr(
# 266 "parser.mly"
 ( (_1,_2) :: _4 )
# 870 "parser.ml"
               : 'treduc))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'forallvartype) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'trule) in
    Obj.repr(
# 268 "parser.mly"
 ( [_1,_2] )
# 878 "parser.ml"
               : 'treduc))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'neidentseq) in
    Obj.repr(
# 272 "parser.mly"
        ( _2 )
# 885 "parser.ml"
               : 'options))
; (fun __caml_parser_env ->
    Obj.repr(
# 274 "parser.mly"
        ( [] )
# 891 "parser.ml"
               : 'options))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'forallvartype) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 280 "parser.mly"
    ( [(_1, _2, _4)] )
# 900 "parser.ml"
               : 'teqlist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'forallvartype) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'term) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'teqlist) in
    Obj.repr(
# 282 "parser.mly"
    ( (_1, _2, _4)::_6 )
# 910 "parser.ml"
               : 'teqlist))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ptree.ident) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ptree.tdecl list) in
    Obj.repr(
# 286 "parser.mly"
        ( TTypeDecl(_2) :: _4 )
# 918 "parser.ml"
               : Ptree.tdecl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : Ptree.ident) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ptree.ident) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ptree.tdecl list) in
    Obj.repr(
# 288 "parser.mly"
        ( TNameDecl(_2,_4) :: _6 )
# 927 "parser.ml"
               : Ptree.tdecl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 8 : Ptree.ident) in
    let _4 = (Parsing.peek_val __caml_parser_env 6 : 'identseq) in
    let _7 = (Parsing.peek_val __caml_parser_env 3 : Ptree.ident) in
    let _8 = (Parsing.peek_val __caml_parser_env 2 : 'options) in
    let _10 = (Parsing.peek_val __caml_parser_env 0 : Ptree.tdecl list) in
    Obj.repr(
# 290 "parser.mly"
        ( (TFunDecl(_2, _4, _7, _8)) :: _10 )
# 938 "parser.ml"
               : Ptree.tdecl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : Ptree.ident) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : Ptree.ident) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'options) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ptree.tdecl list) in
    Obj.repr(
# 292 "parser.mly"
        ( (TConstDecl(_2, _4, _5)) :: _7 )
# 948 "parser.ml"
               : Ptree.tdecl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'options) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'teqlist) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : Ptree.tdecl list) in
    Obj.repr(
# 297 "parser.mly"
        ( (TEquation(_3, _2)) :: _5 )
# 957 "parser.ml"
               : Ptree.tdecl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'nevartype) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'tfact) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ptree.tdecl list) in
    Obj.repr(
# 299 "parser.mly"
        ( (TQuery(_2, _4)) :: _6 )
# 966 "parser.ml"
               : Ptree.tdecl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'tfact) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ptree.tdecl list) in
    Obj.repr(
# 301 "parser.mly"
        ( (TQuery([], _2)) :: _4 )
# 974 "parser.ml"
               : Ptree.tdecl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : 'nevartype) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'tfactformat) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'optint) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ptree.tdecl list) in
    Obj.repr(
# 303 "parser.mly"
        ( (TNoUnif (_2, _4,_5)) :: _7 )
# 984 "parser.ml"
               : Ptree.tdecl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'tfactformat) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'optint) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : Ptree.tdecl list) in
    Obj.repr(
# 305 "parser.mly"
        ( (TNoUnif ([],_2,_3)) :: _5 )
# 993 "parser.ml"
               : Ptree.tdecl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'nevartype) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'tfact) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ptree.tdecl list) in
    Obj.repr(
# 307 "parser.mly"
        ( (TNot(_2,_4)) :: _6 )
# 1002 "parser.ml"
               : Ptree.tdecl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'tfact) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ptree.tdecl list) in
    Obj.repr(
# 309 "parser.mly"
        ( (TNot([],_2)) :: _4 )
# 1010 "parser.ml"
               : Ptree.tdecl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'nevartype) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'tfact) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ptree.tdecl list) in
    Obj.repr(
# 311 "parser.mly"
        ( (TElimtrue(_2,_4)) :: _6 )
# 1019 "parser.ml"
               : Ptree.tdecl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'tfact) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ptree.tdecl list) in
    Obj.repr(
# 313 "parser.mly"
        ( (TElimtrue([],_2)) :: _4 )
# 1027 "parser.ml"
               : Ptree.tdecl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : Ptree.ident) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'identseq) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'options) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : Ptree.tdecl list) in
    Obj.repr(
# 315 "parser.mly"
        ( (TPredDecl(_2, _4, _6)) :: _8 )
# 1037 "parser.ml"
               : Ptree.tdecl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Ptree.ident) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'options) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : Ptree.tdecl list) in
    Obj.repr(
# 317 "parser.mly"
        ( (TPredDecl(_2, [], _3)) :: _5 )
# 1046 "parser.ml"
               : Ptree.tdecl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : Ptree.ident) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ptree.ident) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ptree.tdecl list) in
    Obj.repr(
# 319 "parser.mly"
        ( (TSet(_2,S _4)) :: _6 )
# 1055 "parser.ml"
               : Ptree.tdecl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : Ptree.ident) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ptree.tdecl list) in
    Obj.repr(
# 321 "parser.mly"
        ( (TSet(_2,I _4)) :: _6 )
# 1064 "parser.ml"
               : Ptree.tdecl list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'treduc) in
    Obj.repr(
# 323 "parser.mly"
 ( [TReduc(_2)] )
# 1071 "parser.ml"
               : Ptree.tdecl list))
(* Entry all *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry tall *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let all (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ptree.decl list)
let tall (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 2 lexfun lexbuf : Ptree.tdecl list)
