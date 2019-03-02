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
{
open Parsing_helper
open Parser

let create_hashtable size init =
  let tbl = Hashtbl.create size in
  List.iter (fun (key,data) -> Hashtbl.add tbl key data) init;
  tbl

(* Untyped front-end *)

let keyword_table =
  create_hashtable 11
[ "fun", FUN;
  "data", DATA;
  "equation", EQUATION;
  "reduc", REDUCTION;
  "query", QUERY;
  "nounif", NOUNIF;
  "param", PARAM;
  "not", NOT;
  "elimtrue", ELIMTRUE;
  "pred", PREDICATE
]

(* Typed front-end *)

let tkeyword_table =
  create_hashtable 11
[ "type", TYPE;
  "name", NAME;
  "fun", FUN;
  "const", CONST;
  "forall", FORALL;
  "equation", EQUATION;
  "clauses", CLAUSES;
  "query", QUERY;
  "nounif", NOUNIF;
  "set", SET;
  "not", NOT;
  "elimtrue", ELIMTRUE;
  "pred", PREDICATE
]

}

rule token = parse
  "\010" | "\013" | "\013\010"
     { Lexing.new_line lexbuf; token lexbuf }
| [ ' ' '\009' '\012' ] +
     { token lexbuf }
| [ 'a'-'z' 'A'-'Z' ] (( ['a'-'z' 'A'-'Z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9' ] )*)
     { let s = Lexing.lexeme lexbuf in
	 try
	   Hashtbl.find (if !Param.typed_frontend then tkeyword_table else keyword_table) s
         with
           Not_found ->
             IDENT (s, extent lexbuf)
     }
| ([ '0'-'9' ]) +
    { 
      try 
        INT (int_of_string(Lexing.lexeme lexbuf))
      with Failure _ ->
	input_error "Incorrect integer" (extent lexbuf)
    }
| "(*" {
         comment lexbuf;
         token lexbuf
       }
| ',' { COMMA }
| '(' { LPAREN }
| ')' { RPAREN }
| '[' { LBRACKET }
| ']' { RBRACKET }
| ';' { SEMI }
| ':' { COLON }
| '&' { WEDGE }
| '=' { EQUAL }
| "->" { RED } 
| "<->" { EQUIV } 
| "<=>" { EQUIVEQ } 
| '/' { SLASH }
| '.' { DOT }
| '*' { STAR }
| "<>" { DIFF }
| eof { EOF }
| _ { input_error "Illegal character" (extent lexbuf) }

and comment = parse
| "*)" { }
| "\010" | "\013" | "\013\010"
     { Lexing.new_line lexbuf; comment lexbuf }
| eof { }
| _ { comment lexbuf }
