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
open Piptree
open Fileprint

type kind =
    Keyword
  | Fun
  | Cst
  | Pred

let kinds = Hashtbl.create 7

let init_kinds d = 
  Hashtbl.iter (fun keyw _ -> Hashtbl.add kinds keyw "\\kwl") Pilexer.keyword_table;
  List.iter (function
      FunDecl((f,_),_,_) -> Hashtbl.add kinds f "\\kwf"
    | DataFunDecl((f,_),_) -> Hashtbl.add kinds f "\\kwf"
    | Reduc((((PFunApp((f,_),_) ,_),_)::_),_) -> Hashtbl.add kinds f "\\kwf"
    | ReducFail((((PFunApp((f,_),_) ,_),_,_)::_),_) -> Hashtbl.add kinds f "\\kwf"
    | PredDecl((p,_),_,_) -> Hashtbl.add kinds p "\\kwp"
    | Free(l,_) -> List.iter (fun (c,_) -> Hashtbl.add kinds c "\\kwc") l
    | _ -> ()) d

let parse filename = 
  try
    let ic = open_in filename in
    let lexbuf = Lexing.from_channel ic in
    let ptree =
      try
        Piparser.all Pilexer.token lexbuf
      with Parsing.Parse_error ->
        input_error "Syntax error" (extent lexbuf)
    in
    close_in ic;
    ptree
  with Sys_error s ->
    user_error ("File error: " ^ s ^ "\n")

}

rule token = parse
  "\010" | "\013" | "\013\010"
     { print_string "$\\\\\n$"; token lexbuf }
| ' ' 
     { print_string "\\ "; token lexbuf }
| '\009'
     { print_string "\\qquad\\qquad "; token lexbuf }
| [ '\012' ] +
     { token lexbuf }
| [ 'a'-'z' 'A'-'Z' ] (( [ 'a'-'z' 'A'-'Z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9' ] )*)
     { 
       let s = Lexing.lexeme lexbuf in
       begin
	 try
           let k = Hashtbl.find kinds s in
	   print_string (k ^ "{");
	   print_sanitize s;
	   print_string "}"
	 with Not_found ->
	   print_string "\\var{";
	   print_sanitize s;
	   print_string "}"
       end;
       token lexbuf
     }
| ([ '0'-'9' ]) +
     { print_string (Lexing.lexeme lexbuf); token lexbuf }
| "(*" {
         print_string "\\textit{(*";
         comment lexbuf
       }
| ',' (' ' *) { print_string ", "; token lexbuf }
| '(' { print_string "("; token lexbuf }
| ')' { print_string ")"; token lexbuf }
| '[' { print_string "["; token lexbuf }
| ']' { print_string "]"; token lexbuf }
| (' ' *) '|' (' ' *) { print_string "\\mid"; token lexbuf }
| ';' { print_string ";"; token lexbuf }
| '!' { print_string "!"; token lexbuf }
| (' ' *) '=' (' ' *) { print_string " = "; token lexbuf }
| '/' { print_string "/"; token lexbuf }
| '.' { print_string "."; token lexbuf }
| '*' { print_string "*"; token lexbuf }
| ':' { print_string "{:}"; token lexbuf }
| '&' { print_string "\\&"; token lexbuf }
| (' ' *) "->" (' ' *) { print_string (if !nice_tex then "\\rightarrow" else "\\ {-}{>}\\ "); token lexbuf }
| (' ' *) "<->" (' ' *) { print_string (if !nice_tex then "\\leftrightarrow" else "\\ {<}{-}{>}\\ "); token lexbuf }
| (' ' *) "<=>" (' ' *) { print_string (if !nice_tex then "\\Leftrightarrow" else "\\ {<}{=}{>}\\ "); token lexbuf }
| (' ' *) "<>" (' ' *) { print_string (if !nice_tex then "\\neq" else "\\ {<}{>}\\ "); token lexbuf }
| (' ' *) "==>" (' ' *) { print_string (if !nice_tex then "\\Longrightarrow" else "\\ {=}{=}{>}\\ "); token lexbuf }
| eof {  print_string "$\n\\end{tabbing}\n" }	
| _ { input_error "Illegal character" (extent lexbuf) }

and comment = parse
| "*)" { print_string "*)}";
         token lexbuf }
| "\010" | "\013" | "\013\010"
     { print_string "}$\\\\\n$\\textit{"; comment lexbuf }
| eof { print_string "}$\n\\end{tabbing}\n" }
| _ { print_sanitize (Lexing.lexeme lexbuf); comment lexbuf }

{

let convert filename = 
  try
    let ic = open_in filename in
    let lexbuf = Lexing.from_channel ic in
    print_preamble();
    print_string "\\begin{tabbing}\n$";
    token lexbuf;
    close_in ic
  with Sys_error s ->
    user_error ("File error: " ^ s ^ "\n")

let converttotex f =
  let d,_ = parse f in
  init_kinds d;
  convert f 

} 
