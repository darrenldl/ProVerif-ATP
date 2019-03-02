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
let nice_tex = ref true

let preamble = "
\\documentclass{article}
\\usepackage[latin1]{inputenc}
\\newcommand{\\kwl}[1]{\\mathbf{#1}}
\\newcommand{\\kwf}[1]{\\mathsf{#1}}
\\newcommand{\\kwc}[1]{\\mathsf{#1}}
\\newcommand{\\kwp}[1]{\\mathsf{#1}}
\\newcommand{\\kwt}[1]{\\mathsf{#1}}
\\newcommand{\\kwe}[1]{\\mathsf{#1}}
\\newcommand{\\kwtable}[1]{\\mathsf{#1}}
\\newcommand{\\var}[1]{\\mathit{#1}}
\\begin{document}
"

let postamble = "
\\end{document}
"

let printed_preamble = ref false

let outfile = ref ""

let outchannel = ref stdout

let print_string s = 
  output_string (!outchannel) s

let print_sanitize s = 
  for i = 0 to String.length s - 1 do
    match s.[i] with
      '\\' -> print_string "{\\textbackslash}"
    | '&' -> print_string "\\ensuremath{\\&}"
    | '{' -> print_string "\\ensuremath{\\{}"
    | '}' -> print_string "\\ensuremath{\\}}"
    | '_' -> print_string "{\\_}"
    | '^' -> print_string "{\\string^}"
    | '#' -> print_string "\\#"
    | '$' -> print_string "\\$"
    | '%' -> print_string "\\%"
    | '@' -> print_string "{\\string@}"
    | '~' -> print_string "{\\string~}"
    | '>' -> print_string "\\ensuremath{>}"
    | '<' -> print_string "\\ensuremath{<}"
    | c -> output_char (!outchannel) c
  done

let print_preamble() =
  if not (!printed_preamble) then
    begin
      printed_preamble := true;
      print_string preamble
    end
  
let close () =
  if (!printed_preamble) then
    print_string postamble;
  if (!outfile) != "" then
    close_out (!outchannel)

