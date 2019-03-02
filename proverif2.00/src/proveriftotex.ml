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
(* TO DO There is a known problem in proveriftotex: when an identifier
is rebound, it may not be printed in the right font. It is printed
everywhere in the same font, corresponding to one of its definitions. *)

open Parsing_helper

(* Parse the arguments *)

type in_pos =
    Pi
  | PiType
  | Default

let in_kind = ref Default

let up_in = function
    "pi" -> Pi
  | "pitype" -> PiType
  | _ -> Parsing_helper.user_error "-in should be followed by pi or pitype"

let ends_with s sub =
  let l_s = String.length s in
  let l_sub = String.length sub in
  (l_s >= l_sub) && (String.sub s (l_s - l_sub) l_sub = sub)
  
let converttotex f =
  let in_front_end =
    match !in_kind with
      Default -> (* Set the front-end depending on the extension of the file *)
	let f_up = String.uppercase_ascii f in
	if ends_with f_up ".PV" then PiType else Pi
        (* Pi is the default when no extension is recognized for compatibility reasons *)
      |	x -> x
  in
  match in_front_end with
    Pi -> Lexertotex.converttotex f
  | PiType -> Pitlexertotex.converttotex f
  | Default -> Parsing_helper.internal_error "The Default case should have been removed previously"

let gc = ref false

let _ =
  Arg.parse
    [
        "-tt", Arg.Clear Fileprint.nice_tex, "\t\tbe close to text format";

        "-in", Arg.String(fun s -> in_kind := up_in s), 
          "<format> \t\tchoose the input format (horn, horntype, spass, pi, pitype)";

        "-o", Arg.String(fun s -> 
	  Fileprint.close();
	  Fileprint.outfile := s;
	  begin
	    try
	      Fileprint.outchannel := open_out s
	    with Sys_error s ->
	      user_error ("File error: " ^ s)
	  end;
	  Fileprint.printed_preamble := false),
          "choose the output file name (for TeX output)";

      "-gc", Arg.Set gc, 
        "display gc statistics"
    ]
    converttotex ("Proverif " ^ Version.version ^ " to TeX convertor");
  Fileprint.close();
  if !gc then Gc.print_stat stdout
