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
open Types
open Parsing_helper
open GMain
open GdkKeysyms

let file = ref None
  
let set_file s =
  file := Some s

let _ =
  Arg.parse
    [ "-lib", Arg.String (fun s -> Param.lib_name := s),
        "<filename> \tchoose the library file (for pitype front-end only)";
      "-commandGraph", Arg.String (fun s ->
        Param.interactive_dot_command := s;),
      "\t\t\tDefine the command for the creation of the graph trace from the dot file";
    ]
    set_file ("Simulator for Proverif " ^ Version.version ^ ", by Bruno Blanchet, Vincent Cheval, and Marc Sylvestre");
  Menu_interact.main_window (!file)
