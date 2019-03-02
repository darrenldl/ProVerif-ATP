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


let ffgg n =
  print_string "(* Generated script of the protocol f^ng^n for n = ";
  print_int n;
  print_string " 
   See Jonathan Millen, A Necessarily Parallel Attack, 
   Workshop on Formal Methods and Security Protocols (FMSP'99)
   July 99. *)

(* Public key cryptography *)

fun pk/1.
fun encrypt/2.
reduc decrypt(encrypt(x,pk(y)),y) = x.

(* Function from secrets to host names *)

fun host/1.

free c.
private free M.

query attacker:M.

let processA = 
	out(c, hostA);
	in(c,(=hostB";
  for i = 1 to n do
    print_string ", n";
    print_int i
  done;
  print_string "));\n\tout(c, (hostA, encrypt((";
  for i = 1 to n do
    print_string "n";
    print_int i;
    print_string ", "
  done;
  print_string "M ), pkB))).\n\nlet processB = \n\tin(c, =hostA);\n";
  for i = 1 to n do
    print_string "new n";
    print_int i;
    print_string "; "
  done;
  print_string "\n\tout(c, (hostB";
  for i = 1 to n do
    print_string ", n";
    print_int i
  done;
  print_string "));\n\tin(c, (=hostA, mes));\n\tlet (=n1";
  for i = 1 to n do
    print_string ", x";
    print_int i
  done;
  print_string ") = decrypt(mes, skB) in\n\tout(c, (n1, x1, encrypt((";
  for i = 1 to n do
    print_string "x";
    print_int i;
    print_string ", "
  done;
  print_string "n1), pkB))).

process 
        new skB; let pkB = pk(skB) in
        out(c, pkB);
	let hostB = host(skB) in
	out(c, hostB);
        new skA; let pkA = pk(skA) in
        out(c, pkA);
	let hostA = host(skA) in
	out(c, hostA);
	((!processA) | (!processB))
"


let _ =
  try 
    ffgg (int_of_string (Sys.argv.(1)))
  with _ ->
    print_string "Error. Usage: ffgg n\nwhere n is an integer\n"
