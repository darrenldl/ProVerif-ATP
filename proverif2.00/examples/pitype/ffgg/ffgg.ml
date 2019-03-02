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

type skey.
type pkey.
type host.
type nonce.

(* Public key encryption *)

fun pk(skey): pkey.
fun encrypt(bitstring, pkey): bitstring.
reduc forall x: bitstring, y: skey; decrypt(encrypt(x,pk(y)),y) = x.

(* Host names *)

const A, B: host.


free c: channel.
free M: nonce [private].

query attacker(M).

let processA(pkB: pkey) = 
	out(c, A);
	in(c,(=B";
  for i = 1 to n do
    print_string ", n";
    print_int i;
    print_string ": nonce"
  done;
  print_string "));\n\tout(c, (A, encrypt((";
  for i = 1 to n do
    print_string "n";
    print_int i;
    print_string ", "
  done;
  print_string "M ), pkB))).\n\nlet processB(skB: skey, pkB: pkey) = \n\tin(c, =A);\n";
  for i = 1 to n do
    print_string "new n";
    print_int i;
    print_string ": nonce; "
  done;
  print_string "\n\tout(c, (B";
  for i = 1 to n do
    print_string ", n";
    print_int i
  done;
  print_string "));\n\tin(c, (=A, mes: bitstring));\n\tlet (=n1";
  for i = 1 to n do
    print_string ", x";
    print_int i;
    print_string ": nonce"
  done;
  print_string ") = decrypt(mes, skB) in\n\tout(c, (n1, x1, encrypt((";
  for i = 1 to n do
    print_string "x";
    print_int i;
    print_string ", "
  done;
  print_string "n1), pkB))).

process 
        new skB: skey; let pkB = pk(skB) in
        out(c, pkB);
	((!processA(pkB)) | (!processB(skB, pkB)))
"


let _ =
  try 
    ffgg (int_of_string (Sys.argv.(1)))
  with _ ->
    print_string "Error. Usage: ffgg n\nwhere n is an integer\n"
