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
open Pitypes

(* Encode queries of the form "query secret .. [public_vars ...]"
   and "query ...==>... public_vars ..." into correspondence queries
   without public_vars. The process may need to be modified, 
   and groups of queries may need to be split. *)
val encode_secret_public_vars : (t_pi_state -> unit) -> t_pi_state -> unit

(* Give the fact to query from the detailed query
   This is used only to create a resembling specification for SPASS

   This function takes as argument the pi state. *)
val query_to_facts : t_pi_state -> fact list
