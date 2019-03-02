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

(* [copy_process p] returns a copy of the process [p]
   * It renames all bound variables to fresh distinct variables
   (though they keep their old name).
   * New occurrences are created for each program point in the process.
   * Free variables of [p] may be linked to terms via [TLink t] on entry.
   In this case, these variables are substituted by the terms in question
   during the copy. Notice that variables that occur as arguments of
   restrictions [Restr] can only be linked to variables via
   [TLink (Var b)], not to other terms. *)
val copy_process : process -> process

(* [reset_occurrence p] creates a copy of the process [p]
   with occurrences nicely numbered. *)
val reset_occurrence : process -> process

(* [prepare_process state] returns a state containing a copy of the process(es) in state [state], such that:
   * each name created by a restriction is renamed to a fresh name
   (these names are in [pi_glob_table] and [pi_glob_table_var_name] 
   in the returned state);
   * all bound variables are renamed to fresh distinct variables,
   with distinct numbers (these variables are in [pi_glob_table_var_name]
   in the returned state);
   * new occurrences are created at each program point in the process,
   starting from 1. *)
val prepare_process : t_pi_state -> t_pi_state

(* [verify_process l p] verifies that all free variables of 
   [p] are in the list [l]. 
   In particular, [verify_process [] p] verifies that
   the process [p] is closed. *)
val verify_process : binder list -> process -> unit

(* [simplify_state state next_f] simplifies the process(es) in the state [state]
   and calls [next_f state'] with each obtained state [state'].
   It considers the following two cases:
   - choice in the process: it merges branches as much as possible
   - equivalence between two processes: it merges the two processes 
   into a biprocess. *)
val simplify_state : t_pi_state -> (t_pi_state -> unit) -> unit
