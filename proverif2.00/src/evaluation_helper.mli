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

val term_evaluation : term -> term
val equal_terms_modulo_eval : term -> term -> bool
val term_evaluation_fail : term -> term
val match_pattern : pattern -> term -> unit
val decompose_term : term * term -> (term * term) list
val decompose_list : (term * term) list -> (term * term) list
val decompose_term_rev : binder * term -> (binder * term) list
val decompose_list_rev : (binder * term) list -> (binder * term) list
val term_evaluation_letfilter :
    Pitypes.term_occ -> term list -> (arg_meaning * term * when_include) list ->
      term list * (arg_meaning * term * when_include) list
val is_in_public : (term * term) list -> term -> term option
val is_in_public_list : (term * term) list -> term list -> term list option
val remove_first_in_public :
  (term * term) list -> (binder * term) list -> (binder * term) list
val update_term_list : (term * term) list ->
  (term * term) list -> (binder * term) list -> (binder * term) list
val add_public_and_close :
    term Pitypes.reduc_state -> (term * term) list -> term Pitypes.reduc_state
val add_public_with_recipe :
    term Pitypes.reduc_state -> term * term -> term Pitypes.reduc_state
val add_public :
    term Pitypes.reduc_state -> term -> term * term Pitypes.reduc_state
val add_public_list :
    term Pitypes.reduc_state -> (term * term) list -> term Pitypes.reduc_state
val close_public_phase_change : term Pitypes.reduc_state -> int -> term Pitypes.reduc_state
val close_public_initial : term Pitypes.reduc_state -> term Pitypes.reduc_state
val extract_phase : int ->
  (process * 'a * 'b * 'c * 'd) list ->
  (process * 'a * 'b * 'c * 'e Pitypes.info) list
