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
exception WrongChoice
exception WarningsAsError
val delete_NamedProcess: 'a Pitypes.reduc_state -> 'a Pitypes.reduc_state
(* [is_auto_reductible state p] Return true if [p] is auto reductible according to [state], *)
(* false otherwise *)
val is_auto_reductible: term Pitypes.reduc_state -> process -> bool
val equal_io_oi : Pitypes.io_r_t -> Pitypes.io_r_t -> bool
(* [reset_env ()] Reset the global environment, clear tables, restore some parameters. *)
(* Used to load a new file *)
val reset_env: unit -> unit
(* [input_error_box b mess ext] Create a message box with title "Error in your Recipe", and one *)
(* button. The message displayed is comming from an InputError(mess, ext) exception. If [b] *)
(* is true, the the message display the line number and the character number of the error. *)
(* Otherwise, its only display the character number *)
val input_error_box: bool -> string -> Parsing_helper.extent -> unit
(* [parse_term string] Return the term corresponding to the parsing of [string]. *)
(* Raise InputError if the parsing went wrong *)
val parse_term: string -> term
(* [dialog_box title string ()] Create a dialog box with title [title], displaying the string *)
(* string [string]. Return the string enter by the user, raise WrongChoice if no string is entered. *)
val dialog_box : string -> string -> unit -> string
(* [proc_of_sub proc] Return the process corresponding to [sub] *)
val proc_of_sub: term Pitypes.sub_proc -> process
(* [sub_of_proc proc] Return the subprocess corresponding to [proc] *)

val sub_of_proc: process -> term Pitypes.sub_proc
(* [update_cur_state state] Update the current state with state *)
val update_cur_state: term Pitypes.reduc_state -> unit
(* [exists_auto ()] Return true if there exists a auto-reductible process in one of the *)
(* subprocess of the current state, false otherwise *)
val exists_auto: unit -> bool
(* [is_first_step ()] Return true if the current state is the initialise state, false otherwise *)
val is_first_step: unit -> bool
(* [get_state ()] Return the current state *)
val get_state: unit -> term Pitypes.reduc_state
(* [get_data ()] Return the current data associated to the current state *)
val get_data: unit -> Pitypes.data_model
val get_recipe : string -> string -> term
val get_new_vars: 'a Pitypes.reduc_state -> (term * 'a) list ->
  (term * term * 'a) list * term list
val expand_recipe : term list -> ('a * term) list -> term -> term
(* Set or get the reference [io_c] used to make RIO reductions *)
val set_io_c: Pitypes.io_r_t -> unit
val get_io_c: unit -> Pitypes.io_r_t
(* Function for forward step *)
val exists_forward: unit -> bool
val one_step_forward: unit -> term Pitypes.reduc_state
val add_to_forwards_lst: term Pitypes.reduc_state -> unit
val reset_forward_lst: unit -> unit
(* val set_lst_is_bck: bool -> unit *)
