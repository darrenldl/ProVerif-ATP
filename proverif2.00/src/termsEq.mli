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
(* This module contains basic functions to manipulate terms modulo
   an equational theory *)

open Types

(* returns true when at least one equation has been registered *)
val hasEquations : unit -> bool

(* Transforms equations into rewrite rules on constructors
   When !Param.html_output is set, an HTML file must be open to receive 
   the display. *)
val record_eqs : t_horn_state -> unit


(* Close clauses modulo the equational theory *
 close_rule_eq is used for clauses entered by the user in Horn-clause 
 front-ends,
 close_fact_eq is used for closing the goals *)
val close_term_eq : (term -> unit) -> term -> unit
val close_term_list_eq : (term list -> unit) -> term list -> unit
val close_fact_eq : (fact -> unit) -> fact -> unit
val close_fact_list_eq : (fact list -> unit) -> fact list -> unit
val close_rule_eq : (reduction -> unit) -> reduction -> unit
val close_rule_hyp_eq : (reduction -> unit) -> reduction -> unit

(* Close terms by rewrite rules of constructors and destructors. *)
val close_term_destr_eq : (term * term) list -> ((term * term) list -> term -> unit) -> term -> unit

(* Close clauses by rewrite rules of constructors and destructors. *
   Used for clauses that define predicates (for LetFilter). *)
val close_rule_destr_eq : (fact list * fact * constraints list list -> unit) -> fact list * fact * constraints list list -> unit

(* [f_has_no_eq f] returns [true] when the function symbol [f]
   has no equation. *)
val f_has_no_eq : funsymb -> bool

(* Unification modulo the equational theory *)
val unify_modulo : (unit -> 'a) -> term -> term -> 'a
val unify_modulo_list : (unit -> 'a) -> term list -> term list -> 'a
val unify_modulo_env : (unit -> 'a) -> (binder * term) list -> (binder * term) list -> 'a

val copy_remove_syntactic : term -> term
val copy_remove_syntactic_fact : fact -> fact
val copy_remove_syntactic_constra : constraints list -> constraints list
val remove_syntactic_term : term -> term
val remove_syntactic_fact : fact -> fact
val remove_syntactic_constra : constraints list -> constraints list

(* Treatment of inequatity constraints *)

(* [check_constraint_list constra] checks that the constraints [constra] 
   are still satisfiable. It raises Unify when they are not. 
   It returns the simplified constraints when they are. *)
val check_constraint_list : constraints list list -> constraints list list

(* [simplify_constra_list rule constralist] 
   simplifies the constraints [constralist] knowing that 
   they occur in a clause containing the facts in the list [rule].
   Raises FalseConstraint when the constraints are not satisfiable. *)
exception FalseConstraint
val simplify_constra_list : fact list -> constraints list list -> constraints list list

(* [implies_constra_list rule formula1 formula2 ()] 
   checks that the inequalities in [formula1] imply those in [formula2]. 
   It returns unit when the check succeeds and raises NoMatch when it fails.
   [formula2] is supposed to contain links that come from a previous matching.
   [rule] is a list of facts of the clause that contains [formula1]. 
   (The argument [rule] is used to know which variables should be preserved in 
   the simplification of the instance of [formula2], which after substitution 
   uses variables of the clause [rule, formula1].) *)

val implies_constra_list : fact list -> constraints list list -> constraints list list -> unit -> unit

(* Transforms equations into rewrite rules on constructors, also closing
   the rewrite rules of destructors modulo equations.
   When !Param.html_output is set, an HTML file must be open to receive 
   the display. *)
val record_eqs_with_destr : Pitypes.t_pi_state -> unit

(* Simplifies a term using the equations *)
exception Reduces
val simp_eq : term -> term
