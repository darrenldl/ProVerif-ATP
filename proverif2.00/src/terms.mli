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
(* This modules contains basic functions to manipulate terms *)

open Types

(* Basic string functions *)

(* [ends_with s sub] is true when the string [s] ends with [sub] *)
val ends_with : string -> string -> bool
    
(* [starts_with s sub] is true when the string [s] starts with [sub] *)
val starts_with : string -> string -> bool

val tuple_table : (typet list, funsymb) Hashtbl.t

(* [get_tuple_fun tl] returns the function symbol corresponding
   to tuples with arguments of types [tl] *)
val get_tuple_fun : typet list -> funsymb
val get_term_type : term -> typet
val get_pat_type : pattern -> typet

val is_var : term -> bool

val equal_types : typet -> typet -> bool

val term_of_pattern_variable : pattern -> term

val get_format_type : format -> typet
val copy_n : int -> 'a -> 'a list
val tl_to_string : string -> typet list -> string

(* [eq_lists l1 l2] tests the physical equality between
   the elements of [l1] and [l2] *)
val eq_lists : 'a list -> 'a list -> bool

(* Creates and returns a new identifier or variable *)

(* Clear useds_ids. Used to reload a file in proverif interact mode *)
val init_used_ids: unit -> unit

(* [record_id s ext] records the identifier [s] so that it will not be
   reused elsewhere. [record_id] must be called only before calls to
   [fresh_id] or [new_var_name] *)
val record_id : string -> Parsing_helper.extent -> unit

(* [fresh_id s] creates a fresh identifier by changing the number of [s].
   Reuses exactly [s] when [s] has not been used before. *)
val fresh_id : string -> string

(* [new_var s t] creates a fresh variable with name [s] and type [t] *)
val new_var : string -> typet -> binder
val new_unfailing_var : string -> typet -> binder

(* [new_var_noren s t] creates a fresh variable with name [s] and type [t]
   The name of this variable is exactly [s], without renaming it to
   a fresh name even if s is already used. Such variables should never
   be displayed. *)
val new_var_noren : string -> typet -> binder

(* [new_var_noren_with_fail s t may_fail] creates a fresh variable with
   name [s], type [t], and may_fail value [may_fail].
   The name of this variable is exactly [s], without renaming it to
   a fresh name even if s is already used. Such variables should never
   be displayed. *)
val new_var_noren_with_fail : string -> typet -> bool -> binder

(* [copy_var v] creates a fresh variable with the same sname and type as [v]  *)
val copy_var : binder -> binder

(* [copy_var_noren v] creates a fresh variable with the same name and type
   as [v]. The name is exactly the same as [v], without renaming to a fresh
   name. *)
val copy_var_noren : binder -> binder

(* [new_var_def t] creates a fresh variable with a default name and type [t] *)
val new_var_def : typet -> term
val new_unfailing_var_def : typet -> term

(* [val_gen tl] creates new variables of types [tl] and returns them in a
   list *)
val var_gen : typet list -> term list

(* [is_may_fail_term t] returns true if [t] is the constant [fail] or a may-fail variable *)
val is_may_fail_term : term -> bool

(* [is_unfailing_var t] returns true if [t] is the constant [fail] or a may-fail variable *)
val is_unfailing_var : term -> bool

(* [is_failure t] returns true if [t] is the constant [fail] or a may-fail variable *)
val is_failure : term -> bool

(* [occurs_var v t] returns true when variable [v] occurs in [t] *)
val occurs_var : binder -> term -> bool
val occurs_var_fact : binder -> fact -> bool

(* [occurs_f f t] returns true when function symbol [f] occurs in [t] *)
val occurs_f : funsymb -> term -> bool
val occurs_f_pat : funsymb -> pattern -> bool
val occurs_f_fact : funsymb -> fact -> bool

(* Syntactic equality *)
val equal_terms : term -> term -> bool
val equals_term_pair : 'a * term -> 'a * term -> bool
val equal_facts : fact -> fact -> bool
val equals_simple_constraint : constraints -> constraints -> bool

(* General variables *)
val new_gen_var : typet -> bool -> funsymb
val generalize_vars_not_in : binder list -> term -> term
val generalize_vars_in : binder list -> term -> term

(* Copies. Variables must be linked only to other variables, with VLink. *)
val copy_term : term -> term
val copy_fact : fact -> fact
val copy_constra : constraints list -> constraints list
val copy_rule : reduction -> reduction
val copy_red : rewrite_rule -> rewrite_rule
(* To cleanup variable links after copies and other manipulations
   [current_bound_vars] is the list of variables that currently have a link.
   [cleanup()] removes all links of variables in [current_bound_vars],
   and resets [current_bound_vars] to the empty list.

   Furthermore, [cleanup_assoc_table_gen_and_ex] cleanup the association table.
 *)
val current_bound_vars : binder list ref
val cleanup : unit -> unit
val link : binder -> linktype -> unit
val link_var : term -> linktype -> unit
val auto_cleanup : (unit -> 'a) -> 'a

(* Exception raised when unification fails *)
exception Unify
val occur_check : binder -> term -> unit
(* Unify two terms/facts by linking their variables to terms *)
val unify : term -> term -> unit
val unify_facts : fact -> fact -> unit
(* Copies. Variables can be linked to terms with TLink *)
val copy_term2 : term -> term
val copy_fact2 : fact -> fact
val copy_constra2 : constraints list -> constraints list
val copy_rule2 : reduction -> reduction

exception NoMatch
val match_terms : term -> term -> unit
val match_facts : fact -> fact -> unit
val matchafact : fact -> fact -> bool
(* Same as matchafact except that it returns true only when some variable
   x is mapped to a term that is not a variable and that contains x by
   the matching substitution *)
val matchafactstrict : fact -> fact -> bool

(* Copy of terms and constraints after matching.
   Variables can be linked to terms with TLink, but the link
   is followed only once, not recursively *)
val copy_term3 : term -> term
val copy_fact3 : fact -> fact
val copy_constra3 : constraints list -> constraints list

(* [copy_term4] follows links [Tlink] recursively,
   but does not rename variables *)
val copy_term4 : term -> term

(* Size of terms/facts *)
val term_size : term -> int
val fact_size : fact -> int

(* Return true when the term contains a variable *)
val has_vars : term -> bool

(* [get_var vlist t] accumulate in reference list [vlist] the list of variables
   in the term [t].
   [get_vars_constra vlist c] does the same for the constraint [c], and
   [get_vars_fact vlist f] for the fact f *)
val get_vars : binder list ref -> term -> unit
val get_vars_constra : binder list ref -> constraints -> unit
val get_vars_fact : binder list ref -> fact -> unit

(* [get_vars_pat accu pat] returns [accu] with the variables bound in [pat] added *)
val get_vars_pat : binder list -> pattern -> binder list
    
(* [replace_f_var vl t] replaces names in t according to
   the association list vl. That is, vl is a reference to a list of pairs
   (f_i, v_i) where f_i is a (nullary) function symbol and
   v_i is a variable. Each f_i is replaced with v_i in t.
   If an f_i in general_vars occurs in t, a new entry is added
   to the association list vl, and f_i is replaced accordingly. *)

val replace_f_var : (funsymb * binder) list ref -> term -> term

(* [rev_assoc v2 vl] looks for [v2] in the association list [vl].
   That is, [vl] is a list of pairs (f_i, v_i) where f_i is a
   (nullary) function symbol and v_i is a variable.
   If [v2] is a v_i, then it returns f_i[],
   otherwise it returns [v2] unchanged. *)

val rev_assoc : binder -> (funsymb * binder) list -> term

(* [follow_link var_case t] follows links stored in variables in [t]
   and returns the resulting term. Variables are translated
   by the function [var_case] *)

val follow_link : (binder -> term) -> term -> term

(* [replace name f t t'] replaces all occurrences of the name [f] (ie f[]) with [t]
   in [t'] *)

val replace_name : funsymb -> term -> term -> term

(* [skip n l] returns list [l] after removing its first [n] elements *)
val skip : int -> 'a list -> 'a list

(* Do not select Out facts, blocking facts, or pred_TUPLE(vars) *)
val add_unsel : fact -> unit
val is_unselectable : fact -> bool

(* helper function for decomposition of tuples *)
val reorganize_fun_app : funsymb -> term list ->
  term list list

(* Symbols *)

val get_fail_symb : typet -> funsymb
val get_fail_term : typet -> term

(* Constants *)

val true_cst : funsymb
val false_cst : funsymb

val true_term : term
val false_term : term

(* Functions *)

val make_choice : term -> term -> term
val is_true_fun : unit -> funsymb

val equal_fun : typet -> funsymb
val diff_fun : typet -> funsymb
val or_fun : unit -> funsymb
val and_fun : unit -> funsymb
val not_fun : unit -> funsymb
val make_not : term -> term
val and_list : term list -> term
val or_not_list : term list -> term
val new_name_fun : typet -> funsymb

val glet_constant_fun : typet -> funsymb
val glet_constant_never_fail_fun : typet -> funsymb

val glet_fun : typet -> funsymb
val gtest_fun : typet -> funsymb
val success_fun : typet -> funsymb
val not_caught_fail_fun : typet -> funsymb

val complete_semantics_constructors : typet list -> typet -> rewrite_rules
val red_rules_fun : funsymb -> rewrite_rules

(* [clauses_for_function clauses_for_red_rules s f] generates clauses
   for a function [f], given a function [clauses_for_red_rules] such
   that [clauses_for_red_rules f red_rules] generates clauses for
   function that has rewrite rules [red_rules].
   (For constructors, the rewrite rules f(...fail...) -> fail are
   omitted from [red_rules]. The function [clauses_for_red_rules] must
   take this point into account. In practice, this is easy because the
   clauses that come from f(...fail...) -> fail are useless.  This
   however needs to be justified in each case.)
   [s] is unused. It helps for calling [clauses_for_function]
   as argument of [Hashtbl.iter]. *)
val clauses_for_function : (funsymb -> rewrite_rules -> unit) ->
  funsymb -> unit

val get_function_name : funsymb -> string
val projection_fun : funsymb * int -> funsymb
(* [get_all_projection_fun tuple_symb] returns the list of projection
   functions corresponding to the tuple function [tuple_symb] *)
val get_all_projection_fun : funsymb -> funsymb list


val reset_occurrence : unit -> unit
val new_occurrence : unit -> int
val put_lets : process -> (binder * term) list -> process

val create_name : string -> string -> typet list * typet -> bool -> funsymb

exception False_inequality

val generate_destructor_with_side_cond : term list list ->
  term list -> term -> Parsing_helper.extent -> rewrite_rules
