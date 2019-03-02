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

(* [implies clause1 clause2] returns true when [clause1] subsumes [clause2] *)
val implies : reduction -> reduction -> bool
(* [reorder hyp] reorders the elements of the hypothesis [hyp]
   to speed up the subsumption test. *)
val reorder : fact list -> fact list

(* [corresp_initialize horn_state] initializes the state of the solver and
   saturates the set of clauses given in [horn_state].
   It allows subsequent calls to resolve_hyp, query_goal_std, 
   and sound_bad_derivable. *)
val corresp_initialize : t_horn_state -> unit
(* [resolve_hyp clause] performs resolution on the hypothesis of the
   clause [clause], and returns the set of obtained clauses with no
   selected hypothesis. In particular, when it returns no clause,
   the hypothesis of [clause] is not derivable. 
   It is called from piauth.ml and from reduction.ml, function 
   check_query_falsified, so it comes indirectly from piauth.ml *)
val resolve_hyp : reduction -> reduction list
(* [query_goal_std fact] performs resolution on [fact], and returns 
   the set of obtained clauses with no selected hypothesis that may
   derive [fact]. In particular, when it returns no clause,
   [fact] is not derivable. 
   It is called only from reduction.ml, in case LetFilter
   - so it comes indirectly from piauth.ml *)
val query_goal_std : fact -> reduction list
(* [sound_bad_derivable clauses] returns the set of clauses that
   derive bad from the initial clauses [clauses].
   It is sound, that is, if it returns a clause, then bad is derivable
   from this clause.
   It restores the previous clauses after the call, so that
   calls to [resolve_hyp] or [query_goal_std] can still be made
   on the initial clauses passed to [corresp_initialize] after calling
   [sound_bad_derivable].
   It is called only from piauth.ml *)
val sound_bad_derivable : reduction list -> reduction list
(* [reset()] resets the whole state *)
val reset : unit -> unit
                      
(* [main_analysis horn_state queries] determines whether the [queries]
   are derivable from the clauses in [horn_state]. It displays the
   results directly on the standard output or in an html file.
   It is called only for the Horn and typed Horn front-ends *)
val main_analysis : t_horn_state -> fact list -> unit

(* [bad_derivable horn_state] determines whether [bad] is derivable
   from the clauses in [horn_state]. It returns the clauses with 
   no selected hypothesis that may derive bad.
   It is called from [Main.interference_analysis] *)
val bad_derivable : t_horn_state -> reduction list

