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
open Parsing_helper
open Types
open Pitypes
open Terms

type query_res = True | False | DontKnow

type nested_t =
    NonNested (* The whole query is not nested *)
  | TopNested (* The whole query is nested, and I am at the top *)
  | InsideNested (* The whole query is nested, and I am verifying a subquery *)
  
let get_res = function
    True -> " is true."
  | False -> " is false."
  | DontKnow -> " cannot be proved."

let get_html_res = function
    True -> " is <span class=\"trueresult\">true</span>."
  | False -> " is <span class=\"falseresult\">false</span>."
  | DontKnow -> " <span class=\"unknownresult\">cannot be proved</span>."

let supplemental_info = ref []

(* Display a clause and possibly a corresponding trace
   When inj_mode = Some q, try to reconstruct a trace that falsifies injectivity
   When inj_mode = None, just try to reconstruct a trace corresponding
   to the derivation of the clause cl.
   Returns true when a trace has definitely been found.
 *)

let display_clause_trace detail recheck opt_query list_started cl =
  Display.Text.print_string "goal reachable: ";
  Display.Text.display_rule cl;
  if !Param.html_output then
    begin
      if not (!list_started) then
	begin
	  list_started := true;
	  Display.Html.print_string "<UL>\n";
	end;
      Display.Html.print_string "<LI>goal reachable: ";
      Display.Html.display_rule cl
    end;
  (* TulaFale expects a derivation after "goal reachable" *)
  if (detail || (!Param.tulafale = 1)) then
    begin
      try
	let new_tree = History.build_history recheck cl in
	if (!Param.reconstruct_trace) && (!Param.reconstruct_derivation) &&
	  (!Param.key_compromise == 0)
	then
	  begin
	    Reduction.do_reduction recheck opt_query new_tree
	  end
	else
	  begin
	    cleanup();
	    false
	  end
      with Not_found ->
	(* When the derivation could not be reconstructed *)
	cleanup();
	false
    end
  else
    false

(* Link variables of a fact to new constants, of type "SpecVar" *)

let rec put_constants = function
    Var v ->
      begin
	match v.link with
	  TLink t -> ()
	| NoLink ->
	   v.link <- TLink (FunApp({ f_orig_name = v.v_orig_name;
                                     f_name = Display.Text.varname v;
				     f_type = [], v.btype;
				     f_cat = SpecVar v;
				     f_initial_cat = SpecVar v;
				     f_private = false;
				     f_options = 0 }, []));
	   current_bound_vars := v :: (!current_bound_vars)
	| _ -> internal_error "unexpected link in put_constants"
      end
  | FunApp(f,l) -> List.iter put_constants l

let put_constants_fact = function
    Pred(p,l) -> List.iter put_constants l
  | Out(t,tl) ->
      put_constants t;
      List.iter (fun (_,t') -> put_constants t') tl

let put_constants_constra = List.iter (function
    Neq(t1,t2) -> put_constants t1; put_constants t2)

let put_constants_rule (hyp, concl, hist, constra) =
  List.iter put_constants_fact hyp;
  put_constants_fact concl;
  List.iter put_constants_constra constra


(* Copy a query, following links inside variables *)

let copy_event = function
    QSEvent(b, t) -> QSEvent(b, TermsEq.copy_remove_syntactic t)
  | QFact(p, tl) -> QFact(p, List.map TermsEq.copy_remove_syntactic tl)
  | QNeq(t1,t2) -> QNeq(TermsEq.copy_remove_syntactic t1, TermsEq.copy_remove_syntactic t2)
  | QEq(t1,t2) -> QEq(TermsEq.copy_remove_syntactic t1, TermsEq.copy_remove_syntactic t2)

let rec copy_query = function
    Before(el, hll) -> Before(List.map copy_event el, List.map (List.map copy_hypelem) hll)

and copy_hypelem = function
    QEvent e -> QEvent(copy_event e)
  | NestedQuery q -> NestedQuery (copy_query q)

(* Check that all elements of SpecVar that occur in the "begin" part
   of a query also occur in its "end" part *)

let occurs_event sv = function
    QSEvent(b,t) -> Terms.occurs_f sv t
  | QFact(p,tl) -> List.exists (Terms.occurs_f sv) tl
  | QNeq(t1,t2) -> (Terms.occurs_f sv t1) || (Terms.occurs_f sv t2)
  | QEq(t1,t2) -> (Terms.occurs_f sv t1) || (Terms.occurs_f sv t2)

let rec occurs_in_e end_part = function
    Var v -> true
  | FunApp({ f_cat = SpecVar _ } as sv, []) -> List.exists (occurs_event sv) end_part
  | FunApp(f,l) -> List.for_all (occurs_in_e end_part) l

let occurs_in_e_event end_part = function
    QSEvent(b,t) -> occurs_in_e end_part t
  | QFact(p,tl) -> List.for_all (occurs_in_e end_part) tl
  | QNeq(t1,t2) -> (occurs_in_e end_part t1) && (occurs_in_e end_part t2)
  | QEq(t1,t2) -> (occurs_in_e end_part t1) && (occurs_in_e end_part t2)

let rec occurs_in_e_query end_part = function
    Before(el,hll) -> (List.for_all (occurs_in_e_event end_part) el)
	&& (List.for_all (List.for_all (occurs_in_e_hypelem end_part)) hll)

and occurs_in_e_hypelem end_part = function
    QEvent e -> occurs_in_e_event end_part e
  | NestedQuery q -> occurs_in_e_query end_part q

let check_query_vars = function
    Before(end_part,hll) -> List.for_all (List.for_all (occurs_in_e_hypelem end_part)) hll

let enforce_query_vars q' =
  if not (check_query_vars q') then
    begin
      Display.Text.print_string "Occurrence checking failed in ";
      Display.Text.display_corresp_query q';
      Display.Text.newline();
      Display.Text.print_line "For the nested query e1 ==> (e2 ==> H) & ... to be true,\nthe variables instantiated when querying e1 ==> e2 & ... and that occur in\nH must also occur in e2. This is wrong for the query above.";
      if !Param.html_output then
	begin
	  Display.Html.print_string "Occurrence checking failed in ";
	  Display.Html.display_corresp_query q';
	  Display.Html.newline();
	  Display.Html.print_line "For the nested query e1 ==> (e2 ==> H) & ... to be true,\nthe variables instantiated when querying e1 ==> e2 & ... and that occur in\nH must also occur in e2. This is wrong for the query above.";
	end;
      raise Unify
    end


(* Replace constants "SpecVar" of a query with the corresponding variables *)

let rec specvar_to_var = function
    Var v -> Var v
  | FunApp({ f_cat = SpecVar v} ,[]) ->
      Var v
  | FunApp(f,l) -> FunApp(f, List.map specvar_to_var l)

let specvar_to_var_event = function
    QSEvent(b,t) -> QSEvent(b, specvar_to_var t)
  | QFact(p, tl) -> QFact(p, List.map specvar_to_var tl)
  | QNeq(t1,t2) -> QNeq(specvar_to_var t1, specvar_to_var t2)
  | QEq(t1,t2) -> QEq(specvar_to_var t1, specvar_to_var t2)

let rec specvar_to_var_query = function
    Before(el,hll) -> Before(List.map specvar_to_var_event el,
			     List.map (List.map specvar_to_var_hypelem) hll)

and specvar_to_var_hypelem = function
    QEvent e -> QEvent(specvar_to_var_event e)
  | NestedQuery q -> NestedQuery (specvar_to_var_query q)

let specvar_to_var_env = List.map (fun (v,t) -> (v, specvar_to_var t))

let specvar_to_var_fact = function
    Pred(p,l) -> Pred(p, List.map specvar_to_var l)
  | Out(t,tl) -> Out(specvar_to_var t,
		     List.map (fun (x,t') -> (x,specvar_to_var t')) tl)

let specvar_to_var_constra = List.map (function
    Neq(t1, t2) -> Neq(specvar_to_var t1, specvar_to_var t2))

(* Test whether v occurs in query q *)

let v_occurs v = function
  | QSEvent(_,t) -> Terms.occurs_var v t
  | QFact(_,tl) -> List.exists (Terms.occurs_var v) tl
  | QNeq(t1,t2) -> (Terms.occurs_var v t1) || (Terms.occurs_var v t2)
  | QEq(t1,t2) -> (Terms.occurs_var v t1) || (Terms.occurs_var v t2)

let rec v_occurs_query v = function
    Before(el,hll) ->
      (List.exists (v_occurs v) el) ||
      (List.exists (List.exists (v_occurs_hypelem v)) hll)

and v_occurs_hypelem v = function
    QEvent e' -> v_occurs v e'
  | NestedQuery q -> v_occurs_query v q

(* [for_all_vars_in_term f t] returns [true] when [f v]
   is true for all variables [v] in [t]. *)

let rec for_all_vars_in_term f = function
  | Var v -> f v
  | FunApp(_,l) -> List.for_all (for_all_vars_in_term f) l

(* Call f for each variable that occurs in the query *)

let rec iter_vars_in_term f = function
    Var v -> f v
  | FunApp(_,l) -> List.iter (iter_vars_in_term f) l

let iter_vars_in_event f = function
    QSEvent(b,t) -> iter_vars_in_term f t
  | QFact(p,tl) -> List.iter (iter_vars_in_term f) tl
  | QNeq(t1,t2) -> iter_vars_in_term f t1; iter_vars_in_term f t2
  | QEq(t1,t2) -> iter_vars_in_term f t1; iter_vars_in_term f t2

let rec iter_vars_in_query f = function
    Before(el,hll) ->
      List.iter (iter_vars_in_event f) el;
      List.iter (List.iter (iter_vars_in_hypelem f)) hll

and iter_vars_in_hypelem f = function
    QEvent e' -> iter_vars_in_event f e'
  | NestedQuery q -> iter_vars_in_query f q

let rec check_occ_queries rest = function
  | [] -> ()
  | (q::l) ->
      iter_vars_in_query (fun v ->
	if List.exists (v_occurs_query v) (rest @ l) &&
	  not (let Before(el,_) = q in List.exists (v_occurs v) el)
	then
	  begin
	    Display.Text.print_string "Occurrence checking failed in ";
	    Display.Text.display_corresp_query q;
	    Display.Text.newline();
	    Display.Text.print_line "For the nested query e1 ==> (e2 ==> H) & (e3 ==> H') & ... to be true,\nthe variables that occur in H and H' must also occur in e2 and e3.\nThis is wrong for the query above.";

	    if !Param.html_output then
	      begin
	      Display.Html.print_string "Occurrence checking failed in ";
	      Display.Html.display_corresp_query q;
	      Display.Html.newline();
	      Display.Html.print_line "For the nested query e1 ==> (e2 ==> H) & (e3 ==> H') & ... to be true,\nthe variables that occur in H and H' must also occur in e2 and e3.\nThis is wrong for the query above.";
	      end;

	    raise Unify
	  end
      ) q;
      check_occ_queries (q::rest) l

(* Check that the value of e in a query e ==> H determines the value
   of e ==> H *)


(* Rename variables to fresh variables *)

let copy_event_fresh = function
    QSEvent(b,t) -> QSEvent(b, Terms.copy_term t)
  | QFact(p, tl) -> QFact(p, List.map Terms.copy_term tl)
  | QNeq(t1,t2) -> QNeq(Terms.copy_term t1, Terms.copy_term t2)
  | QEq(t1,t2) -> QEq(Terms.copy_term t1, Terms.copy_term t2)

(* Copies the query without further renaming of variables *)

let rec copy_term4 = function
    Var v ->
      begin
	match v.link with
	  VLink v' -> Var v'
	| NoLink -> Var v
	| _ -> internal_error "unexpected link in copy_term4"
      end
  | FunApp(f,l) ->
      FunApp(f, List.map copy_term4 l)

let copy_event4 = function
    QSEvent(b,t) -> QSEvent(b, copy_term4 t)
  | QFact(p, tl) -> QFact(p, List.map copy_term4 tl)
  | QNeq(t1,t2) -> QNeq(copy_term4 t1, copy_term4 t2)
  | QEq(t1,t2) -> QEq(copy_term4 t1, copy_term4 t2)

let rec copy_query4 = function
    Before(el, hll) -> Before(List.map copy_event4 el,
			      List.map (List.map copy_hypelem4) hll)

and copy_hypelem4 = function
    QEvent e -> QEvent(copy_event4 e)
  | NestedQuery q -> NestedQuery (copy_query4 q)


(* Unifies two events e and e' modulo the equational theory.
   Calls f for each found most general unifier *)

let unify_event f e e' = match (e,e') with
    QSEvent(b,t), QSEvent(b',t') ->
      if b!=b' then raise Unify;
      TermsEq.unify_modulo f t t'
  | QFact(p,tl), QFact(p',tl') ->
      if p!=p' then raise Unify;
      TermsEq.unify_modulo_list f tl tl'
  | QNeq(t1,t2), QNeq(t1',t2') ->
      TermsEq.unify_modulo (fun () ->
	TermsEq.unify_modulo f t2 t2') t1 t1'
  | QEq(t1,t2), QEq(t1',t2') ->
      TermsEq.unify_modulo (fun () ->
	TermsEq.unify_modulo f t2 t2') t1 t1'
  | _ -> raise Unify

let rec unify_event_list f el el' =
  match el,el' with
    [], [] -> f ()
  | e::r,e'::r' ->
      unify_event (fun () ->
	unify_event_list f r r') e e'
  | _ ->
      Parsing_helper.internal_error "lists should have same length in unify_event_list"
	
(* Replaces variables with constants *)

let put_constants_event = function
    QSEvent(b,t) -> put_constants t
  | QFact(p, tl) -> List.iter put_constants tl
  | QNeq(t1,t2) -> put_constants t1; put_constants t2
  | QEq(t1,t2) -> put_constants t1; put_constants t2

let rec put_constants_query = function
    Before(el, hll) ->
      List.iter put_constants_event el;
      List.iter (List.iter put_constants_hypelem) hll

and put_constants_hypelem = function
    QEvent e -> put_constants_event e
  | NestedQuery q -> put_constants_query q

(* Raise Unify when the term, event, or query are not equal *)

(* Test equality. t1 and t2 must be closed, but they
   may contain variables linked with TLink *)
let equal_terms_modulo t1 t2 =
  Terms.auto_cleanup (fun () ->
    TermsEq.unify_modulo (fun () -> ()) t1 t2)

let equal_event e e' = match (e,e') with
    QSEvent(b,t), QSEvent(b',t') ->
      if b!=b' then raise Unify;
      equal_terms_modulo t t'
  | QFact(p,tl), QFact(p',tl') ->
      if p!=p' then raise Unify;
      List.iter2 equal_terms_modulo tl tl'
  | QNeq(t1,t2), QNeq(t1',t2') ->
      equal_terms_modulo t1 t1';
      equal_terms_modulo t2 t2'
  | QEq(t1,t2), QEq(t1',t2') ->
      equal_terms_modulo t1 t1';
      equal_terms_modulo t2 t2'
  | _ -> raise Unify

let rec equal_hyp_elem h h' = match (h,h') with
    QEvent e, QEvent e' -> equal_event e e'
  | NestedQuery q, NestedQuery q' -> equal_query q q'
  | _ -> raise Unify

and equal_query (Before(el, hll)) (Before(el', hll')) =
  List.iter2 equal_event el el';
  List.iter2 (List.iter2 equal_hyp_elem) hll hll'


let check_det_p q =
  (not (TermsEq.hasEquations())) ||
  (match q with
    Before(el,hll) ->
      let (el', q') =
	Terms.auto_cleanup (fun () ->
	  let el' = List.map copy_event_fresh el in
	  (el', copy_query4 q))
      in
      try
	unify_event_list (fun () ->
	  Terms.auto_cleanup (fun () ->
	    let q1 = copy_query q in
	    let q1' = copy_query q' in
	    put_constants_query q1;
	    put_constants_query q1';
	    if
	      (try
		equal_query q1 q1';
		true
	      with Unify -> false) then raise Unify else false)
	      ) el el'
      with Unify ->
	true)

let enforce_det_p q'' = 
   if not (check_det_p q'') then
      begin
	Display.Text.print_string "Occurrence checking failed in ";
	Display.Text.display_corresp_query q'';
	Display.Text.newline();
	Display.Text.print_line "For the nested query e1 ==> (e2 ==> H) & ... to be true,\nthe value of e2 must determine the value of e2 ==> H.\nThis is wrong for the query above (due to the equational theory).";

	if !Param.html_output then
	  begin
	    Display.Html.print_string "Occurrence checking failed in ";
	    Display.Html.display_corresp_query q'';
	    Display.Html.newline();
	    Display.Html.print_line "For the nested query e1 ==> (e2 ==> H) & ... to be true,\nthe value of e2 must determine the value of e2 ==> H.\nThis is wrong for the query above (due to the equational theory).";
	  end;

	raise Unify
      end


(* Build a clause from a query *)

let inj_marker = [(Terms.new_var Param.def_var_name Param.sid_type, Terms.new_var_def Param.sid_type)]

let non_inj_marker = []

let event_to_end_fact = function
  | QSEvent(_,(FunApp(f,l) as param)) ->
      if (Pievent.get_event_status (!Param.current_state) f).end_status = Inj then
        Pred(Param.end_pred_inj, [Var(Terms.new_var "endsid" Param.sid_type);param])
      else
        Pred(Param.end_pred, [param])
  | QSEvent(_, _) ->
      user_error ("Events should be function applications")
  | QFact(p,l) -> Pred(p,l)
  | QNeq _ | QEq _ -> internal_error "no Neq queries"

let event_list_to_clause = function
    [e] ->
      let g = event_to_end_fact e in
      ([g], g, Empty(g),[])
  | el ->
      let hyp = List.map event_to_end_fact el in
      let pl = List.map (function
	  Pred(p,_) -> p
	| Out _ -> Parsing_helper.internal_error "event_to_end_fact should generate only Pred") hyp
      in
      let combined_pred = Param.get_pred (Combined(pl)) in
      let args = List.concat (List.map (function
	  Pred(_,l) -> l
	| Out _ -> Parsing_helper.internal_error "event_to_end_fact should generate only Pred") hyp)
      in
      let concl = Pred(combined_pred, args) in
      (hyp, concl, Rule(-1, Goal, hyp, concl, []), [])
	
let rec events_to_hyp = function
  | [] -> ([],[],[],[],[])
  | (a::l) ->
      let (hyp', hyp_q', constra', eq_left', eq_right') = events_to_hyp l in
      match a with
      | QEvent e ->
          begin
            match e with
            | QSEvent(b, param) ->
                (* The second arg of Out is used only as a marker to know whether
                   the event is injective or not *)
                ((Out(param, if b then inj_marker else non_inj_marker)) :: hyp', hyp_q', constra', eq_left', eq_right')
            | QFact(p,l) -> ((Pred(p,l)) :: hyp', hyp_q', constra', eq_left', eq_right')
            | QNeq (t1,t2) -> (hyp', hyp_q', [Neq(t1,t2)] :: constra', eq_left', eq_right')
            | QEq (t1,t2) -> (hyp', hyp_q', constra', t1 :: eq_left', t2 :: eq_right')
          end
      |	NestedQuery(Before([QSEvent(b, param)],_) as q) ->
          (* The second arg of Out is used only as a marker to know whether
             the event is injective or not *)
          ((Out(param, if b then inj_marker else non_inj_marker)) :: hyp', q :: hyp_q', constra', eq_left', eq_right')
      |	NestedQuery(Before([QFact(p,l)],_) as q) ->
          ((Pred(p,l)):: hyp', q :: hyp_q', constra', eq_left', eq_right')
      |	NestedQuery(_) ->
	  internal_error "Bad nested query"

(* Transforms a query into a non-injective, non-nested one,
   the only kind of query for which the reconstruction of a trace
   guarantees that the query is false. *)

let non_inj_event = function
    QSEvent(b,t) -> QSEvent(false,t)
  | e -> e

let simplify_query (Before(el,l)) =
  Before(List.map non_inj_event el,
	 List.map (
	 List.map (function
	     NestedQuery(Before([e],_)) -> QEvent(non_inj_event e)
	   | NestedQuery(_) ->
	       internal_error "Bad nested query"
	   | QEvent e -> QEvent(non_inj_event e))
	   ) l)

let remove_nested (Before(el,l)) =
  Before(el,
	 List.map (
	 List.map (function
	     NestedQuery(Before([e],_)) -> QEvent(e)
	   | NestedQuery(_) ->
	       internal_error "Bad nested query"
	   | QEvent e -> QEvent(e))
	   ) l)

let is_non_trivial (Before(el,l)) =
  List.for_all (fun l1 -> l1 != []) l

let is_non_inj = function
    QSEvent(true,_) -> false
  | _ -> true

let is_simple_query (Before(el,l)) =
  (List.for_all is_non_inj el) &&
  (List.for_all (List.for_all (function
      NestedQuery(Before _) -> false
    | QEvent e -> is_non_inj e)) l)

(* For injective agreement *)

let session_id_cst =
  { f_orig_name = "session_id";
    f_name = "session_id";
    f_type = [], Param.sid_type;
    f_private = false;
    f_options = 0;
    f_cat = Eq [];
    f_initial_cat = Eq []
  }

let session_id = FunApp(session_id_cst, [])

let session_id_cst2 =
  { f_orig_name = "session_id2";
    f_name = "session_id2";
    f_type = [], Param.sid_type;
    f_private = false;
    f_options = 0;
    f_cat = Eq [];
    f_initial_cat = Eq []
  }

let session_id2 = FunApp(session_id_cst2, [])

(* to call combine_lists collector[fsymb]  rho{sid2/sid} *)

let rec combine_lists l1 = function
  [] -> []
| ((v,rhov)::l) ->
     let rec do_v = function
       [] -> combine_lists l1 l
     | (v', rholv)::l' ->
	  if v' == v then
            (v', rhov::rholv)::(combine_lists l1 l)
          else
            do_v l'
     in
     do_v l1

(* to call when collector[fsymb] not found, build_list rho{sid2/sid} *)

let build_list = List.map (fun (v,rhov) -> (v, [rhov]))

(* call combine_lists2 [result of combine_lists/collector] rho{sid1/sid}.
   If result empty, raise Unify *)

(* TO DO cleanup after unify_modulo, unify_modulo_env, and unify_modulo_list ?
   (6 occurrences) *)

let check_no_unif t1 t2 =
  let bad = ref false in
  begin
  try
    Terms.auto_cleanup (fun () ->
      TermsEq.unify_modulo (fun () -> bad := true) t1 t2)
  with Unify -> ()
  end;
  not (!bad)

let rec combine_lists2 l1 l2 = match (l1,l2) with
  ([], _) -> []
| (((v, rholv)::l), ((v', rhov')::l')) ->
    if v == v' then
      if List.for_all (fun rhov -> check_no_unif rhov rhov') rholv then
        (v, rholv)::(combine_lists2 l l')
      else
        combine_lists2 l l'
    else
      combine_lists2 l1 l'
| _ -> internal_error "second list should be at least as long as first list in combine_lists2"

module Fun = struct
   type t = funsymb * string
   let compare = compare
end

module FunMap = Map.Make(Fun)

let current_inj_collector = ref FunMap.empty

let combine collector fsymb end_session_id env =
  let rec find_last = function
      [] -> Parsing_helper.internal_error "The environment should contain at least the occurrence variable"
    | [v,t] -> [], v.sname
    | a :: r -> let r', occ_string = find_last r in (a::r', occ_string)
  in
  let (env, occ_string) = find_last env in
  let map_arg = (fsymb, occ_string) in
  end_session_id.link <- TLink session_id;
  let curr_bound_vars = !current_bound_vars in
  current_bound_vars := [];
  let env1 = List.map (fun (v,t) -> (v, copy_term2 t))
               (specvar_to_var_env env) in
  Terms.cleanup();
  end_session_id.link <- TLink session_id2;
  let env2 = List.map (fun (v,t) -> (v, copy_term2 t))
               (specvar_to_var_env env) in
  Terms.cleanup();
  current_bound_vars := curr_bound_vars;
  end_session_id.link <- NoLink;
  let collectorfsymb =
    try
      combine_lists (FunMap.find map_arg collector) env2
    with Not_found ->
      build_list env2
  in
  let res = combine_lists2 collectorfsymb env1 in
  if res = [] then raise Unify;
  FunMap.add map_arg res collector

let check_inj fsymb end_session_id env restwork =
  let old_inj_collector = !current_inj_collector in
  current_inj_collector := combine old_inj_collector fsymb end_session_id env;
  try
    restwork();
    current_inj_collector := old_inj_collector
  with Unify ->
    current_inj_collector := old_inj_collector;
    raise Unify

(*
    Note: there is a small discrepancy between the following version artauth4.tex:
    In the paper, we require that for a variable x_{jk} in the environment
    env_ok(x_{jk}) and env_ok2(x_{jk}) do not unify, where the variable x_{jk} is
    the same for all environments associated with the same function symbol
    fsymb. Here, we require that the environments
    do not unify. I think the following version is sound, but this is more
    difficult to prove, so I use the previous one.


let current_inj_collector = ref []

let check_inj fsymb end_session_id env restwork =
  List.iter (fun (fsymb2, end_session_id2, env2) ->
    if fsymb == fsymb2 then
    begin
      let bad = ref false in
      end_session_id.link <- TLink session_id;
      let curr_bound_vars = !current_bound_vars in
      current_bound_vars := [];
      let env_ok = List.map (fun (v,t) -> (v, copy_term2 t))
                     (specvar_to_var_env env) in
      Terms.cleanup();
      end_session_id2.link <- TLink session_id2;
      let env_ok2 = List.map (fun (v,t) -> (v, copy_term2 t))
                      (specvar_to_var_env env2) in
      Terms.cleanup();
      current_bound_vars := curr_bound_vars;
      begin
        try
          TermsEq.unify_modulo_env (fun () -> bad := true) env_ok env_ok2
        with Unify -> ()
      end;
      end_session_id.link <- NoLink;
      end_session_id2.link <- NoLink;
      if !bad then raise Unify
    end
     ) ((fsymb, end_session_id, env) :: !current_inj_collector);
  let old_inj_collector = !current_inj_collector in
  current_inj_collector := (fsymb, end_session_id, env) :: old_inj_collector;
  try
    restwork();
    current_inj_collector := old_inj_collector
  with Unify ->
    current_inj_collector := old_inj_collector;
    raise Unify
*)

(* Reprogrammation of clause implication to handle implication modulo
   the equational theory
   I can be approximate in that the subsumption test may fail
   even when it is in fact true. So I do not retry all unifications
   when a future unification fails in match_facts_mod_eq,
   by raising Not_found instead of Unify when a future unification fails *)

let match_facts_mod_eq f f1 f2 = match (f1,f2) with
  | Pred(chann1, t1),Pred(chann2, t2) ->
      begin
        if chann1 != chann2 then raise Unify;
        try
          TermsEq.unify_modulo_list (fun () -> try f() with Unify -> raise Not_found) t1 t2
        with Not_found -> raise Unify
      end
  | Out(t1,l1),Out(t2,l2) ->
      (* Is it the right direction ? *)
      let len1 = List.length l1 in
      let len2 = List.length l2 in

      if len2 < len1 then raise Unify;

      let l2 = skip (len2-len1) l2 in

      List.iter2 (fun (v1,t1) (v2,t2) ->
        if v1 != v2 then raise Unify
      ) l1 l2;

      let l1' = List.map snd l1 in
      let l2' = List.map snd l2 in

      begin
      try
        TermsEq.unify_modulo_list (fun () -> try f() with Unify -> raise Not_found) (t1::l1') (t2::l2')
      with Not_found -> raise Unify
      end
  | _ -> raise Unify

let rec match_hyp1_mod_eq f h1 = function
    [] -> raise Unify
  | (h2::hl2) ->
        try
          match_facts_mod_eq f h1 h2
        with Unify ->
          match_hyp1_mod_eq f h1 hl2

let rec match_hyp_mod_eq f hyp1 hyp2 () =
   match hyp1 with
     [] -> f ()
   | (h1 :: hl1) -> match_hyp1_mod_eq (match_hyp_mod_eq f hl1 hyp2) h1 hyp2

let implies_mod_eq (hyp1, concl1, _, constr1) (hyp2, concl2, _, constr2) =
  match_facts_mod_eq (fun () ->
    match_hyp_mod_eq (fun () ->
      begin
	try
	  Terms.auto_cleanup (fun () ->
	    TermsEq.implies_constra_list
	      (List.map (fun f -> specvar_to_var_fact (TermsEq.remove_syntactic_fact f)) (concl2 :: hyp2))
	      (List.map (fun c -> specvar_to_var_constra (TermsEq.remove_syntactic_constra c)) constr2)
	      (List.map (fun c -> specvar_to_var_constra (TermsEq.remove_syntactic_constra c)) constr1) ())
	with NoMatch -> raise Unify
      end;
      )
      (Rules.reorder hyp1) hyp2 ()) concl1 concl2

let implies_mod_eq r1 r2 =
  assert (!current_bound_vars == []);
  put_constants_rule r2;
  let r2' = copy_rule2 r2 in
  cleanup();
  try
    Terms.auto_cleanup (fun () -> implies_mod_eq r1 r2');
    true
  with Unify -> false

let rec remove_subsumed_mod_eq = function
    [] -> []
  | (a::l) ->
      if List.exists (fun r1 -> implies_mod_eq r1 a) l then
	remove_subsumed_mod_eq l
      else
	a::(remove_subsumed_mod_eq (List.filter (fun r2 -> not (implies_mod_eq a r2)) l))

(* Reprogrammation of clause implication to handle one clause and
   one query.  *)

let arg_var =
  { v_orig_name = "event_arg"; sname = "event_arg";
    vname = 0; unfailing = false; btype = Param.event_type; link = NoLink }

let match_facts_eq f end_session_id f1 f2 = match (f1,f2) with
  Pred(chann1, t1),Pred(chann2, t2) ->
    if chann1 != chann2 then raise Unify;
    TermsEq.unify_modulo_list f t1 t2
| Out(t1,marker),Out(t2,l2) ->
    if marker == non_inj_marker then
      TermsEq.unify_modulo f t1 t2
    else
      begin
      match end_session_id with
        None -> Parsing_helper.internal_error "the end event corresponding to an injective begin event should always have a session id"
      | Some i ->
          match t1 with
            FunApp(fsymb, _) ->
              TermsEq.unify_modulo (fun () ->
		(* The change of l2 cannot be done before unification modulo,
                   because before the unification, the event t2 may not correspond to event t1,
                   and so may even not be injective *)
		let l2 =
		  match l2 with
		    [] -> Parsing_helper.internal_error "Environment in Out fact should at least contain the occurrence variable"
		  | [occ_entry] ->
		    (* The user specified to use an empty environment in the event.
		       In this case, we are at least using the arguments of the event in order to prove injectivity. *)
		      [(arg_var, t2); occ_entry]
		  | _ -> l2
		in
		check_inj fsymb i l2 f) t1 t2
          | _ -> Parsing_helper.internal_error "arguments of events should be function applications"
      end
| _ -> raise Unify

let rec match_hyp1_eq f end_session_id h1 = function
    [] -> raise Unify
  | (h2::hl2) ->
        try
          match_facts_eq f end_session_id h1 h2
        with Unify ->
          match_hyp1_eq f end_session_id h1 hl2

let rec match_hyp_eq f hyp1 hyp2 end_session_id () =
   match hyp1 with
     [] -> f ()
   | (h1 :: hl1) -> match_hyp1_eq (match_hyp_eq f hl1 hyp2 end_session_id) end_session_id h1 hyp2

(* Improved verification of predicates in clauses *)

let init_clauses = ref []

let clauses_for_preds = ref None

let get_clauses_for_preds () =
  match ! clauses_for_preds with
    | Some l -> l
    | None ->
        let clauses = ref [] in

        List.iter (fun (hyp1, concl1, constra1, tag1) ->
          TermsEq.close_rule_destr_eq (fun (hyp, concl, constra) ->
            clauses := (hyp, concl, Rule(-1, tag1, hyp, concl, constra), constra) :: (!clauses)
          ) (hyp1, concl1, constra1)
        ) (!Param.current_state).pi_input_clauses;

        List.iter (fun fact ->
          TermsEq.close_rule_destr_eq (fun (hyp, concl, constra) ->
            clauses := (hyp, concl, Rule(-1, LblClause, hyp, concl, constra), constra) :: (!clauses)
          ) ([], fact, [])
        ) (!Param.current_state).pi_elimtrue;

        Terms.cleanup();

        List.iter (function
          | (_,_,Rule(_,(Apply _ | Init), _,_,_), _) as cl -> clauses := cl :: (!clauses)
          | _ -> ()
        ) (!init_clauses);

        clauses_for_preds := Some (!clauses);
        !clauses

let match_hyp_eq f hyp1 constr1 hyp2 end_session_id () =
  let filt = function
    | Out _ -> true
    | Pred(p,_) -> p.p_prop land Param.pred_BLOCKING != 0
  in
  (* To prove the events and blocking predicates of the query (hyp1_events), we
     show that they match the events and blocking predicates of the clause (hyp2_events).
     These predicates cannot be derived from clauses.
     To prove the non-blocking predicate of the query (hyp1_preds), we
     show that they are derivable from any predicates (blocking or not) of the clause
     (hyp2_preds, hyp2_preds_block).
     These predicates cannot be directly in the clause since they are not blocking. *)
  let (hyp1_events, hyp1_preds) = List.partition filt hyp1 in
  let (hyp2_events, hyp2_preds) = List.partition filt hyp2 in
  let hyp2_preds_block = List.filter (function Out _ -> false | Pred(p,_) -> p.p_prop land Param.pred_BLOCKING != 0) hyp2 in

  match_hyp_eq (fun () ->
    if hyp1_preds == [] then f constr1 else
    (* The matching of events succeeded; now I need to prove the facts in hyp1_preds
       from the instance of the facts in hyp2_preds *)
    Terms.auto_cleanup (fun () ->
      let bad_fact = Pred(Param.bad_pred, []) in
      let hyp2_preds' = List.map Terms.copy_fact2 hyp2_preds in
      let hyp1_preds' = List.map Terms.copy_fact2 hyp1_preds in
      let constr1' = List.map Terms.copy_constra2 constr1 in
      let hyp2_preds_block' = List.map Terms.copy_fact2 hyp2_preds_block in
      Terms.cleanup();
      (* Let sigma_0 the substitution that replaces all variables by
         distinct constants. Let H => C the clause found by ProVerif. 
         We show that we can prove an instance of the hypothesis of the query
         from \sigma_0 H. We should prove an instance of the hypothesis of the query
         from any instance of H. The derivation obtained using \sigma_0 H
         can converted into a derivation using \sigma H by replacing the
         constants with other terms. All steps remain valid except that
         the inequalities may no longer be true. Hence, we collect inequalities
         used in the derivation and further check that they are implied by 
         the inequalities in H, by passing them to the function f. *)
      let clauses =
         (hyp1_preds', bad_fact, Rule(-1, LblNone, hyp1_preds', bad_fact, constr1'), constr1') ::
         (get_clauses_for_preds()) @
         (List.map (fun fact -> ([], fact, Rule(-1, LblNone, [], fact, []), [])) hyp2_preds')
      in
      Display.Text.display_inside_query hyp1_preds' constr1' hyp2_preds_block' hyp2_preds';
      incr Param.inside_query_number;
      let inums = string_of_int (!Param.inside_query_number) in

      if !Param.html_output then
        begin
          Display.LangHtml.openfile ((!Param.html_dir) ^ "/inside" ^ inums ^ ".html") ("ProVerif: inside query " ^ inums);
          Display.Html.display_inside_query hyp1_preds' constr1' hyp2_preds_block' hyp2_preds'
        end;
      (* the resolution prover must be _sound_ for this call
	       while for other calls it must be _complete_.
         The function sound_bad_derivable is sound provided the clause
	       do not contain "any_name" and contain unary attacker predicates,
         which is the case here. *)
      let cl = Rules.sound_bad_derivable clauses in
      try
        let (hyp, concl, hist, constra) = 
          List.find (function
            | (hyp, _, _, []) ->
            begin
              try
                Terms.auto_cleanup (fun () ->
                  match_hyp_eq (fun () -> ()) hyp hyp2_preds_block' end_session_id ()
                );
                true
              with Unify -> false
            end
            | _ -> false) cl
        in
        (* Should I try other clauses in cl in case of subsequent failure?
           It may help, but that would be just by chance, since the clauses 
           that use different inequalities on constants of \sigma_0 H 
           in their derivation are typically removed by subsumption. 
           Only clauses that have different hypotheses are kept. *)
   
        (* collect all inequalities in the derivation of cl_found *)
        let derivation = History.build_fact_tree hist in
        let constr1'' = Reduction_helper.collect_constraints derivation in
        Reduction_helper.close_constraints constr1'';
        begin
          (* Success: managed to prove the facts in hyp1_preds' *)
          Display.Text.display_inside_query_success constr1'';

          if !Param.html_output then
            begin
            Display.Html.display_inside_query_success constr1'';
            Display.LangHtml.close();
            Display.Html.print_line ("<A HREF=\"inside" ^ inums ^ ".html\">Inside query: proof succeeded</A>")
            end;

          f constr1''
        end
      with Not_found -> 
        begin
          (* Failure: could not prove some fact in hyp1_preds' *)
          Display.Text.print_line "Inside query: proof failed";

          if !Param.html_output then
            begin
            Display.Html.print_line "Inside query: proof failed";
            Display.LangHtml.close();
            Display.Html.print_line ("<A HREF=\"inside" ^ inums ^ ".html\">Inside query: proof failed</A>")
            end;

          raise Unify
        end
    )
  ) hyp1_events hyp2_events end_session_id ()

let rec implies_q restwork (hyp1, hyp1_q, concl1, constr1) (hyp2, concl2, _, constr2) =
  match_facts_eq (fun () ->
    let end_session_id =
      (* We require that there is at most one injective event before ==>
	 in the query, and we reorder the elements before ==> so that
	 this injective event comes first. As a result, the session
	 identifier of the injective event is always the first argument
	 of the fact, even when there are several elements before ==>.

	 If there were several injective events before ==>, 
	 we should have several end_session_id's and that would be
	 complicated. *)
      match concl2 with
        | Pred(_, (FunApp({f_cat = SpecVar i}, [])::_)) -> Some i
        | _ -> None
    in

    match_hyp_eq (fun constr1' ->
      begin
        try
          Terms.auto_cleanup (fun () ->
            TermsEq.implies_constra_list
            (List.map (fun f -> specvar_to_var_fact (TermsEq.remove_syntactic_fact f)) (concl2 :: hyp2))
            (List.map (fun c -> specvar_to_var_constra (TermsEq.remove_syntactic_constra c)) constr2)
            (List.map (fun c -> specvar_to_var_constra (TermsEq.remove_syntactic_constra c)) constr1') ()
          )
        with NoMatch -> raise Unify
      end;

      (* Instantiate the nested queries with the value given by the clause *)
      let hyp1_q' =
        Terms.auto_cleanup (fun () ->
          List.map (fun q ->
            let q' = copy_query q in
            enforce_query_vars q';
            let q'' = specvar_to_var_query q' in
            enforce_det_p q''; 
            q''
          ) hyp1_q
        )
      in

      check_occ_queries [] hyp1_q';

      (* Verify the nested queries *)
      let rec list_subqueries restwork = function
        | [] -> Terms.auto_cleanup restwork
        | (q::l) ->
            Terms.auto_cleanup (fun () ->
              if check_query (fun () ->
                list_subqueries restwork l) InsideNested true (RealQuery(q,[])) q != True
              then raise Unify
            )
      in

      list_subqueries restwork hyp1_q'
    ) (Rules.reorder hyp1) constr1 hyp2 end_session_id ()
  ) None concl1 concl2

(* Check if a query is true *)

and clause_match_elem restwork el cl h =
  let (_,concl,_,_) = event_list_to_clause el in
  let (hyp, hyp_q, constra, eq_left, eq_right) = events_to_hyp h in
  (* Replace all variables in the clause with constants "SpecVar" *)
  assert (!current_bound_vars == []);
  put_constants_rule cl;
  let cl' = copy_rule2 cl in
  cleanup();
  (* Check whether the clause matches the query *)
  try
    if eq_left != [] then
      Terms.auto_cleanup (fun () ->
        TermsEq.unify_modulo_list (fun () ->
          let (hyp2, hyp_q2, concl2, constra2) =
            Terms.auto_cleanup (fun () ->
              (List.map TermsEq.copy_remove_syntactic_fact hyp,
              List.map copy_query hyp_q,
              TermsEq.copy_remove_syntactic_fact concl,
              List.map TermsEq.copy_remove_syntactic_constra constra))
          in
          Terms.auto_cleanup (fun () ->
            implies_q restwork (hyp2, hyp_q2, concl2, constra2) cl'
          )
        ) eq_left eq_right
      )
    else
      implies_q restwork (hyp, hyp_q, concl, constra) cl';
    true
  with Unify ->
    false

and clauses_match restwork nested q clauses =
  (* when nested != InsideNested, restwork is always fun () -> () *)
  let list_started = ref false in
  let result =
    assert (!current_bound_vars == []);
    let q' = copy_query q in
    cleanup();

    let simple_query = is_simple_query q' in
    (* First check a simplified, non-nested, non-injective query *)

    let Before(el,l) as q'' = simplify_query q' in
    let recheck_fun = fun cl -> List.exists (clause_match_elem (fun () -> ()) el cl) l in
    let def_res = ref DontKnow in
    let res =
      List.for_all (fun cl ->
        let res = List.exists (clause_match_elem (fun () -> ()) el cl) l in
	      (* When res is false, the clause cl falsifies the query *)
        if (not res) && (display_clause_trace (not res) (Some recheck_fun) (Some q'') list_started cl) then def_res := False;
        res
      ) clauses
    in
    if (nested <> InsideNested) && (not simple_query) && (is_non_trivial q'') then
      supplemental_info := [q'', if res then True else !def_res];
    (* If the simplified query cannot be proved, then q cannot be proved either.
       If we could reconstruct a trace against the simplified query, then q is false *)
    if not res
    then !def_res
    else
      (* If q' is simple, then it is equal to its simplified query, so the result is known *)
      if simple_query
      then
        begin
          List.iter (fun cl -> ignore (display_clause_trace (not res) (Some recheck_fun) None list_started cl)) clauses;
          try restwork(); True with Unify -> DontKnow
        end
      else
        (* Otherwise, test the query q' itself *)
	let Before(el,l) = q' in
	if List.for_all (function
	    QSEvent(inj,_) -> not inj
	  | QFact _ -> true
	  | QEq _ | QNeq _ -> Parsing_helper.internal_error "Equalities and inequalities should not occur before ==> in queries") el
	then
	  (* q' is not an injective query. Since simplification just removes
             injectivity and nested queries, q' is a nested, non-injective query *)
          let res = List.for_all (fun cl ->
            let res = List.exists (clause_match_elem (fun () -> ()) el cl) l in
            let recheck_fun = fun cl -> List.exists (clause_match_elem (fun () -> ()) el cl) l in
            (* When res is false, the clause cl falsifies the query *)
            ignore (display_clause_trace (not res) (Some recheck_fun) (Some q') list_started cl);
	    res
	      ) clauses
	  in
          if res
          then
            try
              restwork(); True
            with Unify -> DontKnow
          else DontKnow
	else
	  (* injective query *)
	  match nested with
	  | InsideNested ->
	      let res = clauses_match_inj restwork q clauses in
	      List.iter (fun cl -> ignore (display_clause_trace (not res) None None list_started cl)) clauses;
	      if res then True else DontKnow
	  | TopNested ->
	      begin
		(* look at the simplified non-nested query first *)
		let q_non_nested = remove_nested q' in
		let result_non_nested = check_nonnested_inj_query false list_started q_non_nested clauses in
		match result_non_nested with
		| True ->
		    supplemental_info := [q_non_nested, result_non_nested];
		    (* When the simplified non-nested query is true, look at the real query *)
		    let res = clauses_match_inj restwork q clauses in
		    List.iter (fun cl -> ignore (display_clause_trace (not res) None None list_started cl)) clauses;
		    if res then True else DontKnow
		| DontKnow ->
		    supplemental_info := (q_non_nested, result_non_nested) :: (!supplemental_info);
		    DontKnow
		| False ->
		    supplemental_info := [q_non_nested, result_non_nested];
		    False
	      end
	  | NonNested ->
              (* the query is not nested *)
	      check_nonnested_inj_query true list_started q' clauses
  in
  if (!Param.html_output) && (!list_started) then
    Display.Html.print_string "</UL>\n";
  result

and clauses_match_inj restwork q clauses =
  assert (!current_bound_vars == []);
  let Before(el,l) = copy_query q in
  cleanup();
  match clauses with
    | [] ->
      begin
      	try
      	  restwork(); true
      	with Unify -> false
      end
  | (cl::cll) ->
      List.exists (clause_match_elem (fun () ->
        if not (clauses_match_inj restwork q cll) then raise Unify) el cl) l

and check_nonnested_inj_query display_true list_started q clauses =
  let Before(el,l) = q in
  let res = clauses_match_inj (fun () -> ()) q clauses in
  if res then 
    begin
      (* The query is true *)
      if display_true then
	List.iter (fun cl -> ignore (display_clause_trace false None None list_started cl)) clauses;
      True
    end
  else
    begin
      (* The query is not nested, try to investigate in more detail why the proof failed *)
      let reslist =
	match clauses with
	  [] -> []
	| [cl] -> [false]
	| _ -> 
            List.map (fun cl ->
              List.exists (clause_match_elem (fun () -> ()) el cl) l) clauses
      in
      if List.mem false reslist
      then
        begin
          (* A single clause falsifies the query; in this case, we display the derivation
             only for the clauses that falsify the query. We try to reconstruct a trace
             that falsifies injectivity. *)
          let recheck_fun = fun cl -> List.exists (clause_match_elem (fun () -> ()) el cl) l in
          let reslist_att = List.map2 (fun cl res1 ->
	    display_clause_trace (not res1) (Some recheck_fun) (Some q) list_started cl
	      ) clauses reslist
	  in
          if List.mem true reslist_att then False else DontKnow
        end
      else
        begin
          (* Several clauses simultaneously are needed to falsify the query.
             We display all derivations. *)
          List.iter (fun cl -> ignore (display_clause_trace true None None list_started cl)) clauses;
          DontKnow
        end
    end

    
	
and check_query restwork nested display_query qdisp (Before(el, hypll) as q) =
  (* when nested != InsideNested, restwork is always fun () -> () *)
  Display.Text.print_string "Starting query ";
  Display.Text.display_corresp_secret_putbegin_query qdisp;
  Display.Text.newline();
  if (!Param.html_output) && display_query then
    begin
      if nested = InsideNested then
    	begin
    	  Display.Html.print_string "Starting query ";
    	  Display.Html.display_corresp_secret_putbegin_query qdisp;
    	  Display.Html.newline()
    	end
      else
    	begin
    	  Display.Html.print_string "<LI><span class=\"query\">Query ";
    	  Display.Html.display_corresp_secret_putbegin_query qdisp;
    	  Display.Html.print_string "</span><br>\n"
    	end
    end;
  assert (!current_bound_vars == []);
  let clause = event_list_to_clause el in
  let clauses = Rules.resolve_hyp clause in
      (* Remove clauses subsumed modulo equational theory *)
      (* print_string ((string_of_int (List.length clauses)) ^ " clauses before subsumption modulo eq.\n"); *)
  let clauses =
    if (!Param.simpeq_final) && (TermsEq.hasEquations()) then
      remove_subsumed_mod_eq clauses
    else
      clauses
  in
      (* print_string ((string_of_int (List.length clauses)) ^ " clauses after subsumption modulo eq.\n");
         List.iter (fun cl ->
	print_string "clause after subsumption modulo eq: ";
	Display.Text.display_rule cl) clauses;*)
  clauses_match restwork nested q clauses

let do_query display_query (qorig, qencoded) =
  match qencoded with
  | PutBegin _ -> ()
  | RealQuery (Before(el, hypll) as q, []) ->
      let nested =
	if 
	  List.for_all (List.for_all (function NestedQuery _ -> false
	    | _ -> true)) hypll
	then NonNested
	else TopNested
      in
      let r = check_query (fun () -> ()) nested display_query qorig q in
      Display.Text.print_string "RESULT ";
      Display.Text.display_corresp_secret_putbegin_query qorig;
      Display.Text.print_string (get_res r);
      Display.Text.newline();
      if !Param.html_output then
	begin
	  Display.Html.print_string "<span class=\"result\">RESULT ";
	  Display.Html.display_corresp_secret_putbegin_query qorig;
	  Display.Html.print_string (get_html_res r);
	  Display.Html.print_string "</span>";
	  Display.Html.newline()
	end;
      if (!Param.tulafale <> 1) && (r != True) && ((!supplemental_info) != []) then
	begin
          if qorig != qencoded then
	    begin
	      (* The query was encoded, explain the encoding again, so
		 that the display of the supplemental results makes sense. *)
	      Display.Text.print_string "RESULT (query encoded as ";
	      Display.Text.display_corresp_secret_putbegin_query qencoded;
	      Display.Text.print_string ")";
	      Display.Text.newline();
	      if !Param.html_output then
		begin
		  Display.Html.print_string "<span class=\"result\">RESULT (query encoded as ";
		  Display.Html.display_corresp_secret_putbegin_query qencoded;
		  Display.Html.print_string ")</span>";
		  Display.Html.newline();
		end
	    end;
	  List.iter (fun (q',r') ->
	    Display.Text.print_string "RESULT (";
	    if r' == True then Display.Text.print_string "but " else Display.Text.print_string "even ";
	    Display.Text.display_corresp_query q';
	    Display.Text.print_string (get_res r');
	    Display.Text.print_string ")";
	    Display.Text.newline();
	    if !Param.html_output then
	      begin
		Display.Html.print_string "<span class=\"result\">RESULT (";
		if r' == True then Display.Html.print_string "but " else Display.Html.print_string "even ";
		Display.Html.display_corresp_query q';
		Display.Html.print_string (get_html_res r');
		Display.Html.print_string ")</span>";
		Display.Html.newline();
	      end
		) (!supplemental_info)
	end;
      supplemental_info := []
  | RealQuery _ | QSecret _ ->
      Parsing_helper.internal_error "Query secret and queries with public variables should have been encoded before Piauth.do_query"
      
	   
(* In a query 'F ==> H', F cannot contain function symbols 
   that can be reduced by the equational theory. 
   Same thing for the nested queries in H.

   This is difficult to check in pitsyntax.ml/pisyntax.ml
   because the equations are not translated yet into rewrite
   rules, so we do not know which symbols have (Eq l) with l <> []. *)
   
exception Bad_symbol_in_query of funsymb

let rec verify_Eq_not_in_term = function
  | Var _ -> ()
  | FunApp({f_cat = Eq l; _} as f,args)
     when l <> [] && (List.exists Terms.has_vars args) ->
       raise (Bad_symbol_in_query f)
  | FunApp(_,args) -> List.iter verify_Eq_not_in_term args

let verify_Eq_not_in_event = function
  | QSEvent(_,t) -> verify_Eq_not_in_term t
  | QFact(p,t_list) -> List.iter verify_Eq_not_in_term t_list
  | _ -> internal_error "no Neq and Eq queries"

let rec verify_Eq_not_in_hypelem = function
  | NestedQuery query -> verify_Eq_not_in_realquery query
  | _ -> ()

and verify_Eq_not_in_realquery = function
  | Before(el,hypelems) ->
      List.iter verify_Eq_not_in_event el;
      List.iter (List.iter verify_Eq_not_in_hypelem) hypelems

and verify_Eq_not_in_query = function
  | PutBegin _ | QSecret _ -> ()
  | RealQuery (real_query,_) -> verify_Eq_not_in_realquery real_query

let solve_auth horn_state pi_state =
  let queries =
    match pi_state.pi_process_query with
      SingleProcessSingleQuery(_, CorrespQuery ql) ->
       List.map (fun q -> (q,q)) ql
    | SingleProcessSingleQuery(_, CorrespQEnc qql) -> qql
    | _ ->
       Parsing_helper.internal_error "Unexpected process-query in piauth.ml"
  in
  List.iter (fun (_, query) ->
    try
      verify_Eq_not_in_query query
    with Bad_symbol_in_query f ->
      print_string "The following query contains the invalid function symbol ";
      Display.Text.display_function_name f;
      print_string ". In a query 'F ==> H', F cannot contain function symbols that can be reduced by the equational theory. Same thing for the nested queries in H.\n";
      Display.Text.display_corresp_secret_putbegin_query query;
      print_newline();
      user_error "Incorrect query"
  ) queries;
  init_clauses := horn_state.h_clauses;
  clauses_for_preds := None;
  Rules.corresp_initialize horn_state;
  match queries with
    | [q] -> do_query false q
    | _ ->
      if !Param.html_output then Display.Html.print_string "<UL>\n";
      List.iter (do_query true) queries;
      if !Param.html_output then Display.Html.print_string "</UL>\n"
