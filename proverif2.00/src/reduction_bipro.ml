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

(* Trace reconstruction
   This version of the trace reconstruction does not exploit the
   order of nodes in the derivation tree.
 *)
(* TO DO Test phases
   Should I use evaluated terms in the "comment" field?
 *)

open Types
open Pitypes
open Terms
open Reduction_helper

let made_forward_step = ref false
let failed_traces = ref 0

let debug_find_io_rule = ref false
let debug_backtracking = ref false
let debug_print s = ()
    (* print_string s;
     Display.Text.newline() *)

(* This exception is used in reduction_nobacktrack
   It is raised after a bunch of reductions to
   to get the final state after these reductions,
   while preventing backtracking on these reductions.*)
exception Reduced of (term * term) reduc_state

(* [Terms.auto_cleanup f] runs [f()], removing all links
   created by [f()], whether [f] terminates normally or
   with an exception

   [auto_cleanup_red] is a variant of this function that
   treats the exception [Reduced] specially. Indeed, in most
   cases, when an exception is raised, it is because we
   backtrack, so the links we have set must be removed,
   since we undo the reductions.
   However, the exception [Reduced] is different: for this
   exception, we want to get the final state, so the links
   must be kept.
*)

let auto_cleanup_red f =
  let tmp_bound_vars = !current_bound_vars in
  current_bound_vars := [];
  try
    let r = f () in
    List.iter (fun v -> v.link <- NoLink) (!current_bound_vars);
    current_bound_vars := tmp_bound_vars;
    r
  with
    Reduced s ->
      (* Do not delete the links when the exception [Reduced] is raised.
	 Keep them in [current_bound_vars] so that they are deleted later if needed *)
      current_bound_vars := List.rev_append tmp_bound_vars (!current_bound_vars);
      raise (Reduced s)
  | x ->
      List.iter (fun v -> v.link <- NoLink) (!current_bound_vars);
      current_bound_vars := tmp_bound_vars;
      raise x


(* Set when we should take the else branch of Get but we cannot
   because an element has already been inserted so that the in branch
   is taken. In this case, we try delaying the inserts. *)
let has_backtrack_get = ref false

exception No_result
(* We use the exception Unify for local failure *)

exception FailOneSideOnly

let make_bi_choice (t1, t2) = make_choice t1 t2

let get_choice = function
    FunApp({ f_cat = Choice }, [t1;t2]) -> (t1,t2)
  | _ -> Parsing_helper.internal_error "Choice term expected"

let equal_bi_terms_modulo (t1,t2) (t1',t2') =
  (equal_terms_modulo t1 t1') && (equal_terms_modulo t2 t2')

let is_true_test (t1,t2) =
  let r1 = equal_terms_modulo t1 Terms.true_term in
  let r2 = equal_terms_modulo t2 Terms.true_term in
  if r1 && r2 then true else
  if (not r1) && (not r2) then false else
  raise FailOneSideOnly

(* [bi_action action] executes action for both sides.
   [action] raises Unify when it fails.
   Raises FailOneSideOnly when one side of the action fails.
   Raises Unify when the action fails on both sides. *)

let bi_action action =
  try
    let t1 = action 1 in
    try
      let t2 = action 2 in
      (t1,t2)
    with Unify ->
	(* Left side succeeded, right side failed *)
	raise FailOneSideOnly
  with Unify ->
    (* Left side failed *)
    let _ = action 2 in
    (* Left side failed, right side succeeded *)
    raise FailOneSideOnly

let rev_name_subst_bi = function
    [t] -> let r = rev_name_subst t in (r,r)
  | [t1;t2] -> (rev_name_subst t1, rev_name_subst t2)
  | _ -> Parsing_helper.internal_error "Unexpected number of arguments for this predicate"

let get_term_type_bi = function
    [t] -> Terms.get_term_type t
  | [t1;t2] -> Terms.get_term_type t1
  | _ -> Parsing_helper.internal_error "Unexpected number of arguments for this predicate"

let get_min_choice_phase() = 
  match (!Param.current_state).pi_min_choice_phase with
  | Set min_phase -> min_phase
  | Unset -> Parsing_helper.internal_error "pi_min_choice_phase not set"
                                      
let build_mess_fact phase (tc1,tc2) (t1,t2) =
  if phase < get_min_choice_phase() then
    Pred(Param.get_pred(Mess(phase, Terms.get_term_type t1)), [tc1;t1])
  else
    Pred(Param.get_pred(MessBin(phase, Terms.get_term_type t1)), [tc1;t1;tc2;t2])

let build_table_fact phase (t1,t2) =
  if phase < get_min_choice_phase() then
    Pred(Param.get_pred(Table(phase)), [t1])
  else
    Pred(Param.get_pred(TableBin(phase)), [t1;t2])

(* Display clauses *)

let display_rule (n, sons, hsl, nl, concl) =
  print_string ("Rule " ^ (string_of_int n) ^ ": ");
  display_tag hsl nl;
  print_string "  ";
  Display.Text.display_rule (List.map (fun t -> copy_fact2 t) sons, copy_fact2 concl, Empty concl, []);
  Display.Text.newline()

(* Display the trace *)

let noninterftest_to_string = function
    ProcessTest _ -> " process performs a test that may succeed on one side and not on the other"
  | InputProcessTest _ -> "The pattern-matching in the input succeeds on one side and not on the other."
  | NIFailTest _ -> "This holds on one side and not on the other."
  | ApplyTest _ -> Parsing_helper.internal_error "There should be no ApplyTest in reduction_bipro.ml"
  | CommTest _ -> "The communication succeeds on one side and not on the other."
  | NIEqTest _ -> "The result in the left-hand side is different from the result in the right-hand side."

let display_trace final_state =
  match !Param.trace_display with
    Param.NoDisplay -> ()
  | Param.ShortDisplay ->
      if !Param.html_output then
	Display.Html.display_labeled_trace final_state
      else
	begin
	  if !Param.display_init_state then
	    begin
	      print_string "A more detailed output of the traces is available with\n";
	      if !Param.typed_frontend then
		print_string "  set traceDisplay = long.\n"
              else
		print_string "  param traceDisplay = long.\n";
	      Display.Text.newline()
	    end;
	  Display.Text.display_labeled_trace final_state
	end
  | Param.LongDisplay ->
      if !Param.html_output then
	ignore (Display.Html.display_reduc_state Display.bi_term_to_term true final_state)
      else
	ignore (Display.Text.display_reduc_state Display.bi_term_to_term true final_state)


(* Find a clause *)

let find_io_rule next_f hypspeclist hyplist name_params var_list io_rules =
  let name_params1 = extract_name_params_noneed name_params in
  let l = List.length hypspeclist in
  let lnp = List.length name_params1 in
  let lh = List.length hyplist in
  (* Useful for debugging *)
  if !debug_find_io_rule then
    begin
      auto_cleanup (fun () ->
	print_string "Looking for ";
	display_tag hypspeclist name_params1;
	print_string "  ";
	Display.Text.display_list Display.Text.WithLinks.fact " & " hyplist;
	Display.Text.newline())
    end;
  let found_terms = ref [] in
  let rec find_io_rule_aux = function
    [] -> raise Unify
  | ((n, sons, hypspeclist2, name_params',_)::io_rules) ->
      let l2 = List.length hypspeclist2 in
      let lnp2 = List.length name_params' in
      let lh2 = List.length sons in
      if (l2 < l) || (lnp2 < lnp) || (lh2 < lh) || (not (hypspeclist = skip (l2-l) hypspeclist2))
      then find_io_rule_aux io_rules
      else
        begin
	  let sons3 = skip (lh2-lh) sons in
	  try
	    let name_params2 = skip (lnp2-lnp) name_params' in
	    if not (Param.get_ignore_types()) &&
	      (List.exists2 (fun t1 t2 -> Terms.get_term_type t1 != Terms.get_term_type t2) name_params1 name_params2) then
	      raise Unify;
	    auto_cleanup_red (fun () ->
	      match_modulo_list (fun () ->
	        match_equiv_list (fun () ->
                  let new_found = List.map copy_closed_remove_syntactic var_list in
	          if List.exists (fun old_found ->
	            List.for_all2 equal_terms_modulo old_found new_found) (!found_terms) then
	            raise Unify;
	          found_terms := new_found :: (!found_terms);
		  if !debug_find_io_rule then
		    begin
		      auto_cleanup (fun () ->
			print_string "Found ";
			Display.Text.display_list Display.Text.WithLinks.term ", " new_found;
			Display.Text.newline())
		    end;
	          next_f new_found) sons3 hyplist
                  ) name_params1 name_params2
		)
          with Unify -> find_io_rule_aux io_rules
        end
  in
  find_io_rule_aux io_rules

(* Evaluate a term possibly containing destructors.
   It always succeeds, perhaps returning Fail.  *)

let rec term_evaluation side = function
    Var v ->
      begin
        match v.link with
          TLink t ->
	    (* I think this is useful only to split a Choice inside t *)
	    term_evaluation side t
        | _ -> Parsing_helper.internal_error "Error: term should be closed in attack reconstruction";
      end
  | FunApp(f,l) ->
      (* for speed, use the initial definition of destructors, not the one enriched with the equational theory *)
      match f.f_initial_cat with
	Eq _ | Tuple ->
	  let l' = List.map (term_evaluation side) l in
	  if List.exists is_fail l' then
	    Terms.get_fail_term (snd f.f_type)
	  else
	    FunApp(f, l')
      | Name _ | Failure -> FunApp(f,[])
      |	Choice ->
	  begin
	    match l with
	      [t1;t2] ->
		if side = 1 then
		  term_evaluation side t1
		else
		  term_evaluation side t2
	    | _ -> Parsing_helper.internal_error "Choice should have two arguments"
	  end
      | Red redl ->
	  let l' = List.map (term_evaluation side) l in
	  let rec try_red_list = function
	      [] ->
		Parsing_helper.internal_error "Term evaluation should always succeeds (perhaps returning Fail)"
	    | (red1::redl) ->
		let (left, right, side_c) = auto_cleanup (fun () -> Terms.copy_red red1) in
		try
		  auto_cleanup (fun () ->
		    match_modulo_list (fun () ->
		      if List.for_all disequation_evaluation side_c then
			begin
		        (* TO DO (for speed) should I remove_syntactic, or keep it,
			   but take it into account elsewhere (when doing
			   function symbol comparisons, accept functions that
			   differ by their syntactic status) *)
			  close_term right;
 		          TermsEq.remove_syntactic_term right
			end
		      else
			raise Unify
	             ) left l')
		with Unify -> try_red_list redl
	  in
	  try_red_list redl
      | _ ->
        Printf.printf "\nName of the function:";
        Display.Text.display_function_name f;
        Parsing_helper.internal_error "unexpected function symbol in term_evaluation (reduction_bipro.ml)"

(* Evaluates t1 and tests if it is equal to t2. *)

let equal_terms_modulo_eval t1 t2 =
  let t1_l = term_evaluation 1 t1 in
  let t1_r = term_evaluation 2 t1 in
  if (is_fail t1_l) || (is_fail t1_r) then false else
  equal_bi_terms_modulo (t1_l, t1_r) t2


(* Evaluates a term. Raises Unify when the result is fail. *)

let term_evaluation_fail t side =
  let r = term_evaluation side t in
  if is_fail r then
    raise Unify
  else
    r

let term_evaluation_fail2 t1 t2 side =
  (term_evaluation_fail t1 side, term_evaluation_fail t2 side)

let term_evaluation_name_params occ t name_params =
  let may_have_several_patterns = reduction_check_several_patterns occ in
  let t' = bi_action (term_evaluation_fail t) in
  if may_have_several_patterns then
    t', ((MUnknown,make_bi_choice t',Always) :: name_params)
  else
    t', name_params

let term_evaluation_to_true t side =
  let r = term_evaluation side t in
  if (is_fail r) || (not (equal_terms_modulo r Terms.true_term)) then
    raise Unify
  else
    r

let term_evaluation_name_params_true occ t name_params =
  let may_have_several_patterns = reduction_check_several_patterns occ in
  let t' = bi_action (term_evaluation_to_true t) in
  if may_have_several_patterns then
    ((MUnknown,make_bi_choice t',Always) :: name_params)
  else
    name_params

(* Match a pattern
   Raises Unify when the matching fails *)

let rec match_pattern p side t =
  if not (Terms.equal_types (Terms.get_pat_type p) (Terms.get_term_type t)) then
    raise Unify;
  match p with
    PatVar b ->
      begin
	if side = 1 then
	  Terms.link b (TLink (make_choice t t))
	else
	  match b.link with
	    TLink (FunApp({ f_cat = Choice }, [t1;t2])) ->
	      Terms.link b (TLink (make_choice t1 t))
	  | _ ->
	      (* When the evaluation or pattern matching failed on the left side,
	         some variables may be unbounded when we try the pattern matching
	         on the right side *)
	      Terms.link b (TLink (make_choice t t))
      end
  | PatTuple(f,l) ->
      let vl = Terms.var_gen (fst f.f_type) in
      let tl =
	match_modulo (fun () ->
	  List.map copy_closed_remove_syntactic vl) (FunApp(f, vl)) t
      in
      List.iter2 (fun p t -> match_pattern p side t) l tl
  | PatEqual t' ->
      let t'' = term_evaluation_fail t' side in
      match_modulo (fun () -> ()) t'' t

let bi_match_pattern p (t1,t2) side =
  if side = 1 then
    match_pattern p side t1
  else
    match_pattern p side t2

let bi_match_pattern_and_test p (t1,t2) t side =
  bi_match_pattern p (t1,t2) side;
  let t' = term_evaluation_fail t side in
  if not (equal_terms_modulo t' Terms.true_term) then
    raise Unify

let term_evaluation_name_params_and_match pat occ t name_params =
  let may_have_several_patterns = reduction_check_several_patterns occ in
  let t'' = bi_action (fun side ->
    let t' = term_evaluation_fail t side in
    match_pattern pat side t';
    t')
  in
  if may_have_several_patterns then
    t'', ((MUnknown,make_bi_choice t'',Always) :: name_params)
  else
    t'', name_params

(*
   Terms come with a recipe that explains how to compute them.
   Recipes may contain variables (especially in prepared_attacker_rules)
   which are later instantiated by putting links in these variables.
   Copies of the recipes are not made immediately after creating the links,
   so these links remain when the trace progresses; they are removed
   in case of backtrack (by auto_cleanup_red).
   Not making too many copies is important for speed in complex
   examples such as ffgg.
   Copies of recipes are made before adding a term to public,
   so that recipes in public do not contain links.
   They are also made before using a term in an input.
*)

(* Decompose tuples *)

let rec decompose_term ((recipe, t) as pair:Types.term * (Types.term * Types.term)) =
  match t with
    (FunApp({f_cat = Tuple } as f,l), FunApp({f_cat = Tuple} as f',l')) when f == f' ->
      let projs = Terms.get_all_projection_fun f in
      decompose_list (List.map2 (fun fi ti -> (FunApp(fi,[recipe]),ti))
                      projs (List.combine l l'))
   | _ -> [pair]

and decompose_list = function
    [] -> []
  | (a::l) -> (decompose_term a) @ (decompose_list l)


let rec decompose_term_rev (binder, t) =
  match t with
    (FunApp({f_cat = Tuple } as f,l), FunApp({f_cat = Tuple} as f',l')) when f == f' ->
      let new_list = List.map (fun (x, x') -> ((Terms.new_var "~M" (Terms.get_term_type x)), (x, x')))
	  (List.combine l l')
      in
      Terms.link binder (TLink (FunApp(f, (List.map (fun (x, y) -> Var x) new_list))));
      decompose_list_rev new_list
  | t -> [(binder, t)]

and decompose_list_rev = function
    [] -> []
  | (a::l) -> (decompose_term_rev a) @ (decompose_list_rev l)



(* Test if a term is public *)

let rec is_in_public public = function
  | (FunApp({f_cat = Tuple} as f, l), FunApp(f',l')) when f == f' ->
      (match (is_in_public_list public) (List.combine l l') with
        | None -> None
        | Some lst -> Some(FunApp(f, lst)))
  | t ->
      try
        let (ca, _) = List.find (fun (_, t') -> equal_bi_terms_modulo t t') public in
        Some ca
      with Not_found ->
        None

and is_in_public_list public = function
    [] -> Some []
  | hd::tail ->
      match is_in_public public hd with
	None -> None
      | Some ca ->
        match is_in_public_list public tail with
	  None -> None
	| Some catail -> Some (ca::catail)



let rec remove_first_in_public public = function
    [] -> []
  | (((c, a)::l) as l') ->
      try
        let (ca, _) = List.find (fun (_, t) -> equal_bi_terms_modulo a t) public in
        Terms.link c (TLink ca);
        remove_first_in_public public l
      with Not_found ->
        l'


let update_term_list oldpub public tc_list =
  match tc_list with
    [] -> []
  | ((c0, t0)::l0) ->
    let rec is_in_until = function
	[] -> false
      | (((ca, a)::l) as public) ->
	if public == oldpub then false else
          if equal_bi_terms_modulo a t0
          then
            begin
              Terms.link c0 (TLink ca);
              true
            end
          else
	    is_in_until l
    in
    if is_in_until public then
      remove_first_in_public public l0
    else
      tc_list


(* We maintain the following invariants in public and prepared_attacker_rule:
   1/ All rules in prepared_attacker_rule are for a phase later or equal to the current one.
      Rules for a previous phase are removed.
   2/ All rules in prepared_attacker_rule for the current phase have non-empty assumptions.
      Rules with empty assumptions are removed after adding their conclusion to public.
   3/ All assumptions of rules in prepared_attacker_rule are not in public.
      When an assumption is in public, we remove it, and possibly apply 2/.

[add_public_and_close state l] guarantees that these invariants are preserved after
addition of the terms in [l] to public. 
It removes assumptions of rules in prepared_attacker_rule that are in [l].
When a rule then has no assumptions and is for the current phase, it adds the
conclusion to public and continues closing recursively.

*)

let add_public_and_close state l =
  let queue = ref l in
  let rec remove_from_att_rules public ((recipe, t) as pair) = function
      [] -> []
    | (p, hyp_terms, (recipe_concl, concl_bi_term))::attacker_rules ->
	let attacker_rules' = remove_from_att_rules public pair attacker_rules in
	let phase_p = getphase p in
	assert (phase_p >= state.current_phase);
	let hyp_terms' = match hyp_terms with
	  [] -> []
	| ((c0, t0)::l0) ->
	    if equal_bi_terms_modulo t0 t then
	      begin
		link c0 (TLink recipe);
		remove_first_in_public public l0
	      end
	    else
	      hyp_terms
	in
	if (hyp_terms' = []) && (phase_p = state.current_phase) then
	  begin
	    queue := (decompose_term (Terms.copy_term4 recipe_concl, concl_bi_term)) @ (!queue);
	    attacker_rules'
	  end
	else
	  (* Keep the rule, removing hypotheses that are already in public *)
	  (p, hyp_terms', (recipe_concl, concl_bi_term)) :: attacker_rules'
  in
  let rec do_close state =
    match !queue with
      [] -> state
    | ((c, t)::l) ->
	queue := l;
	if List.exists (fun (_, t') -> equal_bi_terms_modulo t t') state.public then
	  do_close state
	else
	  let public' = (c, t) :: state.public in
	  do_close { state with
                     public = public';
                     prepared_attacker_rule = remove_from_att_rules public' (c, t) state.prepared_attacker_rule }
  in
  do_close state

let rec add_public_with_recipe state (recipe, t) =
  match t with
    (FunApp({ f_cat = Tuple } as f, l), FunApp({f_cat = Tuple} as f',l')) when f == f' ->
       let projs = Terms.get_all_projection_fun f in
       add_public_list state (List.map2 (fun fi ti -> (FunApp(fi, [recipe]), ti)) projs (List.combine l l'))
  | t -> add_public_and_close state [(recipe, t)]

and add_public_list state = function
    [] -> state
  | (a::l) -> add_public_list (add_public_with_recipe state a) l

(* [close_public_after_phase_increment state] guarantees that the invariants on
   public and prepared_attacker_rule mentioned above are preserved after a phase increment.
   It removes rules for previous phases, adds to public the conclusions
   of rules with no assumptions in the new phase, and closes using
   [add_public_and_close]. *)

let close_public_after_phase_increment state =
  let queue = ref [] in
  let rec remove_from_att_rules public = function
      [] -> []
    | ((p, hyp_terms, (recipe_concl, concl_bi_term)) as rule)::attacker_rules ->
	let attacker_rules' = remove_from_att_rules public attacker_rules in
	let phase_p = getphase p in
	if phase_p < state.current_phase then attacker_rules' else
	if (hyp_terms = []) && (phase_p = state.current_phase) then
	  begin
	    queue := (decompose_term (Terms.copy_term4 recipe_concl, concl_bi_term)) @ (!queue);
	    attacker_rules'
	  end
	else
	  (* Keep the rule *)
	  rule :: attacker_rules'
  in
  let state' =
    { state with
      prepared_attacker_rule = remove_from_att_rules state.public state.prepared_attacker_rule }
  in
  add_public_and_close state' (!queue)

(* [close_public_phase_change state n] changes the current phase to [n]
   after closes public, by incrementing the phase from [state.current_phase] to [n]
   and closing by [close_public_after_phase_increment] at each increment. *)
    
let rec close_public_phase_change state n =
  if n < state.current_phase then
    Parsing_helper.internal_error "Phases should be in increasing order.";
  if n = state.current_phase then state else
  let state1 = { state with current_phase = state.current_phase + 1 } in
  let state2 = close_public_after_phase_increment state1 in
  close_public_phase_change state2 n

(* [close_public_initial state] guarantees that the invariants on
   public and prepared_attacker_rule mentioned above are true initially.
   It applies rules with empty assumptions in phase 0 by
   [close_public_after_phase_increment] and 
   closes with terms initially known to be public by 
   [add_public_list]. *)
    
let close_public_initial state =
  let state0 = { state with public = [] } in
  let state1 = close_public_after_phase_increment state0 in
  add_public_list state1 state.public


let add_public state t =
  let new_recipe = new_var "~M" (get_term_type (fst t)) in
  let l = decompose_term_rev (new_recipe, t) in
  let l' = List.map (fun (b,t) -> (Var b, t)) l in
  let state' = add_public_and_close state l' in
  (Terms.copy_term4 (Var new_recipe), state')

(* Do reductions that do not involve interactions
   f takes as input
      - a boolean indicating whether the attacker knowledge has changed
      - the new state

   When the goal is reached, do_red_nointeract returns the final state.
   Otherwise, raises an exception No_result.
*)

let rec do_red_nointeract f prev_state n =
  let (proc, name_params, occs, facts, cache_info) =
	 List.nth prev_state.subprocess n in
  match proc with
    Nil -> debug_print "Doing Nil";
      made_forward_step := true;
      f false { prev_state with
	             subprocess = remove_at n prev_state.subprocess;
                     comment = RNil(n);
                     previous_state = Some prev_state }
  | Par(p,q) ->
      debug_print "Doing Par";
      made_forward_step := true;
      do_red_nointeract (fun new_att_know cur_state2 ->
        do_red_nointeract (fun new_att_know2 cur_state3 ->
             f (new_att_know || new_att_know2) cur_state3)
          cur_state2 n
        ) { prev_state with
	    subprocess = add_at n (p, name_params, occs, facts, Nothing)
	                (replace_at n (q, name_params, occs, facts, Nothing)
                         prev_state.subprocess);
            comment = RPar(n);
            previous_state = Some prev_state } (n+1)
  | Restr(na,(args,env),p,occ) ->
      debug_print "Doing Restr";
      made_forward_step := true;
      let need_list = get_need_vars (!Param.current_state) na.f_name in
      let include_info = prepare_include_info env args need_list in
      let l = extract_name_params na.f_name include_info name_params in
      let n' = FunApp(add_name_for_pat (FunApp(na, l)),[]) in
      let p' = process_subst p na n' in
      begin
	do_red_nointeract f { prev_state with
	    subprocess = replace_at n (p', name_params, occs, facts, Nothing) prev_state.subprocess;
            comment = RRestr(n, na, n');
            previous_state = Some prev_state } n
      end
  | Let(pat,t,p,q,occ) ->
      debug_print "Doing Let";
      made_forward_step := true;
      let new_occs = (LetTag occ) :: occs in
      begin
      try
        auto_cleanup_red (fun () ->
          let t', name_params' = term_evaluation_name_params_and_match pat (OLet(occ)) t name_params in
          let p' = copy_process p in
          let name_params'' = update_name_params IfQueryNeedsIt name_params' pat in
          do_red_nointeract f { prev_state with
	    subprocess = replace_at n (p', name_params'', new_occs, facts, Nothing) prev_state.subprocess;
            comment = RLet1(n, pat, make_bi_choice t');
            previous_state = Some prev_state } n
        )
      with Unify ->
        do_red_nointeract f { prev_state with
	  subprocess = replace_at n (q, name_params, new_occs, facts, Nothing) prev_state.subprocess;
          comment = RLet2(n, pat, t);
          previous_state = Some prev_state } n
      | FailOneSideOnly ->
	  (* SUCCESS *)
	  { prev_state with
            goal = NonInterfGoal(ProcessTest([],[],(Some(n, List.nth prev_state.subprocess n)))) }
      end
  | Test(t,p,q,occ) ->
      debug_print "Doing Test";
      made_forward_step := true;
      if q == Nil then
	(* Optimize the case q == Nil: in this case, the adversary
	   cannot distinguish whether a destructor fails in t or
	   t is false. *)
	begin
	try
          auto_cleanup_red (fun () ->
	    let new_occs = (TestTag occ) :: occs in
            let name_params' = term_evaluation_name_params_true (OTest(occ)) t name_params in
	    do_red_nointeract f
		    { prev_state with
	              subprocess = replace_at n (p, name_params', new_occs, facts, Nothing) prev_state.subprocess;
                      comment = RTest1(n, t);
                      previous_state = Some prev_state } n
	      )
        with Unify ->
	  f false { prev_state with
	      subprocess = remove_at n prev_state.subprocess;
              comment = RTest2(n, t);
              previous_state = Some prev_state }
        | FailOneSideOnly ->
	  (* SUCCESS *)
	  { prev_state with
            goal = NonInterfGoal(ProcessTest([],[],(Some(n, List.nth prev_state.subprocess n)))) }
	end
      else
	begin
	try
          auto_cleanup_red (fun () ->
	    let new_occs = (TestTag occ) :: occs in
            let (t', name_params') = term_evaluation_name_params (OTest(occ)) t name_params in
            if is_true_test t' then
	      do_red_nointeract f
		    { prev_state with
	              subprocess = replace_at n (p, name_params', new_occs, facts, Nothing) prev_state.subprocess;
                      comment = RTest1(n, t);
                      previous_state = Some prev_state } n
            else
              do_red_nointeract f
		    { prev_state with
	              subprocess = replace_at n (q, name_params', new_occs, facts, Nothing) prev_state.subprocess;
                      comment = RTest2(n, t);
                      previous_state = Some prev_state } n
		)
        with Unify ->
	  f false { prev_state with
	      subprocess = remove_at n prev_state.subprocess;
              comment = RTest3(n, t);
              previous_state = Some prev_state }
        | FailOneSideOnly ->
	  (* SUCCESS *)
	  { prev_state with
            goal = NonInterfGoal(ProcessTest([],[],(Some(n, List.nth prev_state.subprocess n)))) }
	end
  | Output(tc,t,p,occ) ->
      let new_goal_opt =
	if cache_info != Nothing then
	  None (* Was already tested and failed before; will still fail if tested again *)
	else
	  match prev_state.goal with
	    NonInterfGoal(CommTest(tin,tout,loc)) ->
	    if equal_terms_modulo_eval tc tout then
	      begin
         	 (match is_in_public prev_state.public tin with
                   Some (recipe) ->
	              begin
		        let new_loc = Some (LocAttacker (recipe), LocProcess(n, List.nth prev_state.subprocess n)) in
			Some (NonInterfGoal(CommTest(tin,tout,new_loc)))
                      end
                   | None ->  (* find a process that does some input on tin *)
		       try
	                  let (n',p') =
		            findi (function
			      (Input(tc,_,_,_),_,_,_,_) -> equal_terms_modulo_eval tc tin
			    | _ -> false
			   ) prev_state.subprocess
		          in
	                  let new_loc = Some (LocProcess(n',p'), LocProcess(n, List.nth prev_state.subprocess n)) in
			  Some (NonInterfGoal(CommTest(tin,tout,new_loc)))
	                with Not_found ->
		    None)
		end
	      else None
	  | _ -> None
      in
      begin
	match new_goal_opt with
	  Some new_goal -> { prev_state with goal = new_goal }
	| None ->
	debug_print "Doing Output";
        (* For passive attackers, do red I/O only,
	   but still evaluate the arguments of the output *)
	if not (!Param.active_attacker) then
	  match cache_info with
	    InputInfo _ | GetInfo _ -> Parsing_helper.internal_error "Should not have input/get info for an output!"
	  | OutputInfo _ -> f false prev_state (* Arguments already evaluated *)
	  | Nothing ->
	      try
		auto_cleanup_red (fun () ->
		  let ((tc1,t1),(tc2,t2)) = bi_action (term_evaluation_fail2 tc t) in
		  let tc' = (tc1, tc2) in
		  let t' = (t1, t2) in
		  let tclist = decompose_term_rev (Terms.new_var "Useless" (Terms.get_term_type tc1), tc') in
		  f false { prev_state with
                            subprocess = replace_at n (Output(make_bi_choice tc', make_bi_choice t',p,occ),
						       name_params, occs, facts,
						       (OutputInfo(tclist, prev_state.public)))
                                     prev_state.subprocess }
		    )
              with Unify ->
	        f false { prev_state with
                      subprocess = remove_at n prev_state.subprocess;
                      comment = ROutput2(n, tc, t);
                      previous_state = Some prev_state }
              | FailOneSideOnly ->
	          (* SUCCESS *)
		  { prev_state with
                    goal = NonInterfGoal(ProcessTest([],[],(Some(n, List.nth prev_state.subprocess n)))) }

	else
        (* For active attackers, one can output on public channels *)
	begin
	  let new_occs = (OutputTag occ) :: occs in
	  match cache_info with
	    InputInfo _ | GetInfo _ -> Parsing_helper.internal_error "Should not have input/get info for an output!"
	  | OutputInfo(tclist, oldpub) ->
	      let tclist' = update_term_list oldpub prev_state.public tclist in
	      if tclist' = [] then
	         begin
		   made_forward_step := true;
       		   let (new_recipe, prev_state') = add_public prev_state (get_choice t) in
		   do_red_nointeract (if prev_state.public == prev_state'.public then f else
		  (fun mod_public cur_state -> f true cur_state))
		    { prev_state' with
                      subprocess = replace_at n (p, name_params, new_occs, facts, Nothing) prev_state.subprocess;
                      comment = ROutput1(n, tc, new_recipe, t);
		      previous_state = Some prev_state } n
		end
	      else
		f false { prev_state with
                          subprocess = replace_at n (proc, name_params, occs, facts,
						     (OutputInfo(tclist', prev_state.public)))
                                         prev_state.subprocess }
	  | Nothing ->
	      try
		auto_cleanup_red (fun () ->
		  let ((tc1,t1),(tc2,t2)) = bi_action (term_evaluation_fail2 tc t) in
		  let tc' = (tc1, tc2) in
		  let t' = (t1, t2) in
		  let tclist = decompose_term_rev (Terms.new_var "Useless" (Terms.get_term_type tc1), tc') in
		  let tclist' = remove_first_in_public prev_state.public tclist in
		  if tclist' = [] then
		    begin
                      made_forward_step := true;
		      let (new_recipe, prev_state') = add_public prev_state t' in
		      do_red_nointeract (if prev_state.public == prev_state'.public then f else
		      (fun mod_public cur_state -> f true cur_state))
			      { prev_state' with
                                  subprocess = replace_at n (p, name_params, new_occs, facts, Nothing) prev_state.subprocess;
			          comment = ROutput1(n, make_bi_choice tc', new_recipe, make_bi_choice t');
			          previous_state = Some prev_state } n
		    end
		  else
		    (* When one side is a channel and the other side is not,
                       we keep the Output process; the failure of the equivalence
                       will be detected (or has already been detected) by CommTest *)
		    f false { prev_state with
                              subprocess = replace_at n (Output(make_bi_choice tc', make_bi_choice t',p,occ), name_params, occs, facts,
							 (OutputInfo(tclist', prev_state.public)))
                                               prev_state.subprocess }
			  )
              with Unify ->
	        f false { prev_state with
                      subprocess = remove_at n prev_state.subprocess;
                      comment = ROutput2(n, tc, t);
                      previous_state = Some prev_state }
              | FailOneSideOnly ->
	          (* SUCCESS *)
		  { prev_state with
                    goal = NonInterfGoal(ProcessTest([],[],(Some(n, List.nth prev_state.subprocess n)))) }
	end
      end
  | Event(FunApp(fs,l) as t,_,p,occ) ->
      debug_print "Doing Event";
      made_forward_step := true;
      begin
	 (* Check that the argument of the event can be evaluated but otherwise ignore it *)
	try
	  auto_cleanup_red (fun () ->
	    let t' = bi_action (term_evaluation_fail t) in
	    do_red_nointeract f { prev_state with
	                        subprocess = replace_at n (p, name_params, occs, facts, Nothing) prev_state.subprocess;
	                        comment = REvent1(n, make_bi_choice t', false);
	                        previous_state = Some prev_state } n
	      )
        with Unify ->
	  f false { prev_state with
                    subprocess = remove_at n prev_state.subprocess;
		    comment = REvent2(n, t);
		    previous_state = Some prev_state }
        | FailOneSideOnly ->
	  (* SUCCESS *)
	  { prev_state with
            goal = NonInterfGoal(ProcessTest([],[],(Some(n, List.nth prev_state.subprocess n)))) }
      end
  | LetFilter(bl, Pred(pr,l), p, q, occ) ->
      Parsing_helper.user_error "Predicates are currently incompatible with non-interference."
  | Repl(p,occ) ->
      debug_print "Doing Repl";
      made_forward_step := true;
      let sid = Terms.new_var "sid" Param.sid_type in
      let new_occs = (ReplTag (occ,count_name_params name_params))::occs in
      let copy_number = ref 0 in
      let new_state = ref { prev_state with
	                    subprocess = remove_at n prev_state.subprocess;
                            comment = RRepl(n,0);
                            previous_state = Some prev_state }
      in
      begin
      try
        auto_cleanup (fun () ->
          find_io_rule (function
             [sid_pat] ->
                    let p' = auto_cleanup (fun () -> copy_process p) in
                    incr copy_number;
                    new_state := { !new_state with
                            subprocess = add_at n (p', (MSid 0,sid_pat,Always)::name_params, new_occs, facts, Nothing) !new_state.subprocess
                          };
                    raise Unify
           | _ -> Parsing_helper.internal_error "Repl case, reduction.ml"
	     ) new_occs facts ((MSid 0,Var sid,Always)::name_params) [Var sid] prev_state.io_rule
           )
      with Unify ->
	debug_print ("Repl: " ^ (string_of_int (!copy_number)) ^ " copies");
        let rec do_red_copies b ncopies state =
          if ncopies < 0 then
            f b state
          else
            do_red_nointeract (fun b' s -> do_red_copies (b||b') (ncopies-1) s) state (n+ncopies)
	in
	do_red_copies false ((!copy_number)-1)
          { !new_state with
            comment = RRepl(n,!copy_number)
          }
     end
  | Input(tc,_,_,_) ->
      begin
	match prev_state.goal with
	  NonInterfGoal(CommTest(tin,tout,loc)) ->
	    if equal_terms_modulo_eval tc tin then
	      begin
		(match  is_in_public prev_state.public tout with
              | Some recipe ->
                  begin
		    let new_loc = Some (LocProcess(n, List.nth prev_state.subprocess n), LocAttacker recipe) in
		    let new_goal = NonInterfGoal(CommTest(tin,tout,new_loc)) in
		    { prev_state with goal = new_goal }
		  end
	      | None ->  (* find a process that does some output on tout *)
		  try
		    let (n',p') =
		      findi (function
			  (Output(tc,_,_,_),_,_,_,_) -> equal_terms_modulo_eval tc tout
			| _ -> false
			      ) prev_state.subprocess
		    in
		    let new_loc = Some (LocProcess(n, List.nth prev_state.subprocess n), LocProcess(n',p')) in
		    let new_goal = NonInterfGoal(CommTest(tin,tout,new_loc)) in
		    { prev_state with goal = new_goal }
		  with Not_found ->
		    f false prev_state)
	      end
	    else f false prev_state
	| _ -> f false prev_state

      end
  | Insert(t,p,occ) ->
      debug_print "Doing Insert";
      begin
	let new_occs = (InsertTag occ) :: occs in
	let new_element_inserted = ref false in
	try
	  auto_cleanup_red (fun () ->
	    let t' = bi_action (term_evaluation_fail t) in
	    let already_in = List.exists (equal_bi_terms_modulo t') prev_state.tables in
	    new_element_inserted := not already_in;
	    made_forward_step := true;
	    do_red_nointeract f
		  { prev_state with
                    subprocess = replace_at n (p, name_params, new_occs, facts, Nothing) prev_state.subprocess;
	            tables = if already_in then prev_state.tables else t'::prev_state.tables;
		    comment = RInsert1(n, make_bi_choice t', false);
	            previous_state = Some prev_state } n
	      )
        with Unify ->
	  f false { prev_state with
                    subprocess = remove_at n prev_state.subprocess;
                    comment = RInsert2(n, t);
                    previous_state = Some prev_state }
        | FailOneSideOnly ->
	    (* SUCCESS *)
	    { prev_state with
              goal = NonInterfGoal(ProcessTest([],[],(Some(n, List.nth prev_state.subprocess n)))) }
	| No_result ->
	    (* The attack reconstruction failed after doing the insert.
	       Try not doing it, in case that allows executing the else branch of a Get. *)
	    if (!has_backtrack_get) && (!new_element_inserted) then
	      f false prev_state
	    else
	      raise No_result
      end
  | NamedProcess(name, tl, p) ->
    debug_print "Doing NamedProcess";
    do_red_nointeract  f { prev_state with
      subprocess = replace_at n (p, name_params, occs, facts, Nothing) prev_state.subprocess;
      comment = RNamedProcess(n, name, tl);
      previous_state = Some prev_state } n

  | _ -> f false prev_state


(* Test success when the knowledge of the attacker has changed *)

let test_success cur_state' =
  try
    match cur_state'.goal with
      NonInterfGoal(NIEqTest((t1, _),(t2, _))) ->
        (match is_in_public cur_state'.public t1, is_in_public cur_state'.public t2 with
        | Some recipe1, Some recipe2 ->
	    let new_goal = NonInterfGoal(NIEqTest((t1, Some recipe1),(t2, Some recipe2))) in
	    (true, { cur_state' with goal = new_goal })
          | _ -> (false, cur_state'))
    | NonInterfGoal(NIFailTest (t, _)) ->
	(match is_in_public cur_state'.public t with
	| Some recipe ->
	    let new_goal = NonInterfGoal(NIFailTest (t, Some recipe)) in
	    (true, { cur_state' with goal = new_goal })
	| None -> (false, cur_state'))
    | NonInterfGoal(CommTest(tin,tout,loc)) ->
	let rin =
           (match is_in_public cur_state'.public tin with
           | Some recipe -> Some (LocAttacker recipe)
           | None ->
	       try
	         let (n,p) =
	           findi (function
		      (Input(tc,_,_,_),_,_,_,_) -> equal_terms_modulo_eval tc tin
		    | _ -> false
		    ) cur_state'.subprocess
	      in
	      Some (LocProcess(n,p))
	    with Not_found ->
	      None)
	in
	let rout =
	   (match is_in_public cur_state'.public tout with
           |  Some recipe -> Some (LocAttacker recipe)
           | None ->
	      try
	        let (n,p) =
		  findi (function
		    (Output(tc,_,_,_),_,_,_,_) -> equal_terms_modulo_eval tc tout
		  | _ -> false
		  ) cur_state'.subprocess
	      in
	      Some (LocProcess(n,p))
	    with Not_found ->
	      None)
	in
	begin
	  match rin,rout with
	    Some lin, Some lout ->
	      let new_goal = NonInterfGoal(CommTest(tin,tout,Some(lin,lout))) in
	      (true, { cur_state' with goal = new_goal })
	  | _ -> (false, cur_state')
	end
    | _ -> (false, cur_state')
  with Unify ->
    (false, cur_state')

(* let test_success = Profile.f1 "test_success" test_success *)

let end_if_success next_f cur_state =
  let (success, cur_state') = test_success cur_state in
  if success then cur_state' else next_f cur_state'

(* Normalize the state after a reduction *)

let rec find_possible_outputs f cur_state n seen_list = function
    [] -> f cur_state
  | (Output(tc,t,p,out_occ) as proc, name_params, occs, facts, cache_info)::rest_subprocess when (!Param.active_attacker) ->
      let tclist' =
	match cache_info with
	  InputInfo _ | GetInfo _ -> Parsing_helper.internal_error "Should not have input/get info for an output!"
	| OutputInfo(tclist, oldpub) ->
	    update_term_list oldpub cur_state.public tclist
	| Nothing ->
	    let tclist = decompose_term_rev  ((Terms.new_var "Useless" (Terms.get_term_type tc)), (tc, tc)) in
	    remove_first_in_public cur_state.public tclist
      in
      let seen_list' = (proc, name_params, occs, facts, OutputInfo(tclist', cur_state.public)) :: seen_list in
      if tclist' = [] then
        do_red_nointeract (fun change_pub cur_state2 ->
          if change_pub then
            end_if_success (find_possible_outputs_rec f) cur_state2
          else
            find_possible_outputs f cur_state2 0 [] cur_state2.subprocess
	      ) { cur_state with subprocess = List.rev_append seen_list' rest_subprocess } n
      else
	find_possible_outputs f cur_state (n+1) seen_list' rest_subprocess
  | sub_proc::rest_subprocess -> find_possible_outputs f cur_state (n+1) (sub_proc::seen_list) rest_subprocess

and find_possible_outputs_rec f cur_state3 =
	 find_possible_outputs f cur_state3 0 [] cur_state3.subprocess

(*      When the process number n has been changed *)

let normal_state f change_pub cur_state n =
  do_red_nointeract (fun change_pub2 cur_state2 ->
    if change_pub || change_pub2 then
      end_if_success (find_possible_outputs_rec f) cur_state2
    else f cur_state2
	            ) cur_state n

(*      When two processes have been changed, numbers n1 and n2 *)

let normal_state2 f change_pub cur_state n1 n2 =
  let n1',n2' = if n1 < n2 then n1,n2 else n2,n1 in
  do_red_nointeract (fun change_pub2 cur_state2 ->
    do_red_nointeract (fun change_pub3 cur_state3 ->
      if change_pub || change_pub2 || change_pub3 then
        end_if_success (find_possible_outputs_rec f) cur_state3
      else f cur_state3
	              ) cur_state2 n1'
	            ) cur_state n2'

(*      When all processes have been changed *)

let normal_state_all f change_pub cur_state =
  let rec do_red_all change_pub2 cur_state2 n =
    if n < 0 then
      if change_pub2 then
	end_if_success (find_possible_outputs_rec f) cur_state2
      else
	f cur_state2
    else
      do_red_nointeract (fun change_pub3 cur_state3 ->
	do_red_all (change_pub2 || change_pub3) cur_state3 (n-1)
			) cur_state2 n
  in
  do_red_all change_pub cur_state (List.length cur_state.subprocess - 1)

(* Initial attacker knowledge *)

let rec public_build l =
  match l with
  | [] -> []
  | h::t ->
      if not h.f_private then
	(FunApp(h,[]))::(public_build t)
      else
	public_build t

(* Initialize the rule lists *)

let rec init_rule state tree =
  match tree.desc with
    FHAny | FEmpty ->
      begin
	match tree.thefact with
	  Out(_,_) -> state
	| Pred(p, [t]) when p.p_prop land Param.pred_ATTACKER != 0 ->
	    begin
	      let t' = rev_name_subst t in
	      match t' with
		FunApp({ f_cat = Name _; f_private = false },[]) ->
		  { state with public = (t',(t',t')) :: state.public }
	      |	_ ->
                  (* Public contains terms, not patterns
	             -> translate the pattern into a term.
	             If the translation fails because a name is not in the table, we have to stop. *)
		  if (not (is_in_public  state.public (t',t') = None)) then
		    state
		  else
                    (* I introduce a variable for the recipe here,
           	       and use it when displaying hyp_not_matched.
		       Note: it is important that the term t' is never a tuple.
		       Otherwise, it would be decomposed later, and the link
		       between the recipe in public and the one in hyp_not_matched
		       would be lost. *)
                    let recipe = Var (new_var "~M" (Terms.get_term_type t')) in
                    { state with
                      public = (recipe,(t',t')) :: state.public;
	              hyp_not_matched = (Some recipe, Pred(p,[t']))::state.hyp_not_matched }
            end
	| Pred(p, [t1;t2]) when p.p_prop land Param.pred_ATTACKER != 0 ->
	    begin
	      let t1' = rev_name_subst t1 in
	      let t2' = rev_name_subst t2 in
	      match t1', t2' with
		(FunApp({ f_cat = Name _; f_private = false },[]),
		 FunApp({ f_cat = Name _; f_private = false },[])) when
		equal_terms_modulo t1' t2' ->
		  { state with public = (t1',(t1', t2')) :: state.public }
	      |	_ ->
                  (* Public contains terms, not patterns
	             -> translate the pattern into a term.
	             If the translation fails because a name is not in the table, we have to stop. *)
		  if (not (is_in_public state.public (t1',t2') = None)) then
		    state
		  else
                    (* I introduce a variable for the recipe here,
           	       and use it when displaying hyp_not_matched.
		       Note: it is important that the term t' is never a tuple.
		       Otherwise, it would be decomposed later, and the link
		       between the recipe in public and the one in hyp_not_matched
		       would be lost. *)
                    let recipe = Var (new_var "~M" (Terms.get_term_type t1')) in
                    { state with
                      public = (recipe,(t1',t2')) :: state.public;
	              hyp_not_matched = (Some recipe, Pred(p,[t1';t2']))::state.hyp_not_matched }
            end
        | _ ->
	    let fact = rev_name_subst_fact tree.thefact in
	    if List.exists (fun (_, fact') -> Terms.equal_facts fact fact') state.hyp_not_matched then
	      (* Do not add [fact] in [state.hyp_not_matched] if it is already present *)
	      state
	    else
	      { state with
                hyp_not_matched = (None, fact)::state.hyp_not_matched }
      end
  | FRemovedWithProof _ -> state
  | FRule (n, tags, constra, sons) ->
      let rec init_sons_rule state1 = function
	| [] ->
	    begin
	      match tags with
	        ProcessRule (hsl,nl) ->
                  {state1 with io_rule = (n, List.map (fun t -> rev_name_subst_fact t.thefact) sons,
					  hsl, rev_name_subst_list nl,
					  rev_name_subst_fact tree.thefact)::state1.io_rule}
	      | Apply (f,_) when f.f_cat != Tuple ->
		  begin
		    let (p,c) =
		      match tree.thefact with
			Pred(p,l) -> (p,rev_name_subst_bi l)
		      | _ -> Parsing_helper.internal_error "unexpected Apply clause"
		    in
		    let h = List.map (function
			{ thefact = Pred(_,l) } -> (Terms.new_var "~X" (get_term_type_bi l), rev_name_subst_bi l)
		      |	_ -> Parsing_helper.internal_error "unexpected Apply clause") sons
                    in
                    let h' = decompose_list_rev h in
		      (* concl_copy is the recipe used to compute the conclusion from the hypotheses *)
                    let recipe_concl = FunApp(f, (List.map (fun (x, y) -> Var x) h)) in
	            {state1 with prepared_attacker_rule = (p, h',(recipe_concl, c))::state1.prepared_attacker_rule}
		  end
              | Rn _ ->
                  begin
	            match tree.thefact with
		      Pred(p, l) ->
			let t1',t2' = rev_name_subst_bi l in
			if not (equal_terms_modulo t1' t2') then
			  Parsing_helper.internal_error "Rule Rn should conclude p(name,name) with the same name";
                        { state1 with prepared_attacker_rule = (p, [], (t1',(t1',t2')))::state1.prepared_attacker_rule }
                    | _ -> Parsing_helper.internal_error "Rule Rn should conclude p(name)"
	          end
	      | _ -> state1
	    end
	| h::t ->
	    let state1' = init_rule state1 h in
	    init_sons_rule state1' t
      in
      init_sons_rule state sons
  | FEquation son -> init_rule state son


(* Handle reductions i/o and in *)

(* Perform an input on a public channel (Res In) *)

let do_res_in cur_state seen_list rest_subprocess n current_cache_list name_params' new_occs facts tc pat p tc' mess_term public_status next_f    =
  (* The real list of processes is (List.rev_append seen_list (InputProcess :: rest_subprocess)) *)
  let (recipe, mess_list, oldpub) =
    match public_status with
      Some (recipe, m,o) -> (recipe, m,o)
    | None ->
        let new_recipe = Terms.new_var "~M" (Terms.get_term_type (fst mess_term)) in
        (Var new_recipe, decompose_term_rev (new_recipe, mess_term), [])
  in
  (* Remove the elements of mess_list' that are already in cur_state.public *)
  let mess_list' = update_term_list oldpub cur_state.public mess_list in
  let recipe' = Terms.copy_term4 recipe in
  (* When mess_list' is not empty, its first element is not in cur_state.public
     Remember that point to avoid testing again that part of public *)
  current_cache_list := (mess_term, Some (recipe', mess_list', cur_state.public)) :: (!current_cache_list);
  if mess_list' != [] then raise Unify; (* The message is not public *)
  try
    made_forward_step := true;
    auto_cleanup_red (fun () ->
      let _ = bi_action (bi_match_pattern pat mess_term) in
      let name_params'' = update_name_params Always name_params' pat in
      let p' = auto_cleanup (fun () -> copy_process p) in
      let fact' = build_mess_fact cur_state.current_phase tc'  mess_term in
      normal_state next_f false
	  { cur_state with
            subprocess = List.rev_append seen_list ((p', name_params'', new_occs, fact' :: facts, Nothing) :: rest_subprocess);
            comment = RInput(n, make_bi_choice tc', pat, recipe', make_bi_choice mess_term);
            previous_state = Some cur_state } n
	)
  with No_result ->
    (* Inputting the message mess_term on this input will always fail,
       even in the following of the trace *)
    current_cache_list := List.tl (!current_cache_list);
    raise Unify
  | FailOneSideOnly ->
    (* SUCCESS the pattern matching fails on one side only *)
      { cur_state with
        goal = NonInterfGoal(InputProcessTest([],[],make_bi_choice mess_term, (Some(n, List.nth cur_state.subprocess n, LocAttacker recipe')))) }

(* Perform a (Red I/O) reduction between an input and an asynchronous output *)

let do_async_res_io cur_state seen_list rest_subprocess n current_cache_list name_params' new_occs facts tc pat p tc' mess_term public_channel next_f  =
  (* The real list of processes is (List.rev_append seen_list (InputProcess :: rest_subprocess))
     It differs from cur_state.subprocess only by the cache of input processes, so when
     looking for an output process, we can use cur_state.subprocess instead. *)
  current_cache_list := (mess_term, None) :: (!current_cache_list);
  (* Find the corresponding asynchronous output *)
  let rec find_asynchronous_output noutput = function
      [] -> raise Unify (* not found *)
    | ((Output(tc2, t2, Nil,out_occ), name_params2,occs2, facts2, cache_info2)::_) when
      (equal_bi_terms_modulo (get_choice tc2) tc') && (equal_bi_terms_modulo (get_choice t2) mess_term) ->
	noutput
    | _::rest_subprocess2 -> find_asynchronous_output (noutput+1) rest_subprocess2
  in
  let noutput = find_asynchronous_output 0 cur_state.subprocess in
  begin
    try
      made_forward_step := true;
            try
	      auto_cleanup_red (fun () ->
	        let _ = bi_action (bi_match_pattern pat mess_term) in
                let name_params'' = update_name_params Always name_params' pat in
                let p' = auto_cleanup (fun () -> copy_process p) in
                let fact' = build_mess_fact cur_state.current_phase tc' mess_term in
		let tc'' = make_bi_choice tc' in
                let cur_state' =
                  if public_channel then
	      (* The adversary is passive and the channel is public;
		 the adversary eavesdrops the message sent by RIO *)
                    let (new_recipe, cur_state') = add_public cur_state mess_term in
                    { cur_state' with
                      subprocess = remove_at noutput
	                (List.rev_append seen_list ((p', name_params'', new_occs, fact' :: facts, Nothing) :: rest_subprocess));
	              comment = RIO(n, tc'', pat, noutput, tc'', Some new_recipe, make_bi_choice mess_term, false);
	              previous_state = Some cur_state
                    }
                  else
                    { cur_state with
                      subprocess = remove_at noutput
	                (List.rev_append seen_list ((p', name_params'', new_occs, fact' :: facts, Nothing) :: rest_subprocess));
	              comment = RIO(n, tc'', pat, noutput, tc'', None, make_bi_choice mess_term, false);
	              previous_state = Some cur_state
                    }
            in
                let ninput = if n > noutput then n-1 else n in
                normal_state next_f (cur_state'.public != cur_state.public) cur_state' ninput
              )
            with Unify ->
	(* The pattern does not match *)
	      let noutput' = if n>noutput then noutput else noutput-1 in
	      let tc'' = make_bi_choice tc' in
              let cur_state2 =
	        if public_channel then
	       (* The adversary is passive and the channel is public;
		  the adversary eavesdrops the message sent by RIO2 *)
                  let (new_recipe, cur_state') = add_public cur_state mess_term in
	          { cur_state'  with
                    subprocess = remove_at noutput' (List.rev_append seen_list rest_subprocess);
	            comment = RIO2(n, tc'', pat, noutput, tc'', Some new_recipe, make_bi_choice mess_term, false);
                    previous_state = Some cur_state }
             else
	       { cur_state  with
                 subprocess = remove_at noutput' (List.rev_append seen_list rest_subprocess);
	         comment = RIO2(n, tc'', pat, noutput, tc'', None, make_bi_choice mess_term, false);
                 previous_state = Some cur_state }
	   in
           next_f cur_state2
      | FailOneSideOnly ->
	  (* SUCCESS the pattern matching fails on one side only *)
	  { cur_state with
            goal = NonInterfGoal(InputProcessTest([],[],make_bi_choice mess_term, Some(n, List.nth cur_state.subprocess n, LocProcess(noutput, List.nth cur_state.subprocess noutput)))) }
    with No_result ->
      current_cache_list := List.tl (!current_cache_list);
      raise Unify
  end


(* Perform a (Res I/O) reduction with a synchronous output *)

let do_sync_res_io cur_state seen_list rest_subprocess n name_params' new_occs facts tc pat p tc' public_channel next_f   =
  (* The real list of processes is (List.rev_append seen_list (InputProcess :: rest_subprocess))
     It differs from cur_state.subprocess only by the cache of input processes, so when
     looking for an output process, we can use cur_state.subprocess instead. *)
  let rec find_synchronous_output noutput = function
      [] -> raise No_result (* Not found *)
    | ((Output(tc2,t2,p2,out_occ),name_params2,occs2, facts2, cache_info2)::rest_subprocess2) when (p2 != Nil) || public_channel ->
      begin
        try
	  let tc2' = get_choice tc2 in
          let t2' = get_choice t2 in
          if equal_bi_terms_modulo tc2' tc' then
	    begin
              made_forward_step := true;
		(* The i/o reduction is possible, compute the reduced state *)
		let fact = build_mess_fact cur_state.current_phase tc' t2' in
		try
		  auto_cleanup_red (fun () ->
                  let _ = bi_action (bi_match_pattern pat t2') in
                  let name_params'' = update_name_params Always name_params' pat in
                  let p' = auto_cleanup (fun () -> copy_process p) in
                  let cur_state' =
		    if public_channel then
	              (* The adversary is passive and the channel is public;
			 the adversary eavesdrops the message sent by RIO *)
		      let (new_recipe, cur_state2) = add_public cur_state t2' in
		      { cur_state2 with
			  subprocess = replace_at noutput (p2, name_params2, (OutputTag out_occ)::occs2, facts2, Nothing)
			    (List.rev_append seen_list ((p', name_params'', new_occs, fact :: facts, Nothing) :: rest_subprocess));
			  comment = RIO(n, make_bi_choice tc', pat, noutput, tc2, Some new_recipe, t2, false);
			  previous_state = Some cur_state }
		    else
		      { cur_state with
			  subprocess = replace_at noutput (p2, name_params2, (OutputTag out_occ)::occs2, facts2, Nothing)
			    (List.rev_append seen_list ((p', name_params'', new_occs, fact :: facts, Nothing) :: rest_subprocess));
			  comment = RIO(n, make_bi_choice tc', pat, noutput, tc2, None, t2, false);
			  previous_state = Some cur_state }
		  in
		  normal_state2 next_f (cur_state'.public != cur_state.public) cur_state' noutput n
		      )

	        with Unify -> (* The pattern does not match *)
                  let noutput' = if n > noutput then noutput else noutput-1 in
		  let cur_state' =
		    if public_channel then
	              (* The adversary is passive and the channel is public;
			 the adversary eavesdrops the message sent by RIO2 *)
		      let (new_recipe, cur_state2) = add_public cur_state t2' in
		      { cur_state2 with
                        subprocess = replace_at noutput' (p2, name_params2, occs2, facts2, Nothing)
			  (List.rev_append seen_list rest_subprocess);
		        comment = RIO2(n, make_bi_choice tc', pat, noutput, tc2, Some new_recipe, t2, false);
                        previous_state = Some cur_state }
		    else
		      { cur_state with
                        subprocess = replace_at noutput' (p2, name_params2, occs2, facts2, Nothing)
			  (List.rev_append seen_list rest_subprocess);
		        comment = RIO2(n, make_bi_choice tc', pat, noutput, tc2, None, t2, false);
                        previous_state = Some cur_state }
		  in
		  normal_state next_f (cur_state'.public != cur_state.public) cur_state' noutput'
	        | FailOneSideOnly ->
	            (* SUCCESS the pattern matching fails on one side only *)
		    { cur_state with
                      goal = NonInterfGoal(InputProcessTest([],[],t2,Some(n, List.nth cur_state.subprocess n, LocProcess(noutput, List.nth cur_state.subprocess noutput)))) }
	      end
	    else raise Unify
          with Unify | No_result ->
	    find_synchronous_output (noutput+1) rest_subprocess2
	end
    | _::rest_subprocess2 -> find_synchronous_output (noutput+1) rest_subprocess2
  in
  find_synchronous_output 0 cur_state.subprocess
(* Perform a get (Res Get) *)

let rec find_term stop_l t l =
  if l == stop_l then false else
  match l with
    [] -> false
  | (a::r) ->
      if equal_bi_terms_modulo t a then true else find_term stop_l t r

let do_res_get cur_state seen_list rest_subprocess n current_cache_list name_params' new_occs facts pat t p mess_term old_tables next_f    =
  (* The real list of processes is (List.rev_append seen_list (InputProcess :: rest_subprocess)) *)
  current_cache_list := mess_term :: (!current_cache_list);
  debug_print "Get";
  if not (find_term old_tables mess_term cur_state.tables) then raise Unify; (* The entry is not found *)
  debug_print "Ok, the entry is present";
  try
    made_forward_step := true;
    auto_cleanup_red (fun () ->
      (* we check that the pattern pat matches and t evaluates to true *)
      let _ = bi_action (bi_match_pattern_and_test pat mess_term t) in
      let name_params'' = update_name_params Always name_params' pat in
      let p' = auto_cleanup (fun () -> copy_process p) in
      let fact' = build_table_fact cur_state.current_phase mess_term in
      normal_state next_f false
		{ cur_state with
                  subprocess = List.rev_append seen_list ((p', name_params'', new_occs, fact' :: facts, Nothing) :: rest_subprocess);
                  comment = RGet(n, pat, t, make_bi_choice mess_term);
                  previous_state = Some cur_state } n
	)
  with No_result ->
    (* Using the entry mess_term on this input will always fail,
       even in the following of the trace *)
    current_cache_list := List.tl (!current_cache_list);
    raise Unify
  | FailOneSideOnly ->
    (* SUCCESS the pattern matching fails on one side only *)
      { cur_state with
        goal = NonInterfGoal(ProcessTest([],[],Some(n, List.nth cur_state.subprocess n))) }

(* Dispatch between (Res In), asynchronous (Res I/O), and synchronous (Res I/O), and (Res Get).
   May also execute (Insert) in case an insert has been delayed because it prevented executing the
   else branch of Get. *)

exception Backtrack_get
(* This exception is used only when I should take the
   else of Get and I cannot because an element that
   makes Get succeed already occurs. *)

let rec find_in_out next_f cur_state n seen_list = function
    [] -> raise No_result
  | ((Input(tc,pat,p,occ) as proc ,name_params,occs, facts, cache_info)::rest_subprocess) ->
      debug_print ("Trying Input on process " ^ (string_of_int n));
      begin
	match cache_info with
	  OutputInfo _ | GetInfo _ -> Parsing_helper.internal_error "Should not have output/get info for an input!"
	| InputInfo(tc_list, oldpub, tc', name_params', new_occs, l) ->
	    let tc_list' = update_term_list oldpub cur_state.public tc_list in
	    if (!Param.active_attacker) && (tc_list' = []) then
	      begin
	        (* The channel is public and the attacker is active, try (Res In) *)
		let current_cache_list = ref [] in
		let rec do_l = function
		    [] ->
		      let seen_list' = (proc ,name_params,occs, facts,
					InputInfo(tc_list', cur_state.public, tc', name_params', new_occs, !current_cache_list)) :: seen_list in
		      find_in_out next_f cur_state (n+1) seen_list' rest_subprocess
		  | (mess_term, public_status)::l ->
		      try
	                 do_res_in cur_state seen_list rest_subprocess n current_cache_list name_params' new_occs facts tc pat p tc' mess_term public_status next_f
		      with Unify ->
		      do_l l
		in
		do_l l
	      end
	    else
	      begin
	        (* The channel is private or the attacker is passive, try (Res I/O) *)
		let current_cache_list = ref [] in
		let public_channel = (not (!Param.active_attacker)) && (tc_list' = []) in
		let rec do_l = function
		    [] ->
		      let seen_list' = (proc ,name_params,occs, facts,
					InputInfo(tc_list', cur_state.public, tc', name_params', new_occs, !current_cache_list)) :: seen_list in
		      begin
			try
			  do_sync_res_io cur_state seen_list rest_subprocess n name_params' new_occs facts tc pat p tc' public_channel next_f
			with Unify | No_result ->
			  find_in_out next_f cur_state (n+1) seen_list' rest_subprocess
		      end
		  | (mess_term,_)::l ->
		      try
			do_async_res_io cur_state seen_list rest_subprocess n current_cache_list name_params' new_occs facts tc pat p tc' mess_term public_channel next_f
		      with Unify ->
			do_l l
		in
		do_l l
	      end
	| Nothing ->
	    let seen_list' = ref ((proc, name_params, occs, facts, cache_info) :: seen_list) in
	    try
              auto_cleanup_red (fun () ->
		let (tc', name_params') = term_evaluation_name_params (OInChannel(occ)) tc name_params in
		let m =
		  if cur_state.current_phase < get_min_choice_phase() then
		    let v = Reduction_helper.new_var_pat pat in
		    (v,v)
		  else
		    (Reduction_helper.new_var_pat pat, Reduction_helper.new_var_pat pat)
		in
                let new_occs = (InputTag occ) :: occs in
		let fact = build_mess_fact cur_state.current_phase tc' m in
                let new_recipe = Terms.new_var "Useless" (Terms.get_term_type (fst tc')) in
		let tc_list = decompose_term_rev (new_recipe, tc') in
		let tc_list' = remove_first_in_public cur_state.public tc_list in
		if (!Param.active_attacker) && (tc_list' = []) then
		  begin
		    (* Input on a public channel, and the attacker is active: apply (Res In)  *)
		    let current_cache_list = ref [] in
		    try
		      find_io_rule (function
			  [mess_term1;mess_term2] ->
			    do_res_in cur_state seen_list rest_subprocess n current_cache_list name_params' new_occs facts tc pat p tc' (mess_term1,mess_term2) None next_f
			| _ -> Parsing_helper.internal_error "input case; reduction_bipro.ml"
			      ) new_occs (fact :: facts) name_params' [fst m; snd m] cur_state.io_rule
		    with Unify ->
		      seen_list' := (proc, name_params, occs, facts,
				     InputInfo([], [], tc', name_params', new_occs, !current_cache_list)) :: seen_list;
		      raise No_result
		  end
		else
		  begin
		    (* Input on a private channel or the attacker is passive: apply (Res I/O)
		       First try an asynchronous output, with a corresponding clause in the tree *)
		    let current_cache_list = ref [] in
		    let public_channel = (not (!Param.active_attacker)) && (tc_list' = []) in
		    try
		      find_io_rule (function
			  [mess_term1;mess_term2] ->
			    do_async_res_io cur_state seen_list rest_subprocess n current_cache_list name_params' new_occs facts tc pat p tc' (mess_term1,mess_term2) public_channel next_f
			| _ -> Parsing_helper.internal_error "input case; reduction_bipro.ml"
			      ) new_occs (fact :: facts) name_params' [fst m; snd m] cur_state.io_rule
                    with Unify ->
		      seen_list' := (proc, name_params,occs, facts,
				     InputInfo(tc_list', cur_state.public, tc', name_params', new_occs, !current_cache_list)) :: seen_list;
		      (* Try a synchronous output *)
		      do_sync_res_io cur_state seen_list rest_subprocess n name_params' new_occs facts tc pat p tc' public_channel next_f
		    end
		    )
	    with Unify | No_result ->
	      find_in_out next_f cur_state (n+1) (!seen_list') rest_subprocess
	  | FailOneSideOnly ->
	      (* SUCCESS the evaluation of the channel name fails on one side only *)
	      { cur_state with
                goal = NonInterfGoal(ProcessTest([],[],Some(n, List.nth cur_state.subprocess n))) }
      end
  | ((Get(pat,t,p,p_else,occ) as proc ,name_params,occs, facts, cache_info)::rest_subprocess) ->
      debug_print ("Trying Get on process " ^ (string_of_int n));
      begin
	match cache_info with
	  OutputInfo _ | InputInfo _ -> Parsing_helper.internal_error "Should not have input/output info for a get!"
	| GetInfo(old_tables, l) ->
	    let new_occs = (GetTag occ) :: occs in
	    let current_cache_list = ref [] in
	    let rec do_l = function
		[] ->
		  let seen_list' = (proc ,name_params,occs, facts,
				    GetInfo(cur_state.tables, !current_cache_list)) :: seen_list in
		  find_in_out next_f cur_state (n+1) seen_list' rest_subprocess
	      | mess_term::l ->
		  try
		    do_res_get cur_state seen_list rest_subprocess n current_cache_list name_params new_occs facts pat t p mess_term old_tables next_f
		  with Unify ->
		    do_l l
	    in
	    do_l l
	| Nothing ->
	    let seen_list' = ref ((proc, name_params, occs, facts, cache_info) :: seen_list) in
	    try
              auto_cleanup_red (fun () ->
		let m =
		  if cur_state.current_phase < get_min_choice_phase() then
		    let v = Reduction_helper.new_var_pat pat in
		    (v,v)
		  else
		    (Reduction_helper.new_var_pat pat, Reduction_helper.new_var_pat pat)
		in
		let new_occs = (GetTag occ) :: occs in
		let fact = build_table_fact cur_state.current_phase m in
		begin
		  let current_cache_list = ref [] in
		  try
		    find_io_rule (function
			[mess_term1;mess_term2] ->
			  do_res_get cur_state seen_list rest_subprocess n current_cache_list name_params new_occs facts pat t p (mess_term1,mess_term2) [] next_f
		      | _ -> Parsing_helper.internal_error "get case; reduction_bipro.ml"
                            ) new_occs (fact :: facts) name_params [fst m; snd m] cur_state.io_rule
		  with Unify ->
		    if p_else != Nil then
		      (* See if we should take the else branch if present *)
		      begin
			try
			  let new_occs = (GetTagElse occ) :: occs in
			  find_io_rule (function
			      [] ->
				(* We should take the else branch, since a clause uses that branch *)
				debug_print "Get: else branch should be taken";
				if List.exists (fun mess_term ->
				  try
				    auto_cleanup (fun () ->
                                      (* we check that the pattern pat matches and t evaluates to true *)
				      let _ = bi_action (bi_match_pattern_and_test pat mess_term t) in
				      true)
				  with Unify -> false
				      (* When FailOneSideOnly is raised, it will be catched above and
					 the trace reconstruction succeeds. *)) cur_state.tables
				then
				  begin
				    debug_print "Get: an element of the table matches, cannot take the else branch, backtracking";
				    (* The Get process is blocked forever: the else branch should be taken,
				       but the table contains an element that prevents it. Since elements
				       are only added to tables, this situation will not change.
				       So I backtrack. *)
				    has_backtrack_get := true;
				    raise Backtrack_get
				  end
				else
				  begin
				    debug_print "Get: taking the else branch";
				    normal_state next_f false
				      { cur_state with
			                subprocess = List.rev_append seen_list ((p_else, name_params, new_occs, facts, Nothing) :: rest_subprocess);
                                        comment = RGet2(n, pat, t);
                                        previous_state = Some cur_state } n
				  end
			    | _ -> Parsing_helper.internal_error "get else case; reduction_bipro.ml"
				  ) new_occs facts name_params [] cur_state.io_rule
			with Unify ->
			  seen_list' := (proc, name_params, occs, facts,
					 GetInfo(cur_state.tables, !current_cache_list)) :: seen_list;
			  raise No_result
		      end
		    else
		      begin
			seen_list' := (proc, name_params, occs, facts,
				       GetInfo(cur_state.tables, !current_cache_list)) :: seen_list;
			raise No_result
		      end
		end
		  )
	    with Unify | No_result ->
	      find_in_out next_f cur_state (n+1) (!seen_list') rest_subprocess
	  | FailOneSideOnly ->
	      (* SUCCESS an element of the table matches on one side and not on the other *)
	      { cur_state with
                goal = NonInterfGoal(ProcessTest([],[],Some(n, List.nth cur_state.subprocess n))) }
	  | Backtrack_get -> raise No_result
      end
  | ((Insert(t,p,occ), name_params, occs, facts, cache_info) as sub_proc)::rest_subprocess ->
      debug_print "Doing Insert";
      begin
	let new_occs = (InsertTag occ) :: occs in
	let new_element_inserted = ref false in
	try
	  auto_cleanup_red (fun () ->
	    let t' = bi_action (term_evaluation_fail t) in
	    let already_in = List.exists (equal_bi_terms_modulo t') cur_state.tables in
	    new_element_inserted := not already_in;
	    normal_state next_f false
	      { cur_state with
	        subprocess = List.rev_append seen_list ((p, name_params, new_occs, facts, Nothing) :: rest_subprocess);
	        tables = if already_in then cur_state.tables else t'::cur_state.tables;
                comment = RInsert1(n, make_bi_choice t', false);
                previous_state = Some cur_state } n
	      )
        with Unify | FailOneSideOnly ->
	  Parsing_helper.internal_error "Insert: Unify/FailOneSideOnly should have been detected on the first try of that insert"
	| No_result ->
	    (* The attack reconstruction failed after doing the insert.
	       Try not doing it, in case that allows executing the else branch of a Get. *)
	    if (!has_backtrack_get) && (!new_element_inserted) then
	      find_in_out next_f cur_state (n+1) (sub_proc :: seen_list) rest_subprocess
	    else
	      raise No_result
      end
  | sub_proc::rest_subprocess ->
      find_in_out next_f cur_state (n+1) (sub_proc :: seen_list) rest_subprocess

(* Handle phases *)

(* [extract_phase n processes] modifies the processes for a [phase n] transition:
   removes processes with no phase prefix or a phase prefix less than [n];
   removes the phase prefix [phase n], leaving the rest of the process;
   leaves processes with phase prefix greater than [n] unchanged. *)

let rec extract_phase n = function
    [] -> []
  | (Phase(n',p,occ),name_params,occs, facts, cache_info)::r ->
      let r' = extract_phase n r in
      if n = n' then (p,name_params,occs, facts, Nothing)::r' else
      if n<n' then (Phase(n',p,occ),name_params,occs, facts, Nothing)::r' else r'
  | _::r -> extract_phase n r

(* [find_phase current_phase None processes] returns either
   [None] when no process in [processes] starts with a phase, or
   [Some n] when a process in [processes] starts with phase [n] and this is the lowest such phase. 
   It is an error if a process in [processes] starts with a phase less or equal to [current_phase]. *) 

let rec find_phase current_phase found_phase = function
    [] -> found_phase
  | (Phase(n,p,_),name_params,occs, facts, cache_info)::rest_subprocess ->
      if n <= current_phase then
	Parsing_helper.user_error "Phases should be in increasing order.";
      let found_phase' = 
	match found_phase with
	  None -> Some n
	| Some n_found -> if n_found <= n then found_phase else Some n
      in
      find_phase current_phase found_phase' rest_subprocess
  | _::rest_subprocess -> 
      find_phase current_phase found_phase rest_subprocess

let do_phase next_f cur_state =
  match find_phase cur_state.current_phase None cur_state.subprocess with
    None ->
      if !made_forward_step then
	begin
          incr failed_traces;
          made_forward_step := false
	end;
      (* Useful for debugging *)
      if !debug_backtracking then
	begin
	  ignore (Display.Text.display_reduc_state Display.bi_term_to_term true cur_state);
	  print_string "Blocked. Backtracking...\n"
	end
      else
	debug_print "Backtracking";
      raise No_result
  | Some n -> 
      debug_print "Doing Phase";
      made_forward_step := true;
      (* Reclose public, since new function symbols may become applicable *)
      let cur_state' = close_public_phase_change cur_state n in
      (* Do transition to phase n *)
      let cur_state'' =
	{ cur_state' with
	  subprocess = extract_phase n cur_state'.subprocess;
	  previous_state = Some cur_state;
	  current_phase = n;
	  comment = RPhase(n) }
      in
      normal_state_all next_f false cur_state''

(* Put all reductions together *)

let reduction_step next_f state =
  try
    find_in_out next_f state 0 [] state.subprocess
  with No_result ->
    do_phase next_f state

let rec reduction_backtrack state =
  reduction_step reduction_backtrack state

let rec reduction_nobacktrack state =
  try
    reduction_step (fun state -> raise (Reduced state)) state
  with Reduced one_red_state ->
    display_trace one_red_state;
    Param.display_init_state := false;
    reduction_nobacktrack { one_red_state with previous_state = None }

let reduction state =
  if !Param.trace_backtracking then
    reduction_backtrack state
  else
    reduction_nobacktrack state

(* Build the goal *)

let analyze_tree tree =
  match tree.desc with
    FRule(_, lbl, _, hyp) ->
      begin
	match lbl, hyp with
	  ProcessRule(hyp_tags, name_params), hyp ->
	    ProcessTest([], [], None)
	| Rfail(p), hyp ->
	    NIFailTest((match hyp with
	      [{ thefact = Pred(_, l) }] -> rev_name_subst_bi l
	    | _ -> Parsing_helper.internal_error "Unexpected derivation for choice"), None)
	| TestComm(pi,po), [{thefact = Pred(_,lin)}; {thefact = Pred(_,lout)}] ->
	    CommTest(rev_name_subst_bi lin, rev_name_subst_bi lout, None)
	| TestEq(p), [{thefact = Pred(_,l1)};{thefact = Pred(_,l2)}] ->
	    NIEqTest((rev_name_subst_bi l1, None), (rev_name_subst_bi l2, None))
	| _ -> Parsing_helper.internal_error "Unexpected clause concluding the derivation for choice"
      end
  | _ -> Parsing_helper.internal_error "Unexpected derivation for choice"


(* Main trace reconstruction function *)

let do_reduction tree =
(*  Profile.start();  *)
  debug_print "Initializing";
  has_backtrack_get := false;
  made_forward_step := true;
  failed_traces := 0;
  let freenames = (!Param.current_state).pi_freenames in
  let public_init = public_build freenames in
  public_free := public_init;
  Param.display_init_state := true;
  init_name_mapping freenames;
  close_tree tree;
  let (main_process, query) = Param.get_process_query (!Param.current_state) in
  let init_state =
    { goal = NonInterfGoal (analyze_tree tree);
      subprocess = [(main_process, [],[],[],Nothing)];
      public = List.map (fun t -> (t,(t, t))) public_init;
      pub_vars = public_init;
      tables = [];
      io_rule = [];
      prepared_attacker_rule = [];
      previous_state = None;
      hyp_not_matched = [];
      assumed_false = [];
      current_phase = 0;
      comment = RInit;
      events = [];
      barriers = []
    }
  in
  let res =
    begin
      try
	let state = init_rule init_state tree in
        (* Close initially the set public *)
	let state = close_public_initial state in
	if !debug_find_io_rule then
	  begin
	    auto_cleanup (fun () ->
	      print_string "Available rules:";
	      Display.Text.newline();
	      List.iter display_rule state.io_rule)
	  end;
	debug_print "Initialization done";
	if !Param.html_output then
	  begin
	    let qs = string_of_int (!Param.derivation_number) in
	    Display.LangHtml.openfile ((!Param.html_dir) ^ "/trace" ^ qs ^ ".html") ("ProVerif: trace for query " ^ qs);
	    Display.Html.print_string "<H1>Trace</H1>\n"
	  end;
	let final_state = normal_state reduction true state 0 in
	display_trace final_state;
	let dot_err = Reduction_helper.create_pdf_trace Display.bi_term_to_term noninterftest_to_string "" final_state in
	if !Param.html_output then
	  begin
	    Display.Html.display_goal Display.bi_term_to_term noninterftest_to_string final_state true;
	    Display.LangHtml.close();
	    let qs = string_of_int (!Param.derivation_number) in
	    Display.Html.print_string ("<A HREF=\"trace" ^ qs ^ ".html\">Trace</A><br>\n");
	    if (not !Param.command_line_graph_set) && (!Param.trace_backtracking && (dot_err = 0))  then
            Display.Html.print_string ("<A HREF=\"trace" ^ qs ^ ".pdf\">Trace graph</A><br>\n")
	  end
	else
	  Display.Text.display_goal Display.bi_term_to_term noninterftest_to_string final_state true;
	final_state.hyp_not_matched = []
      with No_result ->
	if not (!Param.trace_backtracking) then
	  Display.Def.print_line "Blocked!";
	if !Param.html_output then
	  begin
	    Display.LangHtml.close();
	    if not (!Param.trace_backtracking) then
	      begin
		let qs = string_of_int (!Param.derivation_number) in
		Display.Html.print_string ("<A HREF=\"trace" ^ qs ^ ".html\">Unfinished trace</A><br>\n")
	      end;
	    Display.Html.print_line "Could not find a trace corresponding to this derivation."
	  end;
	Display.Text.print_line "Could not find a trace corresponding to this derivation.";
	false
    end
  in
(*  print_endline ("Failed " ^ (string_of_int (!failed_traces)) ^ " traces."); *)
(*  Profile.stop(); *)
  res


let do_reduction tree =
  debug_print "Starting reduction";
  let res = History.unify_derivation do_reduction None tree in
  Terms.cleanup ();
  res
