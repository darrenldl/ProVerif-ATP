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
open Terms

let debug_print s = ()
  (* print_endline s *)

let rec term_evaluation = function
    Var v ->
    begin
      match v.link with
        TLink t -> term_evaluation t
      | _ -> Parsing_helper.internal_error "Error: term should be closed in attack reconstruction";
    end
  | FunApp(f,l) ->
    (* for speed, use the initial definition of destructors, not the one enriched with the equational theory *)
    match f.f_initial_cat with
      Eq _ | Tuple ->
      let l' = List.map term_evaluation l in
      if List.exists Reduction_helper.is_fail l' then
	Terms.get_fail_term (snd f.f_type)
      else
	FunApp(f, l')
    | Name _ | Failure -> FunApp(f,[])
    | Red redl ->
      let l' = List.map term_evaluation l in
      let rec try_red_list = function
	  [] ->
	  Parsing_helper.internal_error "Term evaluation should always succeeds (perhaps returning Fail)"
	| (red1::redl) ->
	  let (left, right, side_c) = auto_cleanup (fun () -> Terms.copy_red red1) in
	  try
	    auto_cleanup (fun () ->
		Reduction_helper.match_modulo_list (fun () ->
		    if List.for_all Reduction_helper.disequation_evaluation side_c then
		      begin
		        (* TO DO (for speed) should I remove_syntactic, or keep it,
			   but take it into account elsewhere (when doing
			   function symbol comparisons, accept functions that
			   differ by their syntactic status) *)
			Reduction_helper.close_term right;
 			TermsEq.remove_syntactic_term right
		      end
		    else
		      raise Unify
		  ) left l')
	  with Unify -> try_red_list redl
      in
      try_red_list redl
    | _ -> Parsing_helper.internal_error "unexpected function symbol in term_evaluation"

(* Evaluates t1 and tests if it is equal to t2. *)
let equal_terms_modulo_eval t1 t2 =
  let t1' = term_evaluation t1 in
  if Reduction_helper.is_fail t1' then false else Reduction_helper.equal_terms_modulo t1' t2

(* Evaluates a term. Raises Unify when the result is fail. *)
let term_evaluation_fail t =
  let r = term_evaluation t in
  if Reduction_helper.is_fail r then
    raise Unify
  else
    r

let rec term_evaluation_letfilter = function
Var { link = TLink t } -> term_evaluation_letfilter t
  | Var v ->  Var v
  | FunApp(f,l) ->
    match f.f_cat with
      Eq _ | Tuple -> FunApp(f, term_evaluation_list_letfilter l)
    | Name _ -> FunApp(f,[])
    |	Failure -> raise Unify
    | Red redl -> term_evaluation_fail (FunApp(f,l))
    | _ -> Parsing_helper.internal_error "unexpected function symbol in term_evaluation_letfilter"

and term_evaluation_list_letfilter l =
  List.map term_evaluation_letfilter l

let term_evaluation_letfilter occ l name_params =
  let may_have_several_types = Reduction_helper.reduction_check_several_patterns occ in
  let l' = term_evaluation_list_letfilter l in
  if may_have_several_types then
    l', ((List.map (fun t -> (MUnknown,t,Always)) l') @ name_params)
  else
    l', name_params


(* Match a pattern
   Raises Unify when the matching fails *)

let rec match_pattern p t =
  if not (Terms.equal_types (Terms.get_pat_type p) (Terms.get_term_type t)) then
    raise Unify;
  match p with
    PatVar b ->
      Terms.link b (TLink t)
  | PatTuple(f,l) ->
      let vl = Terms.var_gen (fst f.f_type) in
      let tl =
	Reduction_helper.match_modulo (fun () ->
	  List.map Reduction_helper.copy_closed_remove_syntactic vl
	    ) (FunApp(f, vl)) t
      in
      List.iter2 match_pattern l tl
  | PatEqual t' ->
      let t'' = term_evaluation_fail t' in
      Reduction_helper.match_modulo (fun () -> ()) t'' t

(* Decompose tuples *)

let rec decompose_term ((recipe, t) as pair) =
  match t with
    FunApp({f_cat = Tuple } as f,l) ->
      let projs = get_all_projection_fun f in
      decompose_list (List.map2 (fun fi ti -> FunApp(fi, [recipe]), ti) projs l)
  | t -> [pair]

and decompose_list = function
    [] -> []
  | (a::l) -> (decompose_term a) @ (decompose_list l)

let rec decompose_term_rev (binder, t) =
  match t with
    FunApp({f_cat = Tuple} as f, l) ->
      let new_list = List.map (fun x -> ((new_var "~M" (Terms.get_term_type x)), x)) l in
      link binder (TLink (FunApp(f, (List.map (fun (x, y) -> Var x) new_list))));
      decompose_list_rev new_list
  | t -> [(binder, t)]

and decompose_list_rev = function
    [] -> []
  | (a::l) -> (decompose_term_rev a) @ (decompose_list_rev l)

(* Test if a term is public *)

let rec is_in_public public = function
  | FunApp({f_cat = Tuple} as f, l) ->
      (match is_in_public_list public l with
        | None -> None
        | Some lst -> Some(FunApp(f, lst)))
  | t ->
      try
        let (ca, _) = List.find (fun (_, t') -> Reduction_helper.equal_terms_modulo t t') public in
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
      let (ca, _) = List.find (fun (_, t) -> Reduction_helper.equal_terms_modulo a t) public in
      link c (TLink ca);
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
          if Reduction_helper.equal_terms_modulo a t0
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
	

let rec add_public_and_close state l (* l contains a list of recipe and the corresponding term *)=
  let queue = ref l in
  let rec remove_from_att_rules public ((recipe, t) as pair) = function
      [] -> []
    | (p, hyp_terms, (recipe_concl, concl_term))::attacker_rules ->
	let attacker_rules' = remove_from_att_rules public pair attacker_rules in
	let phase_p = Reduction_helper.getphase p in
	assert (phase_p >= state.current_phase);
	let hyp_terms' =
	  match hyp_terms with
	    [] -> []
	  | (c0,t0)::l0 ->
	    if Reduction_helper.equal_terms_modulo t0 t then
	      begin
		link c0 (TLink recipe);
		remove_first_in_public public l0
	      end
	    else
	      hyp_terms
	in
	if (hyp_terms' = []) && (phase_p = state.current_phase) then
	  begin
            queue := (decompose_term (Terms.copy_term4 recipe_concl, concl_term)) @ (!queue);
	    attacker_rules'
	  end
	else
          (* Keep the rule, removing hypotheses that are already in *)
	  (p, hyp_terms', (recipe_concl, concl_term)) :: attacker_rules'
  in
  let rec do_close state =
    match !queue with
      [] -> state
    | ((c, t)::l) ->
      queue := l;
      if List.exists (fun (_, t') -> Reduction_helper.equal_terms_modulo t t') state.public then
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
    FunApp({ f_cat = Tuple } as f, l) ->
    let projs = get_all_projection_fun f in
    add_public_list state (List.map2 (fun fi ti -> (FunApp(fi, [recipe]), ti)) projs l)
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
    | ((p, hyp_terms, (recipe_concl, concl_term)) as rule)::attacker_rules ->
	let attacker_rules' = remove_from_att_rules public attacker_rules in
	let phase_p = Reduction_helper.getphase p in
	if phase_p < state.current_phase then attacker_rules' else
	if (hyp_terms = []) && (phase_p = state.current_phase) then
	  begin
            queue := (decompose_term (Terms.copy_term4 recipe_concl, concl_term)) @ (!queue);
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
  let new_recipe = new_var "~M" (get_term_type t) in
  let l = decompose_term_rev (new_recipe, t) in
  let l' = List.map (fun (b,t) -> (Var b, t)) l in
  let state' = add_public_and_close state l' in
  (Terms.copy_term4 (Var new_recipe), state')

let rec extract_phase n = function
    [] -> []
  | (Phase(n',p,occ),name_params,occs, facts, cache_info)::r ->
    let r' = extract_phase n r in
    if n = n' then (p,name_params,occs, facts, Nothing)::r' else
    if n<n' then (Phase(n',p,occ),name_params,occs, facts, Nothing)::r' else r'
  | _::r -> extract_phase n r
