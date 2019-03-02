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
open Parsing_helper

let has_equations = ref false

let hasEquations() =
  !has_equations

let non_syntactic f =
  match f.f_cat with
  | Syntactic f' -> f'
  | _ -> f


(******** Close clauses modulo the equational theory ******
 close_rule_eq is used for clauses entered by the user in Horn-clause
 front-ends,
 close_fact_eq is used for closing the goals *)

let rec close_term_eq restwork = function
    Var x ->
      begin
	match x.link with
          TLink t -> close_term_eq restwork t
	(* TO DO should I always recursively close links modulo equations? *)
        | NoLink -> restwork (Var x)
	| _ -> internal_error "unexpected link in close_term_eq"
      end

  | FunApp(f,l) ->
      close_term_list_eq (fun l' ->
	restwork (FunApp(f,l'));
	match f.f_cat with
	| Eq eqlist ->
	    List.iter (fun (lhd,rhs) ->
	      Terms.auto_cleanup (fun () ->
		let (leq', req',_) = copy_red (lhd,rhs,[]) in
		try
		  List.iter2 unify l' leq';
	          restwork req'
		with Unify -> ()
		    )
	    ) eqlist
	 | _ -> ()
      ) l

and close_term_list_eq restwork = function
  | [] -> restwork []
  | (a::l) ->
      close_term_eq (fun a' ->
	close_term_list_eq (fun l' ->
	  restwork (a'::l')
	) l
      ) a

let close_fact_eq restwork = function
    Pred(p,l) ->
      close_term_list_eq (fun l' -> restwork (Pred(p,l'))) l
  | Out(t,l) ->
      Parsing_helper.internal_error "Out facts should not appear in TermsEq.close_fact_eq"
      (* restwork (Out(t,l))
	 If Out facts were present, we might need to
	 apply equations to the "fact" part of Out facts;
	 the environment part is left unchanged
      close_term_eq (fun t' ->
	  restwork (Out(t',l))) t *)


let rec close_fact_list_eq restwork = function
    [] -> restwork []
  | (a::l) ->
      close_fact_eq (fun a' ->
	close_fact_list_eq (fun l' ->
	  restwork (a'::l')) l) a

let close_rule_eq restwork (hyp,concl,hist,constra) =
  close_fact_list_eq (fun hyp' ->
    close_fact_eq (fun concl' ->
      let tmp_bound = !current_bound_vars in
      current_bound_vars := [];
      let hyp'' = List.map copy_fact2 hyp' in
      let concl'' = copy_fact2 concl' in
      let histref = ref hist in
      let rank = ref 0 in
      List.iter2 (fun hyp1 hyp1' ->
	if not (equal_facts hyp1 hyp1') then
	  histref := HEquation(!rank, copy_fact2 hyp1, copy_fact2 hyp1', !histref);
	incr rank) hyp hyp';
      let r = (hyp'', concl'',
	       (if equal_facts concl concl' then
		 (!histref)
	       else
		 HEquation(-1, concl'', copy_fact2 concl, !histref)),
	       List.map copy_constra2 constra) in
      cleanup();
      restwork r;
      current_bound_vars := tmp_bound
		  ) concl) hyp

let close_rule_hyp_eq restwork (hyp,concl,hist,constra) =
  close_fact_list_eq (fun hyp' ->
      let tmp_bound = !current_bound_vars in
      current_bound_vars := [];
      let hyp'' = List.map copy_fact2 hyp' in
      let histref = ref hist in
      let rank = ref 0 in
      List.iter2 (fun hyp1 hyp1' ->
	if not (equal_facts hyp1 hyp1') then
	  histref := HEquation(!rank, copy_fact2 hyp1, copy_fact2 hyp1', !histref);
	incr rank) hyp hyp';
      let r = (hyp'', copy_fact2 concl, (!histref),
	       List.map copy_constra2 constra) in
      cleanup();
      restwork r;
      current_bound_vars := tmp_bound
		  ) hyp

let close_term_eq restwork t =
  if hasEquations() then close_term_eq restwork t else restwork t

let close_term_list_eq restwork t =
  if hasEquations() then close_term_list_eq restwork t else restwork t

let close_fact_eq restwork t =
  if hasEquations() then close_fact_eq restwork t else restwork t

let close_fact_list_eq restwork t =
  if hasEquations() then close_fact_list_eq restwork t else restwork t

let close_rule_eq restwork t =
  if hasEquations() then close_rule_eq restwork t else restwork t


(***** Close clauses by rewrite rules of constructors and destructors. *****
   Used for clauses that define predicates (for LetFilter).

   The variable accu_constra collects side-conditions of
   destructors. *)

let rec close_term_destr_eq accu_constra restwork = function
    Var x ->
      begin
	match x.link with
          TLink t ->
	  (* TO DO should I always recursively close links modulo equations? *)
	    close_term_eq (fun t' -> restwork accu_constra t') t
	| NoLink -> restwork accu_constra (Var x)
	| _ -> internal_error "unexpected link in close_term_destr_eq"
      end
  | FunApp(f,l) ->
      close_term_destr_list_eq accu_constra (fun accu_constra' l' ->
	let eqlist = Terms.red_rules_fun f in

	List.iter (fun red ->
	  Terms.auto_cleanup (fun () ->
	    let (leq', req', side_c') = copy_red red in

	    try
	      List.iter2 unify l' leq';
	      restwork (side_c' @ accu_constra') req'
	    with Unify -> ()
		)
	    ) eqlist
        ) l

and close_term_destr_list_eq accu_constra restwork = function
    [] -> restwork accu_constra []
  | (a::l) ->
      close_term_destr_eq accu_constra (fun accu_constra' a' ->
	close_term_destr_list_eq accu_constra' (fun accu_constra'' l' ->
	  restwork accu_constra'' (a'::l')) l) a

let close_fact_destr_eq accu_constra restwork = function
    Pred(p,l) ->
      close_term_destr_list_eq accu_constra
	(fun accu_constra' l' ->
	  Terms.auto_cleanup (fun () ->
	    try
	    (* Check that the arguments of the predicate do not fail,
	       by unifying them with a message variable (which cannot be fail) *)
	      List.iter (fun t -> unify t (Terms.new_var_def (Terms.get_term_type t))) l';
	      restwork accu_constra' (Pred(p,l'))
	    with Unify -> ()
		)
	    ) l
  | Out(t,l) ->
      Parsing_helper.internal_error "Out facts should not appear in TermsEq.close_fact_destr_eq"

let rec close_fact_destr_list_eq accu_constra restwork = function
    [] -> restwork accu_constra []
  | (a::l) ->
      close_fact_destr_eq accu_constra (fun accu_constra' a' ->
	close_fact_destr_list_eq accu_constra' (fun accu_constra'' l' ->
	  restwork accu_constra'' (a'::l')) l) a

let close_constra1_destr_eq accu_constra restwork = function
    Neq(t1,t2) ->
      close_term_destr_eq accu_constra (fun accu_constra' t1' ->
	close_term_destr_eq accu_constra' (fun accu_constra'' t2' ->
	  Terms.auto_cleanup (fun () ->
	    try
	    (* Check that the arguments of Neq do not fail,
	       by unifying them with a message variable (which cannot be fail) *)
	      unify t1' (Terms.new_var_def (Terms.get_term_type t1'));
	      unify t2' (Terms.new_var_def (Terms.get_term_type t2'));
	      restwork accu_constra'' (Neq(t1',t2'))
	    with Unify -> ()
		)
	    ) t2) t1

let rec close_constra_destr_eq accu_constra restwork = function
    [] -> restwork accu_constra []
  | (a::l) ->
      close_constra1_destr_eq accu_constra (fun accu_constra' a' ->
	close_constra_destr_eq accu_constra' (fun accu_constra'' l' ->
	  restwork accu_constra'' (a'::l')
	    ) l) a

let rec close_constra_destr_list_eq accu_constra restwork = function
    [] -> restwork accu_constra []
  | (a::l) ->
      close_constra_destr_eq accu_constra (fun accu_constra' a' ->
	close_constra_destr_list_eq accu_constra' (fun accu_constra'' l' ->
	  restwork accu_constra'' (a'::l')
	    ) l) a

let close_rule_destr_eq restwork (hyp,concl,constra) =
  close_fact_destr_list_eq [] (fun accu_constra hyp' ->
    close_fact_destr_eq accu_constra (fun accu_constra' concl' ->
      close_constra_destr_list_eq accu_constra' (fun accu_constra'' constra' ->
	let tmp_bound = !current_bound_vars in
	current_bound_vars := [];
	let r = (List.map copy_fact2 hyp', copy_fact2 concl',
		 List.map copy_constra2 ((List.map (fun (t1,t2) -> [Neq(t1,t2)]) accu_constra'') @ constra')) in
	cleanup();
	restwork r;
	current_bound_vars := tmp_bound
				  ) constra) concl) hyp

(********* Transform equations into rewrite rules *********)

(* Copy an equation *)

let copy_eq (leq, req) =
  assert (!current_bound_vars == []);
  let eq' = (copy_term2 leq, copy_term2 req) in
  cleanup();
  eq'

(* Swap sides of an equation *)

let swap_eq (leq, req) = (req, leq)

(* Complete the equations, to obtain all terms equal to one term
   Store the result in the information associated with each constructor *)

let rewrite_system = ref []
let order = ref []

let rec normal_form = function
    Var v -> Var v
  | FunApp(f,l) ->
      let t' = FunApp(f, List.map normal_form l) in
      let rec find_red = function
        [] -> t'
      | ((leq,req)::redl) ->
         try
	   if not (Terms.equal_types (Terms.get_term_type leq) (Terms.get_term_type t')) then
      raise NoMatch;
           Terms.match_terms leq t';
           let r = copy_term3 req in
           Terms.cleanup();
           normal_form r
         with NoMatch ->
           Terms.cleanup();
           find_red redl
      in
      find_red (!rewrite_system)

let rec joinable_critical_pairs build_context (leq1, req1) (leq2, req2) =
  match leq2 with
    Var v -> true
  | FunApp(f,l) ->
      ((not (Terms.equal_types (Terms.get_term_type leq1) (Terms.get_term_type leq2))) ||
       (try
	 Terms.unify leq1 leq2;
	 let req1' = copy_term2 (build_context req1) in
	 let req2' = copy_term2 req2 in
	 Terms.cleanup();
	 let r = Terms.equal_terms (normal_form req1') (normal_form req2') in
	 (*if not r then
	   begin
	     print_string "Non-joinable critical pair:";
	     display_eq (leq1,req1);
	     print_string " and ";
	     display_eq (leq2,req2);
	     print_string ". We should have ";
	     display_eq (req1',req2');
	     print_string "\n"
	   end;*)
	 r
       with Unify ->
	 Terms.cleanup();
	 true
      ))
	&&
      (
       let seen = ref [] in
       let to_see = ref l in
       List.for_all (fun x ->
	 to_see := List.tl (!to_see);
	 let cur_seen = !seen in
	 let cur_to_see = !to_see in
	 let r = joinable_critical_pairs (fun y -> build_context (
	   FunApp(f, List.rev_append cur_seen (y :: cur_to_see))))
	     (leq1, req1) (x, req2) in
	 seen := x :: (!seen);
	 r) l
      )


let rec check_confluent new_rule = function
  [] -> true
| (a::l) ->
    (joinable_critical_pairs (fun x -> x) a new_rule) &&
    (joinable_critical_pairs (fun x -> x) new_rule a) &&
    (check_confluent new_rule l)


let eq_queue = Pvqueue.new_queue()
let eq_base = ref []
let eq_count = ref 0

let rec build_rules_eq leq req f get_rule = function
   FunApp(f2,l) as t ->
      if f2 == f then
      begin
	assert (!current_bound_vars == []);
        try
          unify t leq;
          get_rule req
        with Unify ->
          cleanup()
      end;
      build_rules_eq_list leq req f (fun concl_list -> get_rule (FunApp(f2,concl_list))) l
  | Var _ -> ()

and build_rules_eq_list leq req f get_rule = function
    [] -> ()
  | (a::l) ->
      build_rules_eq leq req f (fun concl -> get_rule (concl::l)) a;
      build_rules_eq_list leq req f (fun concl_list -> get_rule (a::concl_list)) l

let rec implies_eq (leq1, req1) (leq2, req2) =
  assert (!current_bound_vars == []);
  try
    if not (Terms.equal_types (Terms.get_term_type leq1) (Terms.get_term_type leq2)) then
      raise NoMatch;
    Terms.match_terms leq1 leq2;
    Terms.match_terms req1 req2;
    cleanup();
    true
  with NoMatch ->
    cleanup();
    (* Try to match the equation inside a context *)
    match leq2, req2 with
      (FunApp(fl, ll), FunApp(fr, lr)) when fl == fr ->
	List.exists2 (fun leq2 req2 ->
	  implies_eq (leq1, req1) (leq2, req2)) ll lr
    | _ -> false

let add_eq (leq, req) =
  (* reduce to normal form *)
  let leq =
    match leq with
      FunApp(f,l) -> FunApp(f, List.map normal_form l)
    | _ -> leq in
  let req = normal_form req in
  let new_eq = (leq, req) in
  (* check not a trivial equation *)
  if equal_terms leq req then () else
  (* check not x = y *)
  match (leq, req) with
    Var x, Var y when x != y ->
      user_error "The equational theory equates all terms.\nThis trivial case is not supported by the verifier."
  | _ ->
  (* check not subsumed *)
  let test_impl = fun eq -> implies_eq eq new_eq in
  if (List.exists test_impl (!eq_base)) ||
     (Pvqueue.exists eq_queue test_impl) then () else
  begin
    let test_impl = fun eq -> not(implies_eq new_eq eq) in
    eq_base := List.filter test_impl (!eq_base);
    Pvqueue.filter eq_queue test_impl;
    Pvqueue.add eq_queue new_eq
  end

(* Combine leq2 -> req2 followed by leq1 -> req1
   when req2 unifies with C[leq1] *)

let combine_eq_eq1 (leq1, req1) (leq2, req2) =
  match leq1 with
    Var _ -> ()
  | FunApp(f,_) ->
      build_rules_eq leq1 req1 f (fun new_term ->
        let eq3 = (copy_term2 leq2, copy_term2 new_term) in
        cleanup();
        add_eq eq3) req2

(* Combine leq2 -> req2 followed by leq1 -> req1
   when leq1 unifies with C[req2] *)

let combine_eq_eq2 (leq1, req1) (leq2, req2) =
  match req2 with
    Var _ -> ()
  | FunApp(f,_) ->
      build_rules_eq req2 leq2 f (fun new_term ->
        let eq3 = (copy_term2 new_term, copy_term2 req1) in
        cleanup();
        add_eq eq3) leq1

(* Close the equational theory *)

let rec complete_eq bothdir =
  match Pvqueue.get eq_queue with
    None -> !eq_base
  | Some eq ->
      eq_base := eq :: (!eq_base);
      let eq' = copy_eq eq in
      List.iter (fun eq2 ->
	combine_eq_eq1 eq' eq2;
	combine_eq_eq1 eq2 eq';
	if bothdir then
	  begin
	    combine_eq_eq2 eq' eq2;
	    combine_eq_eq2 eq2 eq';
	    if (!rewrite_system) != [] then (* Useful only for non-proved algo. *)
	      begin
		let eqs' = swap_eq eq' in
		let eqs2 = swap_eq eq2 in
		(* Swap eq' *)
		combine_eq_eq1 eqs' eq2;
		combine_eq_eq1 eq2 eqs';
		combine_eq_eq2 eqs' eq2;
		combine_eq_eq2 eq2 eqs';
		(* Swap eq2 *)
		combine_eq_eq1 eq' eqs2;
		combine_eq_eq1 eqs2 eq';
		combine_eq_eq2 eq' eqs2;
		combine_eq_eq2 eqs2 eq';
		(* Swap eq' and eq2 *)
		combine_eq_eq1 eqs' eqs2;
		combine_eq_eq1 eqs2 eqs';
		combine_eq_eq2 eqs' eqs2;
		combine_eq_eq2 eqs2 eqs';
	      end (* End useful only for non-proved algo. *)
	  end) (!eq_base);
      if !Param.verbose_rules then
	begin
          Display.Text.display_eq eq;
	  Display.Text.newline()
	end
      else
         begin
           incr eq_count;
	   if (!eq_count) mod 200 = 0 then
	     begin
	       print_string ((string_of_int (!eq_count)) ^
			     " equations inserted. The rule base contains " ^
			     (string_of_int (List.length (!eq_base))) ^
			     " equations. " ^
			     (string_of_int (Pvqueue.length eq_queue)) ^
			     " equations in the queue.");
	       Display.Text.newline()
	     end
	 end;
       complete_eq bothdir

(* Check subterm *)

let rec check_subterm t1 t2 =
  (equal_terms t1 t2) || (check_strict_subterm t1 t2)

and check_strict_subterm t1 t2 =
  match t1 with
    FunApp(_,l) -> List.exists (fun t -> check_subterm t t2) l
  | _ -> false

(* Find the rewrite system S *)

let add_rewrite ((leq, req) as r) =
  (* check that all variables on the right-hand side also occur in the
     left-hand side *)
  let var_right = ref [] in
  Terms.get_vars var_right req;
  if List.for_all (fun v -> Terms.occurs_var v leq) (!var_right) then
    begin
      (* check that the resulting system is confluent *)
      rewrite_system := r :: (!rewrite_system);
      if not (check_confluent r (!rewrite_system)) then
	begin
	  rewrite_system := List.tl (!rewrite_system);
	  false
	end
      else
	true
    end
  else
    false

let rec check_no_path f f' =
  (f != f') &&
  (List.for_all (fun (f2,f2') ->
    if f == f2 then check_no_path f2' f' else true) (!order))


let find_rewrite_system eq =
  let (leq, req) = copy_eq eq in
  if check_strict_subterm req leq then
    ignore (add_rewrite (leq, req))
  else
    match leq with
      FunApp(f,l) ->
	let rec find_fun_symb accu = function
	    Var _ -> accu
	  | FunApp(f2,l2) ->
	      let accu' = if List.memq f2 accu then accu else f2::accu in
	      List.fold_left find_fun_symb accu' l2
	in
	let new_symbols = find_fun_symb [] req in
	if List.for_all (fun f2 -> check_no_path f2 f) new_symbols then
	  if add_rewrite (leq, req) then
	    order := (List.map (fun f2 -> (f,f2)) new_symbols) @ (!order)
    | Var _ -> ()


(* Lexicographic path ordering *)

let rec add_order = function
    (FunApp(f1,l1), (FunApp(f2,l2) as t2)) when f1 == f2 ->
      List.iter (fun t1 -> add_order (t1,t2)) l1;
      List.iter2 (fun t1 t2 -> add_order  (t1,t2)) l1 l2
  | (FunApp(f1,l1), t2) when occurs_f f1 t2 ->
      (*
      Useful for finding a good ordering for Delaune-ex3.prv, but then
      the generation of the rewrite rules corresponding to the equations
      does not terminate anyway, so it's not that useful.
      begin
	match t2 with
	  FunApp(f2,_) ->
	    if check_no_path f2 f1 then
	      order := (f1,f2) :: (!order)
	| _ -> ()
      end; *)
      List.iter (fun t1 -> add_order (t1,t2)) l1
  | (FunApp(f1,l1), t2) ->
      let rec find_fun_symb accu = function
	  Var _ -> accu
	| FunApp(f2,l2) ->
	    let accu' = if List.memq f2 accu then accu else f2::accu in
	    List.fold_left find_fun_symb accu' l2
      in
      let new_symbols = find_fun_symb [] t2 in
      if List.for_all (fun f2 -> check_no_path f2 f1) new_symbols then
	order := (List.map (fun f2 -> (f1,f2)) new_symbols) @ (!order)
  | _ -> ()

let rec get_symbols_t accu = function
    FunApp(f,l) ->
      if not (List.memq f (!accu)) then
	accu := f :: (!accu);
      List.iter (get_symbols_t accu) l
  | Var _ -> ()

let get_symbols accu equations =
  List.iter (fun (t1,t2) ->
    get_symbols_t accu t1;
    get_symbols_t accu t2) equations

let rec convert_to_symbols symbols = function
    [] -> []
  | ((s,ext)::l) ->
      try
	let f = List.find (fun f -> f.f_name = s) symbols in
	f::(convert_to_symbols symbols l)
      with Not_found ->
	convert_to_symbols symbols l

let rec convert_to_pairs ext = function
    [] | [_] -> []
  | a::((b::l) as l') ->
      if List.memq a l' then
	Parsing_helper.input_error ("Ordering of function symbols contain a duplicate element " ^ a.f_name ^ ".\n") ext;
      (a,b)::(convert_to_pairs ext l')

let order_from_string (s,ext0) equations =
  let symbols = ref [] in
  List.iter (fun (eq, _) -> get_symbols symbols eq) equations;
  let lexbuf = Lexing.from_string s in
  Parsing_helper.set_start lexbuf ext0;
  let order =
    try
      Pitparser.order Pitlexer.token lexbuf
    with Parsing.Parse_error ->
      Parsing_helper.input_error "Syntax error in ordering"
	(Parsing_helper.extent lexbuf)
  in
  let order = convert_to_symbols (!symbols) order in
  convert_to_pairs ext0 order

let rec greater_lpo t1 t2 = match (t1,t2) with
  (Var v1, _) -> false
| (t1, Var v2) -> occurs_var v2 t1
| (FunApp(f1,l1), FunApp(f2,l2)) ->
    (List.exists (fun t1' -> equal_terms t1' t2 || greater_lpo t1' t2) l1) ||
    ((f1 != f2) && (not (check_no_path f1 f2)) &&
     (List.for_all (greater_lpo t1) l2)) ||
    ((f1 == f2) && (greater_lpo_lex l1 l2))

and greater_lpo_lex l1 l2 = match (l1,l2) with
  ([], []) -> false
| (t1::l1',t2::l2') ->
    (greater_lpo t1 t2) ||
    ((equal_terms t1 t2) && (greater_lpo_lex l1' l2'))
| _ -> Parsing_helper.internal_error "Different length in greater_lpo_lex"

(* Build block of equations disjoint from others *)

let rec get_fun_symb flist = function
    Var v -> ()
  | FunApp(f,l) ->
      if not (List.mem f (!flist)) then flist := f :: (!flist);
      List.iter (get_fun_symb flist) l

let rec unionlist l1 = function
    [] -> l1
  | (a::l) ->
      if List.memq a l1 then
	unionlist l1 l
      else
	a::(unionlist l1 l)

let disjoint_list l1 l2 =
  List.for_all (fun x1 -> not (List.memq x1 l2)) l1

let buildblocks eqlists =
  (* Group the blocks of equations into two sets:
     no_info_block: all equations with no specific information
     other_blocks: the groups of equations with specific information *)
  let no_info_block = ref [] in
  let other_blocks = ref [] in
  let no_check_blocks : ((term * term) list * eq_info) list =
    List.filter (fun (_, eqinfo) ->
	eqinfo = EqNoCheck
      ) eqlists
  in
  List.iter (fun (eqlist, eqinfo) ->
    if eqinfo = EqNoInfo then
      no_info_block := eqlist @ (!no_info_block)
    else if eqinfo = EqNoCheck then
      ()
    else
      let flist = ref [] in
      List.iter (fun (eq1,eq2) ->
	get_fun_symb flist eq1;
	get_fun_symb flist eq2) eqlist;
      other_blocks := (!flist, eqlist, eqinfo) :: (!other_blocks)
						    ) eqlists;
  (* Split no_info_block into groups of equations with disjoint
     function symbols *)
  let blocks = ref [] in
  List.iter (fun eq ->
    let flist = ref [] in
    get_fun_symb flist (fst eq);
    get_fun_symb flist (snd eq);
    let tmpblocks = !blocks in
    let cur_block = ref ((!flist),[eq]) in
    blocks := [];
    List.iter (fun (bfunsymb, beq) ->
      if List.exists (fun f1 -> List.memq f1 (!flist)) bfunsymb then
	(* Block has common function symbol with cur_block
           -> merge them *)
	cur_block := (unionlist bfunsymb (fst (!cur_block)),
		      beq @ (snd (!cur_block)))
      else
	(* Block has no common function symbol with cur_block
           -> leave it as it is *)
	blocks := (bfunsymb, beq) :: (!blocks)
      ) tmpblocks;
    blocks := (!cur_block) :: (!blocks);
    ) (!no_info_block);
  (* Check that the other groups of equations (!other_blocks)
     use pairwise disjoint sets of function symbols *)
  List.iter (fun (f1,l1,_) ->
    List.iter (fun (f2,l2) ->
      if not (disjoint_list f1 f2) then
	begin
	  print_string "Error: the following sets of equations";
	  Display.Text.display_item_list Display.Text.display_eq l1;
	  print_string "and";
	  Display.Text.display_item_list Display.Text.display_eq l2;
	  print_string "use common function symbols.\n";
	  Parsing_helper.user_error "Blocks of equations marked [convergent] or [linear] should use function symbols disjoint from equations not marked [convergent] or [linear]."
	end
	  ) (!blocks)
      ) (!other_blocks);
  let rec check_disj = function
      [] -> ()
    | (f1,l1,_)::l ->
	List.iter (fun (f2,l2,_) ->
	  if not (disjoint_list f1 f2) then
	    begin
	      print_string "Error: the following sets of equations";
	      Display.Text.display_item_list Display.Text.display_eq l1;
	      print_string "and";
	      Display.Text.display_item_list Display.Text.display_eq l2;
	      print_string "use common function symbols.\n";
	      Parsing_helper.user_error "Blocks of equations marked [convergent] or [linear] should use function symbols disjoint from each other."
	    end
	      ) l;
	check_disj l
  in
  check_disj (!other_blocks);
  (* Return the blocks of equations, with associated eqinfo *)
  (List.map (fun (_,eqlist) -> (eqlist, EqNoInfo)) (!blocks))
  @ (List.map (fun (_,eqlist,eqinfo) -> (eqlist,eqinfo)) (!other_blocks))
  @ no_check_blocks

(* Check block convergent *)

exception Nontermination of equation
exception Nonconfluent of equation * equation

let check_term block =
  (* Check termination *)
  List.iter (fun ((leq, req) as eq) -> if not (greater_lpo leq req) then
    raise (Nontermination eq)) block

let check_confluent block =
  (* Check confluence *)
  rewrite_system := block;
  List.iter (fun r1 ->
    let r1 = copy_eq r1 in
    List.iter (fun r2 ->
      if not (joinable_critical_pairs (fun x -> x) r1 r2) then
	begin
	  rewrite_system := [];
	  raise (Nonconfluent(r1,r2))
	end) block
	) block;
  rewrite_system := []

let check_convergent block =
  check_term block;
  check_confluent block

(* Check block linear *)

let rec is_linear_term vlist = function
    Var v ->
      if List.memq v (!vlist) then false else
      begin
	vlist := v :: (!vlist);
	true
      end
  | FunApp(_,l) ->
      List.for_all (is_linear_term vlist) l

let is_linear block =
  List.for_all (fun (leq, req) ->
    (is_linear_term (ref []) leq) && (is_linear_term (ref []) req)) block


(* Transforms equations into "equational destructors" *)

let record_eqs_internal equations_list =
  if !Param.eqtreatment = Param.ConvLin then
  begin
    (*print_string "Building order...";
    Display.Text.newline();*)
    begin
       match !Param.symb_order with
	 None ->
	   List.iter (fun (l, _) -> List.iter add_order l) equations_list
       | Some sext ->
	   order := order_from_string sext equations_list
    end;
    (*print_string "Order:\n";
    List.iter (fun (f1,f2) -> print_string (f1.f_name ^ " > " ^ f2.f_name ^ "\n")) (!order);
    print_string "Building blocks...";
    Display.Text.newline();*)
    let blocks = buildblocks equations_list in
    (*print_string "Separating convergent/linear...";
    Display.Text.newline();*)
    let convergent_part = ref [] in
    let linear_part = ref [] in
    List.iter (fun (block,eqinfo) ->
      match eqinfo with
	EqNoInfo ->
	  begin
	  try
	    check_convergent block;
            convergent_part := block @ (!convergent_part)
	  with
	    (Nontermination _ | Nonconfluent _) as e ->
	      if is_linear block then
		linear_part := block @ (!linear_part)
	      else
		begin
		  print_string "Error: Cannot handle the following equations:";
		  Display.Text.display_item_list Display.Text.display_eq block;
		  print_string "This block of equations is not linear and could not be proved convergent.\n";
		  begin
		    match e with
		      Nontermination eq ->
			print_string "(I could not prove that\n";
			Display.Text.display_eq eq;
			print_string "\nis decreasing in a lexicographic path ordering.\nIf you know that your equations are convergent, you can bypass the\ntermination check by declaring your equations by:\n  equation (your convergent equations) [convergent].)\n"
		    | Nonconfluent(eq1,eq2) ->
			print_string "(The system is not confluent because of a critical pair between\n";
			Display.Text.display_eq eq1;
			print_string "\nand\n";
			Display.Text.display_eq eq2;
			print_string ".)\n"
		    | _ -> Parsing_helper.internal_error "TermsEq: added to avoid warning for non-exhaustive pattern-matching"
		  end;
		  Parsing_helper.user_error "These equations cannot be handled."
		end
        end
      | EqLinear ->
	  if is_linear block then
	    linear_part := block @ (!linear_part)
	  else
	    begin
	      print_string "Error: Cannot handle the following equations:";
	      Display.Text.display_item_list Display.Text.display_eq block;
	      print_string "This block of equations is declared linear but it is not.\n";
	      Parsing_helper.user_error "These equations cannot be handled."
	    end
      |	EqConvergent ->
	  begin
	    try
	      check_term block
	    with Nontermination _ ->
	      print_string "Warning: the following equations";
	      Display.Text.display_item_list Display.Text.display_eq block;
	      print_string "are declared convergent. I could not prove termination.\n";
	      print_string "I assume that they really terminate.\n";
	      print_string "Expect problems (such as ProVerif going into a loop) if they do not!\n";
	      flush stdout
	  end;
	  begin
	    try
	      check_confluent block
	    with Nonconfluent(eq1,eq2) ->
	      print_string "Error: Cannot handle the following equations:";
	      Display.Text.display_item_list Display.Text.display_eq block;
	      print_string "This block of equations is declared convergent but it is not\n";
	      print_string "confluent because of a critical pair between\n";
	      Display.Text.display_eq eq1;
	      print_string "\nand\n";
	      Display.Text.display_eq eq2;
	      print_string ".)\n";
	      Parsing_helper.user_error "These equations cannot be handled."
	  end;
          convergent_part := block @ (!convergent_part)
      | EqNoCheck -> ()
	) blocks;

    if !Param.html_output then
      begin
        Display.Html.print_string "<H2>Linear part</H2>\n";
        Display.Html.print_string "Initial equations:";
        Display.Html.display_item_list Display.Html.display_eq (!linear_part)
      end
    else if !Param.verbose_eq then
      begin
        Display.Text.print_string "Linear part:";
        Display.Text.display_item_list Display.Text.display_eq (!linear_part)
      end;
    List.iter (fun eq ->
       add_eq eq;
       add_eq (swap_eq eq)) (!linear_part);
    print_string "Completing equations...";
    Display.Text.newline();
    let resulting_equations_linear = complete_eq true in
    eq_base := [];
    if !Param.html_output then
      begin
        Display.Html.print_string "Completed equations:";
        Display.Html.display_item_list Display.Html.display_eq resulting_equations_linear
      end
    else if !Param.verbose_eq then
      begin
        Display.Text.print_string "Completed equations:";
        Display.Text.display_item_list Display.Text.display_eq resulting_equations_linear
      end;

    if !Param.html_output then
      begin
        Display.Html.print_string "<H2>Convergent part</H2>\n";
        Display.Html.print_string "Initial equations:";
	Display.Html.display_item_list Display.Html.display_eq (!convergent_part)
      end
    else if !Param.verbose_eq then
      begin
        Display.Text.print_string "Convergent part:";
	Display.Text.display_item_list Display.Text.display_eq (!convergent_part)
      end;
    rewrite_system := !convergent_part;
    List.iter add_eq (!convergent_part);
    print_string "Completing equations...";
    Display.Text.newline();
    let resulting_equations_convergent = complete_eq false in
    if !Param.html_output then
      begin
        Display.Html.print_string "Completed equations:";
        Display.Html.display_item_list Display.Html.display_eq resulting_equations_convergent
      end
    else if !Param.verbose_eq then
      begin
        Display.Text.print_string "Completed equations:";
            Display.Text.display_item_list Display.Text.display_eq resulting_equations_convergent
      end;

    let resulting_equations = resulting_equations_linear @ resulting_equations_convergent in
    (* record the equations in each constructor *)
    List.iter (function
      (FunApp(f, l), req) as eq ->
        begin
	  let var_list_rhs = ref [] in
	  Terms.get_vars var_list_rhs req;
	  if not (List.for_all (fun v -> List.exists (Terms.occurs_var v) l) (!var_list_rhs)) then
	    begin
	      print_string "Error in equation: ";
	      Display.Text.display_eq eq;
	      print_newline();
	      Parsing_helper.user_error "All variables of the right-hand side of an equation\nshould also occur in the left-hand side."
	    end;

          match f.f_cat with
            Eq leq -> f.f_cat <- Eq ((l, req) :: leq)
          | _ -> user_error "Does not support equations on non-constructors"
        end
    | _ -> ()) resulting_equations

  end
  else
  begin
    (* Old, non-proved treatment of equations.
       Kept just in case it is useful...
       Just ignore the convergent/linear information. *)
     let eq_list = ref [] in
     List.iter (fun (eqlist,_) ->
       eq_list := eqlist @ (!eq_list)) equations_list;
    List.iter find_rewrite_system (!eq_list);
    if !Param.verbose_eq then
      begin
        print_string "Rewriting system:";
        Display.Text.display_item_list Display.Text.display_eq (!rewrite_system)
      end;

    List.iter (fun eq -> add_eq eq;
                         add_eq (swap_eq eq)) (!eq_list);
    print_string "Completing equations...";
    Display.Text.newline();
    let resulting_equations = complete_eq true in
    (* record the equations in each constructor *)
    if !Param.verbose_eq then
      begin
	print_string "Completed equations:";
	Display.Text.display_item_list Display.Text.display_eq resulting_equations
      end;
    List.iter (function
      (FunApp(f, l), req) as eq ->
        begin
	  let var_list_rhs = ref [] in
	  Terms.get_vars var_list_rhs req;
	  if not (List.for_all (fun v -> List.exists (Terms.occurs_var v) l) (!var_list_rhs)) then
	    begin
	      print_string "Equation: ";
	      Display.Text.display_eq eq;
	      print_newline();
	      Parsing_helper.user_error "All variables of the right-hand side of an equation\nshould also occur in the left-hand side."
	    end;

          match f.f_cat with
            Eq leq -> f.f_cat <- Eq ((l, req) :: leq)
          | _ -> user_error "Does not support equations on non-constructors"
        end
    | _ -> ()) resulting_equations

   end


(****** Unification modulo the equational theory ******)

(* Equivalent of copy_term, but replaces function symbols with
   syntactic ones *)

let syntactic_table = Hashtbl.create 7

let get_syntactic f =
  try
    Hashtbl.find syntactic_table f
  with Not_found ->
    let f' = { f_orig_name = f.f_orig_name;
               f_name = (* "sy_" ^ *) f.f_name;
               f_type = f.f_type;
               f_cat = Syntactic f;
               f_initial_cat = Syntactic f;
               f_private = f.f_private;
               f_options = f.f_options } in
    Hashtbl.add syntactic_table f f';
    f'

let rec put_syntactic = function
  | FunApp(f,l) -> FunApp(get_syntactic f, List.map put_syntactic l)
  | Var v ->
      match v.link with
      |	NoLink ->
          let r =
            { v_orig_name = v.v_orig_name;
              vname = v.vname;
              sname = v.sname;
              unfailing = v.unfailing;
              btype = v.btype;
              link = NoLink }
	  in
          link v (VLink r);
          Var r
      | VLink l -> Var l
      | _ -> internal_error "Unexpected link in put_syntactic"

(* Equivalent of copy_term2, but replaces syntactic function symbols
   with their non-syntactic equivalents *)

let rec copy_remove_syntactic = function
  | FunApp(f,l) -> FunApp(non_syntactic f, List.map copy_remove_syntactic l)
  | Var v ->
      match v.link with
	NoLink ->
	  let r = copy_var v in
	  link v (VLink r);
          Var r
      | TLink l -> copy_remove_syntactic l
      | VLink r -> Var r
      | _ -> internal_error "unexpected link in copy_remove_syntactic"

let copy_remove_syntactic_pair = fun (v,t) -> (v, copy_remove_syntactic t)

let copy_remove_syntactic_fact = function
    Pred(chann, t) -> Pred(chann, List.map copy_remove_syntactic t)
  | Out(t,l) -> Out(copy_remove_syntactic t, List.map copy_remove_syntactic_pair l)

let rec copy_remove_syntactic_constra c = List.map (function
    Neq(t1,t2) -> Neq(copy_remove_syntactic t1, copy_remove_syntactic t2)) c

(* Remove syntactic function symbols without copying *)

let rec remove_syntactic_term = function
 | FunApp(f,l) -> FunApp(non_syntactic f, List.map remove_syntactic_term l)
 | Var v -> match v.link with
      NoLink -> Var v
    | TLink l -> remove_syntactic_term l
    | _ -> internal_error "unexpected link in remove_syntactic_term"

let remove_syntactic_pair = fun (v,t) -> (v, remove_syntactic_term t)

let remove_syntactic_fact = function
    Pred(chann, t) -> Pred(chann, List.map remove_syntactic_term t)
  | Out(t,l) -> Out(remove_syntactic_term t, List.map remove_syntactic_pair l)

let rec remove_syntactic_constra c = List.map (function
    Neq(t1,t2) -> Neq(remove_syntactic_term t1, remove_syntactic_term t2)
	) c

(* Collect variables that are not defined yet *)

let rec collect_unset_vars accu = function
    FunApp(f,l) -> List.iter (collect_unset_vars accu) l
  | Var v ->
      match v.link with
	NoLink ->
	  if not (List.memq v (!accu)) then
	    accu := v :: (!accu)
      | TLink t -> collect_unset_vars accu t
      | _ -> internal_error "unexpected link in collect_unset_vars"

(* Unification modulo itself *)

let f_has_no_eq f =
  match f.f_cat with
    Eq [] -> true
  | Eq _ -> false
  | _ -> true

exception NoBacktrack of binder list ref

let rec close_term_eq_synt restwork = function
  | (Var x) as t ->
    begin
      match x.link with
	| TLink t -> close_term_eq_synt restwork t
	| NoLink -> restwork t
	| _ -> internal_error "unexpected link in close_term_eq_synt"
    end
  | (FunApp(f,l) as t) when f_has_no_eq f ->
      (* Distinguishing this case explicitly helps avoiding a
	 stack overflow: the stack does not grow in this case
	 because we make a tail call. *)
      restwork t
  | (FunApp(f,l) as t) ->
      try
      	auto_cleanup (fun () -> restwork t)
      with Unify ->
	match f.f_cat with
	| Eq eqlist ->
	    let rec reweqlist = function
	      | (leq, req) :: lrew ->
		  let leq', req'  = auto_cleanup (fun () ->
		    List.map put_syntactic leq,
		    put_syntactic req)
		  in
		  begin
		    try
		      auto_cleanup (fun () ->
			unify_modulo_list (fun () -> restwork req')  l leq')
		    with Unify ->
		      (* Try another rewriting when Unify is raised *)
		      reweqlist lrew
		  end
	      | [] -> raise Unify
	    in
	    reweqlist eqlist
	| _ -> Parsing_helper.internal_error "close_term_eq_synt: cases other than Eq should have been treated before"

and unify_modulo restwork t1 t2 =
  close_term_eq_synt (fun t1 ->
    close_term_eq_synt (fun t2 ->
      match (t1,t2) with
      | (Var v, Var v') when v == v' -> restwork ()
      | (Var v, _) ->
	  begin
	    match v.link with
	    | NoLink ->
		begin
		  match t2 with
		  | Var {link = TLink t2'} -> unify_modulo restwork t1 t2'
		  | Var v' when v.unfailing ->
		      link v (TLink t2);
		      restwork ()
		  | Var v' when v'.unfailing ->
		      link v' (TLink t1);
		      restwork ()
		  | FunApp (f_symb,_) when (non_syntactic f_symb).f_cat = Failure && v.unfailing = false -> raise Unify
		  | _ ->
		      occur_check v t2;
             	      link v (TLink t2);
             	      restwork ()
		end
	    | TLink t1' -> unify_modulo restwork t1' t2
	    | _ -> internal_error "Unexpected link in unify 1"
	  end
      | (FunApp(f,_), Var v) ->
	  begin
	    match v.link with
	    | NoLink ->
		if v.unfailing = false && (non_syntactic f).f_cat = Failure
		then raise Unify
		else
		  begin
		    occur_check v t1;
		    link v (TLink t1);
		    restwork ()
		  end
	    | TLink t2' -> unify_modulo restwork t1 t2'
	    | _ -> internal_error "Unexpected link in unify 2"
	  end
      | (FunApp(f1, l1), FunApp(f2,l2)) ->
  	  if (non_syntactic f1) != (non_syntactic f2) then raise Unify;
  	  unify_modulo_list restwork l1 l2
    ) t2
  ) t1

and unify_modulo_list_internal restwork l1 l2 =
  match (l1, l2) with
  | [], [] -> restwork ()
  | (a1::l1'), (a2::l2') ->
      begin
	let unset_vars = ref [] in
	collect_unset_vars unset_vars a1;
	collect_unset_vars unset_vars a2;
	try
	  unify_modulo (fun () ->
	    if not (List.exists (fun v -> v.link != NoLink) (!unset_vars))  then
              (* No variable of a1, a2 defined by unification modulo.
                 In this case, we do not need to backtrack on the choices made
                 in unify_modulo (...) a1 a2 when a subsequent unification fails. *)
	      raise (NoBacktrack unset_vars)
	    else
	      unify_modulo_list_internal restwork l1' l2'
		) a1 a2;
	with NoBacktrack unset_vars' when unset_vars == unset_vars' ->
	  unify_modulo_list_internal restwork l1' l2'
      end
  | _ -> internal_error "Lists should have same length in unify_modulo_list"

(* Optimized version of unification modulo: try to decompose
   the root symbols as much as possible when they do not use an
   equational theory. *)

and unify_modulo_list restwork l1 l2 =
  let unif_to_do_left = ref [] in
  let unif_to_do_right = ref [] in
  let rec add_unif_term t1 t2 =
    match t1, t2 with
      FunApp(f1, l1), FunApp(f2,l2) when f_has_no_eq f1 && f_has_no_eq f2 ->
  	if (non_syntactic f1) != (non_syntactic f2) then raise Unify;
	List.iter2 add_unif_term l1 l2
    | Var v, Var v' when v == v' -> ()
    | (Var v, _) ->
	  begin
	    match v.link with
	    | NoLink ->
		begin
		  match t2 with
		  | Var {link = TLink t2'} -> add_unif_term t1 t2'
		  | Var v' when v.unfailing ->
		      link v (TLink t2)
		  | Var v' when v'.unfailing ->
		      link v' (TLink t1)
		  | FunApp (f_symb,_) when (non_syntactic f_symb).f_cat = Failure && v.unfailing = false -> raise Unify
		  | _ ->
		      try
			occur_check v t2;
             		link v (TLink t2)
		      with Unify ->
			(* When the occur check fails, it might succeed
			   after rewriting the terms, so try that *)
			unif_to_do_left := t1 :: (!unif_to_do_left);
			unif_to_do_right := t2 :: (!unif_to_do_right)
		end
	    | TLink t1' -> add_unif_term t1' t2
	    | _ -> internal_error "Unexpected link in unify_modulo_list (optimized) 1"
	  end
      | (FunApp(f,_), Var v) ->
	  begin
	    match v.link with
	    | NoLink ->
		if v.unfailing = false && (non_syntactic f).f_cat = Failure
		then raise Unify
		else
		  begin
		    try
		      occur_check v t1;
		      link v (TLink t1)
		    with Unify ->
		      (* When the occur check fails, it might succeed
			 after rewriting the terms, so try that *)
		      unif_to_do_left := t1 :: (!unif_to_do_left);
		      unif_to_do_right := t2 :: (!unif_to_do_right)
		  end
	    | TLink t2' -> add_unif_term t1 t2'
	    | _ -> internal_error "Unexpected link in unify_modulo_list (optimized) 2"
	  end
      | _ ->
	  unif_to_do_left := t1 :: (!unif_to_do_left);
	  unif_to_do_right := t2 :: (!unif_to_do_right)
  in
  auto_cleanup (fun () ->
    List.iter2 add_unif_term l1 l2;
    unify_modulo_list_internal restwork (!unif_to_do_left) (!unif_to_do_right))

let unify_modulo restwork t1 t2 =
  unify_modulo_list restwork [t1] [t2]

(* Unification of environments, modulo an equational theory *)

let rec get_list l1 l2 =
  match (l1,l2) with
  | [],[] -> []
  | ((v1,t1)::l1'),((v2,t2)::l2') ->
      let l' = get_list l1' l2' in
      (* Unification of environments ignores variables that do not match.
	 When needed, the result of the unification should be an
	 environment that contains only the common variables *)
      if v1 == v2 then t1 :: l' else l'
  | _ -> internal_error "Lists should have same length in get_list"

let unify_modulo_env restwork l1 l2 =
  let len1 = List.length l1 in
  let len2 = List.length l2 in
  if len2 < len1 then
    begin
      let l1 = Terms.skip (len1-len2) l1 in
      unify_modulo_list restwork (get_list l1 l2) (get_list l2 l1)
    end
  else
    begin
      let l2 = Terms.skip (len2-len1) l2 in
      unify_modulo_list restwork (get_list l1 l2) (get_list l2 l1)
    end

(************** Treatment of inequality constraints ************)

(* Implication between constraints. Use this after simplification
   to get the best possible precision. *)

let assoc_gen_with_term = ref []

let rec implies_list_terms nextf l_t1 l_t2 = match (l_t1,l_t2) with
  | [], [] -> nextf ()
  | ((FunApp(f1,[]))::l1, t2::l2) when f1.f_cat = General_var ->
    begin
      try
	let t = List.assq f1 (!assoc_gen_with_term) in
	if not (equal_terms t t2) then raise NoMatch;

	implies_list_terms nextf l1 l2

      with Not_found ->
	assoc_gen_with_term := (f1, t2) :: (!assoc_gen_with_term);
	try
	  let r = implies_list_terms nextf l1 l2 in
	  assoc_gen_with_term := List.tl (!assoc_gen_with_term);
	  r
	with NoMatch ->
	  assoc_gen_with_term := List.tl (!assoc_gen_with_term);
	  raise NoMatch
    end

  | ((Var v1)::l1), ((Var v2)::l2) when v1 == v2 ->
      implies_list_terms nextf l1 l2
  | ((FunApp (f1,l1'))::l1, (FunApp (f2,l2'))::l2) ->
      if f1 != f2 then raise NoMatch;
      implies_list_terms nextf (l1' @ l1) (l2' @ l2)
  | _,_ -> raise NoMatch

let implies_simple_constraint nextf (Neq(t1,t1')) (Neq(t2, t2')) =
  implies_list_terms nextf [t1;t1'] [t2;t2']

let rec search_for_implied_constraint_in nextf sc1 = function
    [] -> raise NoMatch
  | (sc2::sc_l2) ->
        try
          implies_simple_constraint nextf sc1 sc2
        with NoMatch ->
          search_for_implied_constraint_in nextf sc1 sc_l2

let implies_constraint sc_list1 sc_list2 =
  let rec sub_implies_constraint sc_list1 sc_list2 () =
    match sc_list1 with
    | [] -> ()
    | sc1::sc_l1 -> search_for_implied_constraint_in (sub_implies_constraint sc_l1 sc_list2) sc1 sc_list2
  in
  try
    sub_implies_constraint sc_list1 sc_list2 ();
    true
  with NoMatch ->
    false

(* Simplification of constraints *)

(* Remark: for the way the subsumption test is implemented,
   it is important that all variables that occur in constraints
   also occur in the rest of the rule.
   Indeed, only the variables that occur in the rest of the rule
   are bound during the subsumption test. Other variables
   are always considered to be different, yielding the non-detection
   of subsumption

   When there is no universally quantified variable and no equational
   theory, we can simply remove all inequalities that contain variables
   not in the rest of the rule.
   However, "for all x, x <> y" is wrong even when y does not
   occur elsewhere. Similarly, "x <> decrypt(encrypt(x,y),y)" is wrong
   with the equation "decrypt(encrypt(x,y),y) = x".
   In this case, we can replace these variables with _new_
   constants.
   In the long run, the best solution might be to consider
   inequalities as an ordinary blocking predicate (and to remove
   constraints completely).
 *)

exception TrueConstraint
exception FalseConstraint

let any_val_counter = ref 0

(** [elim_var_if_possible has_gen_var keep_vars v] checks if [v] occurs
    in the list of variables [keep_vars]. If not then it adds a [Tlink]
    into [v] with an "any_val" symbol, so that [v] will be replaced
    with "any_val". *)
let elim_var_if_possible has_gen_var keep_vars v =
  if not (List.memq v keep_vars) then
  begin
    if (not has_gen_var) && (not (hasEquations()))
    then raise TrueConstraint
    else
      begin
        match v.link with
	| NoLink ->
	   incr any_val_counter;
           let name = "any_val" ^ (string_of_int (!any_val_counter)) in
	   Terms.link v (TLink (FunApp(
	      { f_orig_name = name;
                f_name = name;
	        f_type = [], v.btype;
		f_cat = Eq []; (* Should not be a name to avoid bad interaction with any_name_fsymb *)
		f_initial_cat = Eq []; (* Should not be a name to avoid bad interaction with any_name_fsymb *)
		f_private = true;
		f_options = 0 }, [])))
	| TLink _ -> ()
	| _ -> Parsing_helper.internal_error "unexpected link in elim_var_if_possible"
      end
  end

let rec check_vars_occurs has_gen_var keep_vars = function
  | FunApp(_,l) -> List.iter (check_vars_occurs has_gen_var keep_vars) l
  | Var v -> elim_var_if_possible has_gen_var keep_vars v

let rec has_gen_var = function
    Var v -> false
  | FunApp(f,[]) when f.f_cat = General_var -> true
  | FunApp(_,l) -> List.exists has_gen_var l

(** [elim_var_notelsewhere] expect contraints with variable on the left part
    of the disequation *)
let elim_var_notelsewhere has_gen_var keep_vars = function
  | (Neq(Var v1, Var v2)) ->
      assert(v1 != v2);
      elim_var_if_possible has_gen_var keep_vars v1;
      elim_var_if_possible has_gen_var keep_vars v2
      (* constraints Neq(x,t), where x does not appear in the keep_vars and t is not a variable, are true
         Note that, if t was a universally quantified variable, it would have been removed by swap.
      *)
  | (Neq(Var v, t)) ->
      elim_var_if_possible false keep_vars v;
      check_vars_occurs has_gen_var keep_vars t
  | c ->
      Display.Text.display_constra [c];
      Parsing_helper.internal_error "unexpected constraint in simplify_simple_constraint: t <> t', t not variable"

(*********************************************************
	functions for formula simplification. This section
	include the functions :
		- unify_disequation
		- elim_universal_variable
**********************************************************)

(** Unify_disequations *)

let rev_assoc2 keep_vars assoc_gen_var v =
  match rev_assoc v (!assoc_gen_var) with
    Var _ ->
      if List.mem v keep_vars then
	Var v
      else
	let v' = new_gen_var v.btype false in
	assoc_gen_var := (v', v) :: (!assoc_gen_var);
	FunApp(v', [])
  | x -> x


(** [make_disequation_from_unify] create the list of simple constraint
	corresponding to $\bigvee_j x_j \neq \sigma_k x_j$*)
let rec make_disequation_from_unify keep_vars assoc_gen_with_var = function
  | [] -> []
  | (var::l) ->
      let l' = make_disequation_from_unify keep_vars assoc_gen_with_var l in
      	match var.link with
	  | NoLink -> l'
	  | TLink _ ->
	      (Neq(rev_assoc2 keep_vars assoc_gen_with_var var, follow_link (rev_assoc2 keep_vars assoc_gen_with_var) (Var var))) :: l'
	  | _ -> internal_error "unexpected link in make_disequation_from_unify"

let rec close_disequation_eq restwork = function
  | [] -> restwork ()
  | Neq(t1,t2)::l ->
      begin
	try
	  unify_modulo (fun () ->
	    close_disequation_eq restwork l;
	    raise Unify) t1 t2
	    (* In fact, always terminates by raising Unify; never returns; cleanup() *)
	with
	  Unify -> cleanup ()
      end

let unify_disequation nextf accu constra =
  let assoc_gen_with_var = ref [] in (* Association list general var * var *)

  assert (!Terms.current_bound_vars == []);

  (* Get all classic variables *)

  let keep_vars = ref [] in
  List.iter (get_vars_constra keep_vars) constra;

  (* all general variable in [constra] are replaced by classic variables *)
  let constra' = List.map (function
    | Neq(t1,t2) -> Neq(replace_f_var assoc_gen_with_var t1, replace_f_var assoc_gen_with_var t2)
	  ) constra
  in
  let var_list = ref [] in
  List.iter (get_vars_constra var_list) constra';

  close_disequation_eq (fun () ->
    try
      let new_disequation = make_disequation_from_unify !keep_vars assoc_gen_with_var !var_list in
      cleanup ();
      accu := (nextf new_disequation) :: (!accu)
    with
    	TrueConstraint -> cleanup ()
  ) constra';

  assert (!Terms.current_bound_vars == [])

(** Elim_universal_variables *)

(** This function must be applied after [unify_disequation]. Indeed we assume that for
	any v \neq t in [constra], v only occur once in [constra].*)
let elim_universal_variable constra =

  let rec look_for_general_var constra_done = function
    | [] -> List.rev constra_done
    | Neq(FunApp(f,[]),_)::q when f.f_cat = General_mayfail_var ->
	look_for_general_var constra_done q
    | Neq(v1, FunApp(f,[]))::q when f.f_cat = General_mayfail_var ->
        let rep = function
	  | Neq(x, t) -> Neq(x, replace_name f v1 t)
	in

	let constra_done' = List.map rep constra_done
	and q' = List.map rep q in

	look_for_general_var constra_done' q'
    | Neq(Var v,_)::q when v.unfailing ->
	Parsing_helper.internal_error "May-fail variables forbidden in inequalities (1)"
    | Neq(_, Var v)::q when v.unfailing ->
	Parsing_helper.internal_error "May-fail variables forbidden in inequalities (2)"
    (* Given the previous cases, at this point, in Neq(t,t'), t and t' cannot
       fail: they cannot be General_mayfail_vars nor may-fail variables,
       and they cannot be the constant fail, because the unification of
       fail with the cases that remain (General_var, variable) fails. *)
    | Neq(FunApp(f,[]),_)::q when f.f_cat = General_var ->
	look_for_general_var constra_done q
    | Neq(Var(v) as v1,FunApp(f,[]))::q when f.f_cat = General_var ->
        let rep = function
	  | Neq(x, t) -> Neq(x, replace_name f v1 t)
	in

	let constra_done' = List.map rep constra_done
	and q' = List.map rep q in

	look_for_general_var constra_done' q'
    | t::q -> look_for_general_var (t::constra_done) q
  in
  look_for_general_var [] constra

(*** Combining the simplification ***)

let feed_new_constra keep_vars accu constra =
(* TO DO do not keep "syntactic" terms after unification modulo?
   let constra = remove_syntactic_constra constra in *)
  try
    let constra_has_gen_var = List.exists (function
    	| Neq(x,t) -> has_gen_var t) constra in
    List.iter (elim_var_notelsewhere constra_has_gen_var keep_vars) constra;
    let constrasimp = copy_constra3 constra in
    Terms.cleanup();
    if constrasimp = [] then
      raise FalseConstraint
    else if List.exists (fun a'' -> implies_constraint a'' constrasimp) (!accu) then
      ()
    else
      accu := constrasimp :: (List.filter (fun a'' -> not (implies_constraint constrasimp a'')) (!accu))
  with TrueConstraint ->
    Terms.cleanup()


(* Check that the current constraints are still satisfiable.
   Raise Unify when they are not. Returns the simplified constraints
   when they are.

   In the next function, Terms.auto_cleanup is useful because
   links may be stored in Terms.current_bound_vars when the function is called;
   these links must remain. *)

let check_constraint_list constra_list =
  Terms.auto_cleanup (fun _ ->
    let constra_list_1 = List.map Terms.copy_constra2 constra_list in
    Terms.cleanup();
    let accu = ref [] in
    List.iter (unify_disequation elim_universal_variable accu) constra_list_1;
    List.iter (function [] -> raise Terms.Unify |_ -> ()) !accu;
    !accu
  )

(* [simplify_constra_list_keepvars keep_vars constralist]
   simplifies the constraints [constralist] knowing that
   variables in [keep_vars] occur elsewhere, so they should be preserved.
   Raises FalseConstraint when the constraints are not satisfiable.

   In the next function, Terms.auto_cleanup is useful for two reasons:
   - links may be stored in Terms.current_bound_vars when the function is called;
   these links must remain.
   - during the function, exception FalseConstraint may be raised, with some
   links created during the function remaining; these links must be deleted
   before the function returns. *)

let simplify_constra_list_keepvars keep_vars constralist =
  Terms.auto_cleanup (fun () ->
    let accu = ref [] in
    List.iter (unify_disequation elim_universal_variable accu) constralist;
    let accu' = ref [] in
    List.iter (feed_new_constra keep_vars accu') (!accu);
    !accu'
  )

(* [simplify_constra_list rule constralist]
   simplifies the constraints [constralist] knowing that
   they occur in a clause containing the facts in the list [rule].
   Raises FalseConstraint when the constraints are not satisfiable. *)

let get_vars_facts l =
  let vars = ref [] in
  List.iter (Terms.get_vars_fact vars) l;
  !vars

let simplify_constra_list rule constralist =
  simplify_constra_list_keepvars (get_vars_facts rule) constralist

(* Implication between constraints

1/ copy the constraints to instantiate variables according to
   the substitution computed by matching conclusion and hypotheses.
   This uses copy_constra3

2/ simplify the obtained constraint, by simplify_constra_list

3/ test the implication, by implies_constra
   raise NoMatch if it fails

Notice that variables may not be cleaned up when this function is called.
*)

let implies_constra_list_keepvars keep_vars formula1 formula2 () =
  (* Apply the previous calculated substitution on [formula2] *)
  let formula2' = List.map copy_constra3 formula2 in
  (* We are assuming in this function that formula1 is already simplified
     so only formula2' need to be simplified *)
  try
    let formula2'' = simplify_constra_list_keepvars keep_vars formula2' in
    if not
	(List.for_all (fun c2elem ->
	  List.exists (fun c1elem -> implies_constraint c1elem c2elem) formula1
	    ) formula2'') then raise NoMatch
  with FalseConstraint ->
    raise NoMatch

let implies_constra_list rule formula1 formula2 () =
  implies_constra_list_keepvars (get_vars_facts rule) formula1 formula2 ()


(***** Close destructor rewrite rules under equations ******)


(* Subsumption between rewrite rules with side conditions *)

let implies_rew (leq1, req1, side_c1) (leq2, req2, side_c2) =
  assert (!current_bound_vars == []);
  try
    List.iter2 Terms.match_terms leq1 leq2;
    Terms.match_terms req1 req2;
    (* test side_c2 => \sigma side_c1
       where \sigma is obtained by the above matching.*)
    let vars = ref [] in
    List.iter (Terms.get_vars vars) leq2;
    Terms.get_vars vars req2;
    implies_constra_list_keepvars (!vars) side_c2 side_c1 ();
    Terms.cleanup();
    true
  with NoMatch ->
    Terms.cleanup();
    false

(* Convert from Neq form to pair form *)

let neq_to_pair = function
    [Neq(t1,t2)] -> (t1,t2)
  | l ->
      let l1 = List.map (fun (Neq(t,_)) -> t) l in
      let l2 = List.map (fun (Neq(_,t)) -> t) l in
      let tuple_fun = Terms.get_tuple_fun (List.map Terms.get_term_type l1) in
      (FunApp(tuple_fun, l1), FunApp(tuple_fun, l2))

(* Closure of destructors itself *)

let close_destr_eq f l =
  let results = ref [] in

  List.iter (fun (leq, req,side_c) ->
    close_term_list_eq (function
      | [] -> internal_error "should not be empty"
      |	(req'::leq') ->
	  let curr_bound_vars = !current_bound_vars in
	  current_bound_vars := [];

	  let (leq1,req1, side_c1) =
	    (List.map copy_term2 leq', copy_term2 req',
	     List.map (fun (t1,t2) -> [Neq(copy_term2 t1, copy_term2 t2)]) side_c)
	  in
	  cleanup();

	  (* Simplify the obtained constraints *)
	  begin
	    try
	      let vars = ref [] in
	      List.iter (Terms.get_vars vars) leq1;
	      Terms.get_vars vars req1;
	      let side_c1' = simplify_constra_list_keepvars (!vars) side_c1 in
	      let rew1 = (leq1, req1, side_c1') in

	      (* Eliminate redundant rewrite rules *)
	      if List.exists (fun rew2 ->
		implies_rew rew2 rew1) (!results) then ()
	      else
		results := rew1 :: (List.filter (fun rew2 ->
		  not(implies_rew rew1 rew2)) (!results));
	    with FalseConstraint -> ()
	  end;
	  current_bound_vars := curr_bound_vars
    ) (req::leq)
  ) l;

  (* Convert back from the Neq form to the pair form *)
  List.map (fun (leq, req, side_c) ->
    let var_list_rhs = ref [] in
    Terms.get_vars var_list_rhs req;
    List.iter (List.iter (Terms.get_vars_constra var_list_rhs)) side_c;
    if not (List.for_all (fun v -> List.exists (Terms.occurs_var v) leq) (!var_list_rhs)) then
      begin
	print_string ("Error in the definition of destructor " ^ f.f_name ^ " after taking into account equations:\nIncorrect rewrite rule: ");
	Display.Text.display_red f [leq, req, List.map neq_to_pair side_c];
	Parsing_helper.user_error "All variables of the right-hand side of a rewrite rule\nshould also occur in the left-hand side."
      end;

    (leq, req, List.map neq_to_pair side_c)
      ) !results

(* Record equations *)

let record_eqs horn_state =
  has_equations := (horn_state.h_equations != []);
  if hasEquations() then
    begin
      if !Param.html_output then
	begin
	  Display.LangHtml.openfile ((!Param.html_dir) ^ "/eq.html") "ProVerif: equations";
	  Display.Html.print_string "<H1>Equations</H1>\n"
	end;
      record_eqs_internal horn_state.h_equations;
      if !Param.html_output then
	begin
      	  Display.LangHtml.close();	
	  Display.Html.print_string "<A HREF=\"eq.html\">Equations</A><br>\n"
	end
    end

(* Record equations, also updating rewrite rules of destructors *)

let record_eqs_with_destr pi_state =
  has_equations := (pi_state.pi_equations != []);
  if hasEquations() then
    begin
      if !Param.html_output then
	begin
	  Display.LangHtml.openfile ((!Param.html_dir) ^ "/eq.html") "ProVerif: equations and destructors";
	  Display.Html.print_string "<H1>Equations</H1>\n"
	end;
      record_eqs_internal pi_state.pi_equations;

      if !Param.html_output then
	Display.Html.print_string "<H1>Completed destructors</H2>\n"
      else if !Param.verbose_destr then
	Display.Text.print_line "Completed destructors:";
      
      List.iter (fun f ->
	match f.f_cat with
	| Red red_rules ->
	    let red_rules' = close_destr_eq f red_rules in
	    if !Param.html_output then
	      (Display.Html.display_red f red_rules';Display.Html.print_string "<br>")
	    else if !Param.verbose_destr then
	      (Display.Text.display_red f red_rules';Display.Text.print_string "\n");
	    f.f_cat <- Red red_rules'
	| _ -> ()
	      ) pi_state.pi_funs;

      if !Param.html_output then
	begin
	  Display.LangHtml.close();
	  Display.Html.print_string "<A HREF=\"eq.html\">Equations & Destructors</A><br>\n"
	end
    end

(********* Simplifies a term using the equations ********)

exception Reduces

let simp_eq t =
  if not (!Param.simpeq_remove) then
    normal_form t
  else
    let rec find_red_term = function
	Var v -> ()
      | (FunApp(f,l)) as t ->
	  List.iter find_red_term l;
	  let rec find_red = function
              [] -> ()
	    | ((leq,req)::redl) ->
		try
		  if not (Terms.equal_types (Terms.get_term_type leq) (Terms.get_term_type t)) then
		    raise NoMatch;
		  Terms.match_terms leq t;
		  (*let r = copy_term3 req in*)
		  Terms.cleanup();
		  raise Reduces
		with NoMatch ->
		  Terms.cleanup();
		  find_red redl
	  in
	  find_red (!rewrite_system)
    in
    find_red_term t;
    t

(*
let simp_eq t =
  print_string "Simplifying ";
  Display.Text.display_term t;
  print_string " into ";
  let r = simp_eq t in
  Display.Text.display_term r;
  Display.Text.newline();
  r
*)
