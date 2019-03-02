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
open Terms

let secret_vars = ref []
let secret_vars_with_sets = ref []
let non_interference = ref false

let initialize = function
    Solve_Noninterf(secrets_with_sets) ->
     non_interference := true;
     secret_vars := List.map fst secrets_with_sets;
     secret_vars_with_sets := secrets_with_sets
  | _ ->
     non_interference := false;
     secret_vars := [];
     secret_vars_with_sets := []
                                
                           
let detect_atteq = function
    ([Pred(p1, [Var v1]); Pred(p2, [Var v2]); Pred({p_info = [TestUnifP _]}, [Var v1'; Var v2'])],
     (Pred(p4, [])), _, []) 
      when p1.p_prop land Param.pred_ATTACKER != 0
      && p2.p_prop land Param.pred_ATTACKER != 0
      && p4 == Param.bad_pred
      && v1 == v1'
      && v2 == v2' -> true
  | _ -> false
    

(****
   I. Check if the two parameters of testeq are unifiable for some value of x.
   If this is not true, the rule can be removed.

   If they are unifiable, we simplify the rule by replacing the testeq:
   fact with testeq:(x1,...,xn),(\sigma_u x1,...,\sigma_u xn)
   where \sigma_u is the most general unifier.
 ****)
let rec contains_bound_name fl = function
    Var v -> false
  | FunApp(f,l) -> (not (List.memq f fl)) &&
      ((match f.f_cat with 
	Name _ -> f.f_private 
      | _ -> false) || (List.exists (contains_bound_name fl) l))

let unify_up_to_x next_stage t1 t2 =
  let vlsecr = List.map (fun f -> (f,Terms.new_var f.f_name (snd f.f_type))) (!secret_vars) in
  let vl = ref vlsecr in
  assert (!current_bound_vars == []);
  let t1' = replace_f_var vl t1 in
  let t2' = replace_f_var vl t2 in
  let fl = List.map fst (!vl) in
  try 
    unify t1' t2';
    (* Remove the rule when the secret is bound to a term
       containing bound names.
       When "among (...)" is specified, the secret may be contain bound
       names. We could imagine other choices. The difficulty is to
       allow the user to specify a possibly infinite set of terms for
       the secret. *)
    let keep = List.for_all (fun (f,v) -> 
      match v.link with
	NoLink -> true
      | TLink t -> 
	  begin
	    let set = List.assq f (!secret_vars_with_sets) in
	    match set with
	      None ->
		let valx = follow_link (fun v2 -> rev_assoc v2 (!vl)) t in
		not (contains_bound_name fl valx)
	    | Some _ -> true
	  end
      | _ -> Parsing_helper.internal_error "unexpected link in unify_up_to_x") vlsecr
    in
    if not keep then
      cleanup() 
    else
      let t1simp = List.map (fun v2 -> rev_assoc v2 (!vl)) (!current_bound_vars) in
      let t2simp = List.map (fun v2 -> follow_link (fun v2 -> rev_assoc v2 (!vl)) (Var v2)) (!current_bound_vars) in
      cleanup();
      next_stage t1simp t2simp
  with Unify -> 
    (* The terms are never unifiable, so this rule cannot
       cause a breach of non-interference. *)
    cleanup()

(* II. Swap pairs (variable, secret), (variable, general variable),
   (secret, general variable). Eliminate pairs (general variable, _) *)

let rec swap t1done t2done t1remain t2remain = 
  match (t1remain,t2remain) with
    [],[] -> 
      (List.rev t1done, List.rev t2done)
  | (FunApp(f1,[]) :: l1),(a2::l2) 
	when f1.f_cat = General_mayfail_var ->
	  swap t1done t2done l1 l2
  | (a1::l1),(FunApp(f,[])::l2) 
	when f.f_cat = General_mayfail_var -> 
	  let rep = replace_name f a1 in
	  let t2done' = List.map rep t2done in
	  let l2' = List.map rep l2 in
	  swap t1done t2done' l1 l2'
  | (FunApp(f1,[]) :: l1),(a2::l2) 
	when f1.f_cat = General_var ->
	  (* Here a2 cannot be a may-fail variable, because
	     in this unification links the may-fail variable
	     to the general message variable, thus the pair
	     is ordered (may-fail variable, general variable) *)
	  swap t1done t2done l1 l2
  | ((Var v)::l1),(FunApp(f,[])::l2) 
	when f.f_cat = General_var && v.unfailing -> 
	  (* When we have a pair (v = may-fail variable, genx = general variable),
	     replace v with a message variable, since it cannot be fail, because
	     genx cannot be fail. *)
	  let v' = Var (Terms.new_var v.sname v.btype) in
	  Terms.link v (TLink v');
	  let rep = replace_name f v' in
	  let t2done' = List.map rep t2done in
	  let l2' = List.map rep l2 in
	  swap t1done t2done' l1 l2'
  | (a1::l1),(FunApp(f,[])::l2) 
	when f.f_cat = General_var -> 
	  let rep = replace_name f a1 in
	  let t2done' = List.map rep t2done in
	  let l2' = List.map rep l2 in
	  swap t1done t2done' l1 l2'
  | ((Var v as a1)::l1),((FunApp(f,[]) as a2)::l2) 
	when List.memq f (!secret_vars) -> 
	  let rep = replace_name f a1 in
	  let t2done' = List.map rep t2done in
	  let l2' = List.map rep l2 in
	  swap (a2 :: t1done) (a1 :: t2done') l1 l2'
  | (a1::l1),(a2::l2) ->
      swap (a1::t1done) (a2::t2done) l1 l2
  | _ -> Parsing_helper.internal_error "Lists of different lengths in swap"

let swap_with_copy next_stage hypbefore hypafter concl hist constra l1 l2 =
  assert (!Terms.current_bound_vars == []);
  let l1', l2' = swap [] [] l1 l2 in
  let hypbefore' = List.map Terms.copy_fact3 hypbefore in
  let hypafter' = List.map Terms.copy_fact3 hypafter in
  let concl' = Terms.copy_fact3 concl in
  let constra' = List.map Terms.copy_constra3 constra in
  Terms.cleanup();
  next_stage hypbefore' hypafter' concl' hist constra' l1' l2'

(**** 
   III. If all bindings of testunif are of the form x,M
   where x a secret, and all hypotheses are attacker(x_i),
   then the testunif fact is true for some x_i.
 ****)
   
(* Rebuilds the standard rule format from an exploded rule format
   hypbefore hypafter concl hist constra t1simp t2simp, 
   where t1simp, t2simp are lists of terms *)

let dec_out_rule next_stage hypbefore hypafter concl hist constra t1simp t2simp =
  match (t1simp,t2simp) with 
    [],[] -> ()
  | [t1s],[t2s] ->
      let hypbefore' = (Pred(Param.get_pred (TestUnifP(Terms.get_term_type t1s)), [t1s; t2s])) :: hypbefore in
      next_stage hypbefore' hypafter concl hist constra
  | _ ->
      let tuple_fun = get_tuple_fun (List.map Terms.get_term_type t1simp) in
      let hypbefore' = (Pred(Param.get_pred (TestUnifP(Param.bitstring_type)), 
			     [ FunApp(tuple_fun, t1simp); 
			       FunApp(tuple_fun, t2simp)])) :: hypbefore
      in
      next_stage hypbefore' hypafter concl hist constra

let check_any_x = function 
    Pred(chann,[Var v]) -> chann.p_prop land Param.pred_ANY != 0
  | _ -> false

let secr_in_sets next_stage hypbefore hypafter concl hist constra t1 t2 =

let rec unify_secrets todo = function
    [] -> 
      if todo != [] then unify_secrets [] todo else 
      let curr_bound_vars = !current_bound_vars in
      current_bound_vars := [];
      let hypbefore' = List.map Terms.copy_fact2 hypbefore in
      let hypafter' = List.map Terms.copy_fact2 hypafter in
      let concl' = Terms.copy_fact2 concl in
      let constra' = List.map Terms.copy_constra2 constra in
      cleanup();
      next_stage hypbefore' hypafter' concl' hist constra';
      current_bound_vars := curr_bound_vars
  | ((f,v)::l) ->
      let set = List.assq f (!secret_vars_with_sets) in
      match set with
	None -> unify_secrets todo l
      | Some s -> 
	  match follow_link (fun v2 -> rev_assoc v2 (todo @ l)) (Var v) with
	    Var _ when l != [] -> unify_secrets ((f,v)::todo) l
	  | _ -> 
	      let rec unifyinset = function
		  [] -> ()
		| (au::lu) -> 
		    let curr_bound_vars = !current_bound_vars in
		    current_bound_vars := [];
		    begin
		      try
			unify (Var v) au;
			unify_secrets todo l
		      with Unify ->
			()
		    end;
		    cleanup();
		    current_bound_vars := curr_bound_vars;
		    unifyinset lu
	      in
	      unifyinset s 

in

  let vlsecr = List.map (fun f -> (f,Terms.new_var f.f_name (snd f.f_type))) (!secret_vars) in
  let vl = ref vlsecr in
  assert (!current_bound_vars == []);
  let t1' = List.map (replace_f_var vl) t1 in
  let t2' = List.map (replace_f_var vl) t2 in
  try 
    List.iter2 unify t1' t2';
    unify_secrets [] vlsecr;
    cleanup()
  with Unify -> 
    Parsing_helper.internal_error "Here, the terms should be unifiable"



let check_testunif_true next_stage hypbefore hypafter concl hist constra l1 l2 =
  if (List.for_all check_any_x hypbefore)
      && (List.for_all check_any_x hypafter)
      && (l1 != [])
      && (List.for_all (function
          FunApp(f2,[]) -> List.memq f2 (!secret_vars)
	| _ -> false) l1) then
    begin
      (*
     dec_out_rule (fun hypbefore hypafter concl hist constra ->
       Display.Text.display_rule (List.rev_append hypbefore hypafter, concl, hist, constra)) hypbefore hypafter concl hist constra l1 l2;
      *)
     (* Testunif true *)
     let hist' = TestUnifTrue(List.length hypbefore, hist) in
     secr_in_sets next_stage hypbefore hypafter concl hist' constra l1 l2
    end
   else
     (* Keep the rule *)
     dec_out_rule next_stage hypbefore hypafter concl hist constra l1 l2

(****

IV. Instantiation and elimination of useless variables.

A clause
 R = att(x) /\ H /\ testunif((..., x, ...), (..., f(M1, ..., Mn), ...)) -> bad
becomes
 R { f(x1, ..., xn) / x }
when f constructor or name function symbol (not a secret or general variable)
     H contains only unselectable facts, 
and repeat the whole simplification.

A clause 
 R = att(x1) /\ att(x2) /\ H /\ testunif((..., x1, ...), (..., x2, ...)) -> bad
becomes
 R { x2/x1 }
plus eliminate the pair x2,x2 in testunif, and eliminate
duplicate hypotheses. Later useless facts att(x) will be removed.
(This cannot be applied to the clause 
          att(x1) /\ att(x2) /\ testeq(x1,x2) -> bad
)
 ****)

let is_bad = function
    Pred(p, []) -> p==Param.bad_pred
  | _ -> false

let is_att_x x = function
    Pred(p, [Var v]) when (p.p_prop land Param.pred_ATTACKER != 0) && (x == v) -> true
  | _ -> false

let do_instantiate (_,set) = 
  (match set with
    None -> false
  | Some l -> true)

let inst_elim next_stage repeat_next_stage hypbefore hypafter concl hist constra l1 l2 =
   if not (is_bad concl) then
     next_stage hypbefore hypafter concl hist constra l1 l2
   else
   let redo_all_optim = ref false in
   let contains_att_x x = (List.exists (is_att_x x) hypbefore)
     || (List.exists (is_att_x x) hypafter) in
   let has_selectable () = not ((List.for_all is_unselectable hypbefore)
      && (List.for_all is_unselectable hypafter)) in
   let redo_optim() =
       let hypbefore' = List.map Terms.copy_fact2 hypbefore in
       let hypafter' = List.map Terms.copy_fact2 hypafter in
       let concl' = Terms.copy_fact2 concl in
       let constra' = List.map Terms.copy_constra2 constra in
       let l1' = List.map Terms.copy_term2 l1 in
       let l2' = List.map Terms.copy_term2 l2 in
       Terms.cleanup();
       dec_out_rule (fun hypbefore hypafter concl hist constra -> 
	 repeat_next_stage ((List.rev_append hypbefore hypafter), concl, hist, constra))
	 hypbefore' hypafter' concl' hist constra' l1' l2'
   in
   assert (!Terms.current_bound_vars == []);
   List.iter2 (fun l1 l2 -> 
     match (l1,l2) with
       (Var v1), (FunApp(f,l)) 
	 when (contains_att_x v1)
         (* && not ((List.memq f (!secret_vars)) ||
                    f.f_cat = General_var *)
       ->
	 if List.exists do_instantiate (!secret_vars_with_sets) then
	   begin
	     (* Multiple instantiation is costly. 
	        Do it only when necessary, that is,
	        when there is otherwise no selectable hypothesis *)
	     if has_selectable() then () else
	     begin
	       List.iter (fun ((s,_) as descr) ->
		 if (do_instantiate descr) &&
		   (Terms.equal_types (snd s.f_type) v1.btype)
		 then
		   let curr_bound_vars = !Terms.current_bound_vars in
		   Terms.current_bound_vars := [];
		   Terms.link v1 (TLink (FunApp(s,[])));
		   redo_optim();
		   Terms.current_bound_vars := curr_bound_vars
			  ) (!secret_vars_with_sets);
	       let lvar = Terms.var_gen (List.map Terms.get_term_type l) in
	       Terms.link v1 (TLink (FunApp(f, lvar)));
	       redo_all_optim := true
	     end
	   end
	 else
	   begin
	     let lvar = Terms.var_gen (List.map Terms.get_term_type l) in
	     Terms.link v1 (TLink (FunApp(f, lvar)));
	     redo_all_optim := true
	   end
     | (Var v1), (Var v2) 
	 when (contains_att_x v1) && (contains_att_x v2) &&
              v2.unfailing && not v1.unfailing ->
	   (* when v2 may fail and v1 cannot be fail, we can link
	      only in the direction that v2 is set to v1. *)
	   Terms.link v2 (TLink (Var v1));
	   redo_all_optim := true
     | (Var v1), (Var v2) 
	 when (contains_att_x v1) && (contains_att_x v2) ->
	   Terms.link v1 (TLink (Var v2));
	   redo_all_optim := true
     | _, _ -> ()) l1 l2;
   if (!redo_all_optim) then
     redo_optim()
   else
     next_stage hypbefore hypafter concl hist constra l1 l2

(****
  Check that the values of the secrets can be given inside the
  specified sets 
 ****)

let rec unify_secrets todo = function
    [] -> if todo != [] then unify_secrets [] todo
  | ((f,v)::l) ->
      let set = List.assq f (!secret_vars_with_sets) in
      match set with
	None -> unify_secrets todo l
      | Some s -> 
	  match follow_link (fun v2 -> rev_assoc v2 (todo @ l)) (Var v) with
	    Var _ when l != [] -> unify_secrets ((f,v)::todo) l
	  | _ -> 
	      let rec unifyinset = function
		  [] -> raise Unify
		| (au::lu) -> 
		    let curr_bound_vars = !current_bound_vars in
		    current_bound_vars := [];
		    try
		      unify (Var v) au;
		      unify_secrets todo l;
		      cleanup();
		      current_bound_vars := curr_bound_vars
		    with Unify ->
		      cleanup();
		      current_bound_vars := curr_bound_vars;
		      unifyinset lu
	      in
	      unifyinset s 

let secr_in_sets t1 t2 =
  let vlsecr = List.map (fun f -> (f,Terms.new_var f.f_name (snd f.f_type))) (!secret_vars) in
  let vl = ref vlsecr in
  assert (!current_bound_vars == []);
  let t1' = List.map (replace_f_var vl) t1 in
  let t2' = List.map (replace_f_var vl) t2 in
  try 
    List.iter2 unify t1' t2';
    unify_secrets [] vlsecr;
    cleanup();
    true
  with Unify -> 
    (* The terms are never unifiable, so this rule cannot
       cause a breach of non-interference. *)
    cleanup();
    false


let check_sets next_stage hypbefore hypafter concl hist constra l1 l2 =
  if secr_in_sets l1 l2 then
  next_stage hypbefore hypafter concl hist constra l1 l2


(****
   V. Combine all the simplifications together
 ****)

let simplify next_stage repeat_next_stage ((hyp, concl, hist, constra) as r) = 
  if (not (!non_interference)) || (detect_atteq r) then
    next_stage r
  else
    let rec simplify_testunif hypbefore hypafter concl hist constra =
      match hypafter with
	[] -> next_stage ((List.rev hypbefore), concl, hist, constra)
      |	(a::l) ->
	  match a with
	    Pred({p_info = [TestUnifP _]},[t1;t2]) ->
	(* In the intermediate simplification steps, the rule is in format
	   hypbefore hypafter concl hist constra t1 t2. 
	   At the beginning, t1 t2 are terms;
	   after unify_up_to_x, they are lists of terms. 
	   dec_out_rule rebuilds the standard rule format.
	      print_string "Simplifying ";
	      Display.Text.display_rule r; *)
	      unify_up_to_x (swap_with_copy (inst_elim (check_sets (check_testunif_true simplify_testunif)) repeat_next_stage) hypbefore l concl hist constra) t1 t2
	  | _ -> simplify_testunif (a::hypbefore) l concl hist constra
    in
    simplify_testunif [] hyp concl hist constra



(* Selection function: called when the standard selection function says 
   to select the conclusion *)  
   
let selfun ((hyp, concl, _, _) as r) = 
  if not ((!non_interference) && (is_bad concl) && (hyp != [])) then -1 else
  if detect_atteq r then 0 else
  begin
    print_string "Warning: selection not found in Noninterf.selfun in rule\n";
    Display.Text.display_rule r;
   -1
  end
