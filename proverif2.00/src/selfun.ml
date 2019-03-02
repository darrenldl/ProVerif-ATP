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
open Terms

let never_select_weight = -10000
let match_concl_weight = -7000
let default_add_no_unif_weight = -5000
let default_user_no_unif_weight = -6000
let dummy_weight = -4000

let no_unif_set = ref ([] : (fact_format * int) list)
let inst_constraints = ref false

let initialize v_no_unif_set solver_kind =
  no_unif_set := List.map (fun (f,n) ->
    let n =
      if n >= 0 then default_user_no_unif_weight else 
        if n <= never_select_weight then never_select_weight+1 else
          n
    in
(*
  if !Param.verbose_term then
    begin
      print_string "nounif "; 
      Display.Text.display_fact_format f; 
      print_string ("/" ^ (string_of_int n));
      Display.Text.newline()
    end;
*)
    (f,n)) v_no_unif_set;
  match solver_kind with
    Solve_Equivalence
  | Solve_WeakSecret _ ->
     inst_constraints := true
  | _ ->
     inst_constraints := false
    
let rec has_same_format_term t1 t2 =
   match (t1,t2) with
   | (FunApp(f1,l1), FFunApp(f2,l2)) ->
        (f1 == f2) && (List.for_all2 has_same_format_term l1 l2)
   | (Var _, FVar v2) | (_, FAny v2) -> 
       begin
	 match v2.link with
	   NoLink -> 
	     begin
	       if v2.unfailing then 
		 begin
		   Terms.link v2 (TLink t1);
		   true
		 end
	       else
		 (* v2 is a message variable; the matching works only if t1 is a message *)
		 match t1 with
		   Var v' when v'.unfailing -> false
		 | FunApp(f,[]) when f.f_cat = Failure -> false
		 | _ -> Terms.link v2 (TLink t1); true
	     end
	 | TLink t1' -> Terms.equal_terms t1 t1'
	 | _ -> Parsing_helper.internal_error "unexpected link in has_same_format_term"
       end
   | (_,_) -> false

let has_same_format (c1, p1) (c2, p2) =
  (c1 == c2) && (auto_cleanup (fun () -> List.for_all2 has_same_format_term p1 p2))

let rec find_same_format f = function
    [] -> 0
  | ((a,n)::l) -> if has_same_format f a then n else find_same_format f l

(* Remark: format_equal could be a bit less strict. When a variable
   is marked at least once "FVar", it has the same meaning as if it
   is always marked "FVar". *)

let rec format_equal t1 t2 =
   match (t1,t2) with
   | (FFunApp(f1,l1), FFunApp(f2,l2)) ->
        (f1 == f2) && (List.for_all2 format_equal l1 l2)
   | (FVar v1, FVar v2) | (FAny v1, FAny v2) -> 
       begin
	 (v1.unfailing == v2.unfailing) &&
	 (match v2.link with
	   NoLink -> Terms.link v2 (VLink v1); true
	 | VLink v1' -> v1 == v1'
	 | _ -> Parsing_helper.internal_error "unexpected link in format_equal")
       end
   | (_,_) -> false

let format_equal_fact (c1, p1) ((c2, p2),_) =
  (c1 == c2) && (auto_cleanup (fun () -> List.for_all2 format_equal p1 p2))

let rec compute_match_format t1 t2 =
   match (t1,t2) with
   | (Var v1), (Var v2) -> FAny v1
   | (Var v1), _ -> FVar v1
   | (FunApp (f1,l1')), (FunApp (f2,l2')) ->
       if f1 != f2 then 
	 internal_error "terms do not match 3";
       FFunApp(f1,List.map2 compute_match_format l1' l2')
   | _,_ -> internal_error "terms do not match 4"

let compute_match_format_fact f1 f2 = match (f1,f2) with
  Pred(c1, p1), Pred(c2, p2) ->
    if c1 != c2 then
      internal_error "facts do not match";
    (c1, List.map2 compute_match_format p1 p2)
| _ -> internal_error "match format should be called only with Pred facts, since these facts should appear in conclusions"

(* selection_fun rule returns -1 if no fact is selected in rule, and
   the index of the selected hypothesis otherwise  (0 corresponds to 
   the first hypothesis) 
*)

(* Standard, equivalent to the old version without selection function *)

let term_warning ((hyp, concl, _, _) as rule) =
  if (!Param.max_depth) < 0 then
    begin
      if (!Param.should_stop_term) || (!Param.verbose_term) then
	begin
	  print_string "The following rule unifies with itself\n";
	  Display.Text.display_rule rule;
	  print_string "The completion process will probably not terminate\n"
	end;
      if !Param.should_stop_term then
	begin
	  print_string "You have several solutions to guarantee termination:\n";
	  print_string " - limit the depth of terms with param maxDepth = <depth>.\n";
	  print_string " - add one of the unifying facts of this rule to the set\n";
	  print_string "   of facts on which unification is forbidden, with nounif <fact>.\n";
	  print_string " - add a rule that is more general than all rules generated by the\n";
	  print_string "   unifications of the above rule. (Maybe you have already done that, and I\n";
	  print_string "   did not detect it. If so, ignore this message by pressing [return].)\n";
	  print_string "Press [return] to continue, [ctrl-c] to stop\n";
	  Param.should_stop_term := false;
	  ignore(read_line())
	end
    end

let selection_fun_nounifset ((hyp, concl, _, _) as rule) = 
  let rec sel (nold, wold) n = function 
      [] -> 
        if (nold >= 0) && (matchafactstrict concl (List.nth hyp nold)) then
	  term_warning(rule);
        nold
    | (f::l) when is_unselectable f ->
	  (* Guarantee that p(x) is never selected when we decompose data
	     constructors on p, except that we can select the conclusion when
	     all hypotheses and the conclusion are of the form p(x) for
	     such p. This is important for the soundness of 
	     the decomposition of data constructors. *)
        sel (nold, wold) (n+1) l
    | (Pred(p,lp) as h::l) ->
	let wnew = find_same_format (p,lp) (!no_unif_set) in
	if wnew < 0 then
	  if wnew > wold
 	  then sel (n,wnew) (n+1) l 
          else sel (nold, wold) (n+1) l
	else
	  begin
	    if matchafactstrict concl h then term_warning(rule);
	    n
	  end
    | _ -> Parsing_helper.internal_error "Selfun(1): added to avoid warning for non-exhaustive pattern-matching"
  in 
  if is_unselectable concl then
    (* The conclusion is never selected if an hypothesis can be *)
    sel (-1, never_select_weight) 0 hyp
  else
    (* The conclusion can be selected if we don't find better in
       the hypothesis *)
    sel (-1, -1) 0 hyp

(* Very good for skeme, but slightly slower for some other protocols *)

let selection_fun_nounifset_maxsize ((hyp, concl, _, _) as rule) = 
  let rec sel (nold, wold) n = function 
      [] -> 
	if (nold >= 0) && (matchafactstrict concl (List.nth hyp nold)) then
	  term_warning(rule);
	nold
    | (f::l) when is_unselectable f ->
	  (* Guarantee that p(x) is never selected when we decompose data
	     constructors on p, except that we can select the conclusion when
	     all hypotheses and the conclusion are of the form p(x) for
	     such p. This is important for the soundness of 
	     the decomposition of data constructors. *)
        sel (nold, wold) (n+1) l
    | (Pred(p,lp) as h::l) -> 
	let wtmp = find_same_format (p,lp) (!no_unif_set) in
        let wnew = 
	  if wtmp < 0
	  then wtmp 
	  else fact_size h 
	in
        if wnew > wold 
	then sel (n,wnew) (n+1) l 
        else sel (nold, wold) (n+1) l
    | _ -> Parsing_helper.internal_error "Selfun(2): added to avoid warning for non-exhaustive pattern-matching"
  in 
  if is_unselectable concl then
    (* The conclusion is never selected if an hypothesis can be *)
    sel (-1, never_select_weight) 0 hyp
  else
    (* The conclusion can be selected if we don't find better in
       the hypothesis *)
    sel (-1, -1) 0 hyp

(* Very good for termination - even if it does not solve all cases, of course *)

let selection_fun_weight ((hyp, concl, _, _) as rule) =
  let rec sel (nold, wold) n = function
      [] -> 
	if nold = -1 then (* conclusion selected *)
	  begin
	    List.iter (function h ->
	      if matchafactstrict concl h then
		begin
		  let format = compute_match_format_fact h concl in
		  if not (List.exists (format_equal_fact format) (!no_unif_set)) then
		    begin
		      no_unif_set := (format, default_add_no_unif_weight) :: !no_unif_set;
		      if !Param.verbose_term then
			begin
			  print_string "nounif "; 
			  Display.Text.display_fact_format format; 
			  print_string ("/" ^ (string_of_int default_add_no_unif_weight));
			  Display.Text.newline()
			end
		    end
		end) hyp
	  end;
        if (!Param.verbose_term) && (((wold < 0) && (nold >= 0)) (* || (wold < -1) *) ) then
	  begin
	    print_string "Termination warning: ";
	    Display.Text.display_rule rule;
	    print_string ("Selecting " ^ (string_of_int nold));
	    Display.Text.newline()
	  end;
        nold
    | (f::l) when is_unselectable f ->
	  (* Guarantee that p(x) is never selected when we decompose data
	     constructors on p. This is important for the soundness of 
	     the decomposition of data constructors. *)
        sel (nold, wold) (n+1) l
    | (Pred(p,lp) as h::l) -> 
	let wnew =
	  if matchafactstrict concl h then match_concl_weight else 
	  let wtmp = find_same_format (p,lp) (!no_unif_set) in
	  if wtmp < 0 then wtmp else
	  if !Param.select_fun == Param.TermMaxsize then fact_size h else 0
	in
        if wnew > wold 
	then sel (n,wnew) (n+1) l 
        else sel (nold, wold) (n+1) l
    | _ -> Parsing_helper.internal_error "Selfun(3): added to avoid warning for non-exhaustive pattern-matching"
  in 
  let wconcl = 
    if is_unselectable concl then
      (* The conclusion is never selected if an hypothesis can be *)
      never_select_weight
    else
      match concl with
	Pred(p, []) when p == Param.dummy_pred -> dummy_weight
      |	_ ->
          (* The conclusion can be selected if we don't find better in
	     the hypothesis *)
	  if List.exists (fun h -> matchafactstrict h concl) hyp then match_concl_weight else -1
  in
  sel (-1, wconcl) 0 hyp

(* Avoid creating cycles when instantiating in inst_constra:
   renames all variables to unused ones. *)
let rec false_copy = function
    Var v -> Terms.new_var_def v.btype
  | FunApp(f,l) -> FunApp(f, List.map false_copy l)

let inst_constra = function
    Neq(Var v,t) -> 
      if v.link = NoLink then 
	Terms.link v (TLink (false_copy t))
  | _ -> ()

let selection_fun ((hyp,concl,hist,constra) as rule) =
  let r = 
   match !Param.select_fun with
     Param.NounifsetMaxsize -> selection_fun_nounifset_maxsize rule
   | Param.Term | Param.TermMaxsize -> selection_fun_weight rule
   | Param.Nounifset -> selection_fun_nounifset rule
  in
  let r =
    (* For proofs of equivalences (!inst_constraints = true),
       if the conclusion is selected (r = -1) and it is unselectable,
       that is, it is of the form such as bad: or attacker:x,x',
       then we try to find a better selection by selecting an hypothesis
       attacker:x,x' in which x (or x') occurs in an inequality x <> M. *)
    if (r = -1) && (!inst_constraints) && (is_unselectable concl) then
      begin
	List.iter (List.iter inst_constra) constra;
	let rule2 = (List.map copy_fact2 hyp, copy_fact2 concl, hist, List.map copy_constra2 constra) in
	Terms.cleanup();
	match !Param.select_fun with
	  Param.NounifsetMaxsize -> selection_fun_nounifset_maxsize rule2
	| Param.Term | Param.TermMaxsize -> selection_fun_weight rule2
	| Param.Nounifset -> selection_fun_nounifset rule2
      end
    else r
  in
  let r =
    if r = -1 then Noninterf.selfun rule else r
  in
  if r = -1 then Weaksecr.selfun rule else r

let guess_no_unif rulequeue =
  (* If no "nounif" instruction is given, first guess them by "selection_fun_weight" *)
  if (!no_unif_set = []) || (!Param.select_fun == Param.Term)
      || (!Param.select_fun == Param.TermMaxsize) then
    Pvqueue.iter rulequeue (fun r -> ignore (selection_fun_weight r));
