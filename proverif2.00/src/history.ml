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
open Parsing_helper
open Terms

exception HistoryUnifyError

(* add a rule and return its history *)

let rule_hash = Hashtbl.create 7

let change_type_attacker p t =
  match p.p_info with
    [Attacker(n,_)] -> Param.get_pred (Attacker(n,t))
  | [AttackerBin(n,_)] -> Param.get_pred (AttackerBin(n,t))
  | [AttackerGuess _] -> Param.get_pred (AttackerGuess(t))
  | [Compromise _] -> Param.get_pred (Compromise(t))
  | [PolymPred(s,i,tl)] -> Param.get_pred (PolymPred(s,i,Terms.copy_n (List.length tl) t))
  | [] -> 
      if !Param.typed_frontend then
	Parsing_helper.internal_error "Non-polymorphic user-defined predicates should not be declared data in the typed front-end"
      else
	p
  | _ -> Parsing_helper.internal_error "Unexpected predicate in change_type_attacker"

let get_rule_hist descr =
  try
    Hashtbl.find rule_hash descr
  with Not_found ->
    let (hyp,concl,constra,hdescr) = 
      match descr with
        RElem(preds, ({ p_type = [t1;t2] } as p)) ->
	  let v = Terms.new_var_def t1 in
	  let v' = Terms.new_var_def t2 in
	  (List.map (fun p' -> Pred(change_type_attacker p' t1, [v])) preds, 
	   Pred(p, [v;v']), 
	   [], Elem(preds,p))
      | RApplyFunc(f,p) ->
	  let rec gen_vars n =
	    if n = 0 then
	      [] 
	    else
	      (FunApp(f, Terms.var_gen (fst f.f_type))) :: (gen_vars (n-1))
	  in
	  let concl = gen_vars (List.length p.p_type) in
	  let hypl = reorganize_fun_app f concl in
	  (List.map (fun h -> Pred((change_type_attacker p (Terms.get_term_type (List.hd h))), h)) hypl, 
	   Pred((change_type_attacker p (Terms.get_term_type (List.hd concl))), concl), [],
	   Apply(f,p))
      | RApplyProj(f,nproj,p) ->
	  let rec gen_vars n =
	    if n = 0 then
	      [] 
	    else
	      (FunApp(f, Terms.var_gen (fst f.f_type))) :: (gen_vars (n-1))
	  in
	  let hyp = gen_vars (List.length p.p_type) in
	  let concl = List.nth (reorganize_fun_app f hyp) nproj in
	  ([Pred((change_type_attacker p (Terms.get_term_type (List.hd hyp))),hyp)], 
	   Pred((change_type_attacker p (Terms.get_term_type (List.hd concl))), concl), [],
	   Apply(Terms.projection_fun(f,nproj+1), p))
      |	_ -> 
	  internal_error "unsupported get_rule_hist"
    in
    let hist = Rule(-1, hdescr, hyp, concl, constra) in
    Hashtbl.add rule_hash descr hist;
    hist

(* History simplification *)

(* We use a hash table that associates to each fact all trees that
   derive it. To avoid recomputing hashes, we store them together with
   the considered fact. *)

module HashFact =
  struct

    type t = 
	{ hash : int;
	  fact : fact }

    let equal a b = Termslinks.equal_facts_with_links a.fact b.fact

    type skel_term =
	SVar of int
      |	SFun of string * skel_term list

    type skel_fact =
	SPred of string * skel_term list
      |	SOut of skel_term

    let rec skeleton_term = function
	Var b -> 
	  begin
	    match b.link with
	      TLink t -> skeleton_term t
	    | NoLink -> SVar(b.vname)
	    | _ -> Parsing_helper.internal_error "unexpected link in skeleton_term"
	  end
      |	FunApp(f,l) -> 
	  match f.f_cat with
	    Name _ -> SFun(f.f_name,[])
	  | _ -> SFun(f.f_name, List.map skeleton_term l)

    let skeleton_fact = function
	Pred(p,l) -> SPred(p.p_name, List.map skeleton_term l)
      |	Out(t,_) -> SOut(skeleton_term t)

    let hash a = a.hash

    (* build a HashFact.t from a fact *)

    let build f = { hash = Hashtbl.hash(skeleton_fact f);
		    fact = f }

  end

module TreeHashtbl = Hashtbl.Make(HashFact)

let tree_hashtbl = TreeHashtbl.create 7

let seen_fact hf =
  if !Param.simplify_derivation_level = Param.AllFacts then
    TreeHashtbl.find tree_hashtbl hf
  else
  match hf.HashFact.fact with
    Pred(p,_) when p.p_prop land Param.pred_ATTACKER != 0 ->
      TreeHashtbl.find tree_hashtbl hf
  | _ -> raise Not_found 
               (* Remove proofs of the same fact only for attacker facts,
                  several proofs of the same fact may be useful for attack
		  reconstruction for other facts: for mess facts, in particular
		  several outputs of the same message on the same channel
		  may be needed for private channels. *)

let rec unroll_rwp t =
  match t.desc with 
    FRemovedWithProof t' -> unroll_rwp t'
  | _ -> t

let equal_son t t' =
  unroll_rwp t == unroll_rwp t'

let seen_tree hf t =
  if !Param.simplify_derivation_level != Param.AttackerSameTree then
    begin
      TreeHashtbl.add tree_hashtbl hf t;
      t
    end
  else
    match t.thefact with
      Pred(p,_) when p.p_prop land Param.pred_ATTACKER != 0 -> 
          (* If t was already proved, it would have been removed by seen_fact when it
	     concludes an attacker fact *)
	TreeHashtbl.add tree_hashtbl hf t;
	t
    | _ ->
	try
	  let r = TreeHashtbl.find_all tree_hashtbl hf in
	  let t' =
	    List.find (fun t' ->
	      (match t.desc, t'.desc with
		FHAny, FHAny -> true
	      | FEmpty, FEmpty -> true
	      | FRule(n, tags, constra, sons), FRule(n', tags', constra', sons') ->
		  (n == n') && (Termslinks.equal_tags tags tags') && (Termslinks.equal_constra constra constra') &&
		  (List.length sons == List.length sons') && (List.for_all2 equal_son sons sons')
	      | FEquation son, FEquation son' ->
		  equal_son son son'
	      | FRemovedWithProof _, _ -> internal_error "Unexpected FRemovedWithProof"
	      | _ -> false)
		) r
	  in
	  { t with desc = FRemovedWithProof t' }
        with Not_found ->
	  TreeHashtbl.add tree_hashtbl hf t;
	  t

let rec simplify_tree t =
  let hf = HashFact.build t.thefact in
  match t.desc with
    FRemovedWithProof t' -> 
      begin
	try
	  { t with desc = FRemovedWithProof (TreeHashtbl.find tree_hashtbl hf) }
	with Not_found ->
	  simplify_tree t'
      end
  | FHAny | FEmpty ->
      begin
	try   
	  { t with desc = FRemovedWithProof (seen_fact hf) }
        with Not_found ->
	  seen_tree hf t
      end
  | FRule(n, tags, constra, sons) -> 
      begin
	try   
	  { t with desc = FRemovedWithProof (seen_fact hf) }
        with Not_found ->
	  let sons' = List.rev_map simplify_tree (List.rev sons) in
	  seen_tree hf { t with desc = FRule(n, tags, constra, sons') } 
      end
  | FEquation son -> 
      begin
	try   
	  { t with desc = FRemovedWithProof (seen_fact hf) }
        with Not_found ->
	  let son' = simplify_tree son in
	  seen_tree hf { t with desc = FEquation son' }
      end

(* Find hypothesis number n in the history tree *)

type res = FindSuccess of fact_tree
         | FindFailure of int

let rec get_desc_rec t n = 
  match t.desc with
    FEmpty -> if n = 0 then FindSuccess(t) else FindFailure(n-1)
  | FHAny -> FindFailure(n)
  | FRemovedWithProof _ -> FindFailure(n)
  | FRule(_,_,_,l) -> get_desc_list_rec l n
  | FEquation h -> get_desc_rec h n

and get_desc_list_rec l n = 
  match l with
    [] -> FindFailure(n)
  | (a::l') ->
      match get_desc_rec a n with
	FindSuccess d -> FindSuccess d
      | FindFailure n' -> get_desc_list_rec l' n'


let get_desc s t n =
  match get_desc_rec t n with
    FindSuccess d -> d
  | FindFailure n' -> 
      print_string ("Hypothesis " ^ (string_of_int n) ^ " not found (" ^ s ^ ")\n");
      Display.Text.display_history_tree "" t;
      internal_error ("failed to find history hypothesis (" ^ s ^ ")")

(* Rebuild the derivation tree *)

let rec build_fact_tree = function
    Empty(f) -> 
      let tmp_bound_vars = !current_bound_vars in
      current_bound_vars := [];
      let f' = copy_fact2 f in
      cleanup();
      current_bound_vars := tmp_bound_vars;
      { desc = FEmpty;
        thefact = f' }
  | Any(n, h) ->
      let t = build_fact_tree h in
      let d = get_desc "any" t n in
      begin
	try
	  match d.thefact with
	    Pred(p, a::r) when p.p_prop land Param.pred_ANY_STRICT != 0
	      && p.p_prop land Param.pred_ANY == 0 ->
	      (* The arguments of "any" facts must all be equal *)
	      List.iter (fun b -> unify a b) r
	  | _ -> ()
	with Unify -> raise HistoryUnifyError
      end;
      d.desc <- FHAny;
      t
  | Removed(rem_count, dup_count, h) -> 
      let t = build_fact_tree h in
      let d1 = get_desc "removed" t rem_count in
      let d2 = get_desc "removed" t dup_count in
      begin
      try 
        unify_facts d1.thefact d2.thefact
      with Unify -> raise HistoryUnifyError
      end;      
      d1.desc <- FRemovedWithProof d2;
      t
  | HEquation(n,leq,req,h) ->
     let t = build_fact_tree h in
     (* Copy the facts *)
     let tmp_bound_vars = !current_bound_vars in
     current_bound_vars := [];
     let leq' = copy_fact2 leq in
     let req' = copy_fact2 req in
     cleanup();
     current_bound_vars := tmp_bound_vars;
     if n = -1 then 
       begin
        begin
          try 
            unify_facts req' t.thefact
          with Unify -> raise HistoryUnifyError
        end;
        { desc = FEquation(t);
          thefact = leq' }
       end
     else
       begin
         let d = get_desc "equation" t n in
         begin
           try 
             unify_facts leq' d.thefact
           with Unify -> raise HistoryUnifyError
         end;
         d.desc <- FEquation({ desc = FEmpty;
                               thefact = req' });
         t
       end
  | Rule(n,descr,hyp,concl,constra) -> 
      let tmp_bound = !current_bound_vars in
      current_bound_vars := [];
      let rhyp = List.map copy_fact hyp in
      let rconcl = copy_fact concl in
      let rconstra = List.map copy_constra constra in
      let rdescr = 
	match descr with
	  ProcessRule(hypspec,name_params) -> 
	    ProcessRule(hypspec,List.map copy_term name_params)
	| x -> x
      in
      cleanup();
      current_bound_vars := tmp_bound;
      { desc = FRule(n, rdescr, rconstra, List.map (fun f -> { desc = FEmpty; thefact = f }) rhyp);
	thefact = rconcl }
  | Resolution(h1, n, h2) ->
      let t1 = build_fact_tree h1 in
      let t2 = build_fact_tree h2 in
      let d = get_desc "resolution" t2 n in
      begin
	try 
          unify_facts t1.thefact d.thefact
	with Unify -> raise HistoryUnifyError
      end;
      d.desc <- t1.desc;
      t2
  | TestUnifTrue(n, h2) ->
      let t2 = build_fact_tree h2 in
      let d = get_desc "test_unif_true" t2 n in
      d.desc <- FRule(-1, TestUnif, [], []);
      t2

(** [revise_tree step_name recheck tree] checks that the derivation [tree] 
    is still an attack against the considered property.
It rechecks inequality constraints.
It also rechecks that the derivation still contradicts the desired security 
property.
For non-interference or weak secrets, that's ok: we still have a 
derivation of "bad".
For correspondences, that may be wrong, because unification may
make arguments of some events equal, for instance.
In case [tree] does not satisfy these checks, [revise_tree] raises
[TermsEq.FalseConstraint]. 
When it does, [revise_tree] returns an updated version of [tree].

    [recheck] is either [None] or [Some recheck_fun], where [recheck_fun] is
    a function that takes a clause as argument and returns false when
    the clause contradicts the current query, true when it does not
    contradict it. **)
	
(* [get_clause_from_derivation] rebuilds a Horn clause from a derivation *)

let get_clause_from_derivation tree =
  let concl = tree.thefact in
  let hyp = ref [] in
  let constra = ref [] in

  let rec rebuild_hyp tree =
    match tree.desc with
      FEmpty ->
        if not (List.exists (Termslinks.equal_facts_with_links tree.thefact) (!hyp)) then
          hyp := tree.thefact :: (!hyp)
    | FHAny | FRemovedWithProof _ -> ()
    | FEquation son -> rebuild_hyp son
    | FRule(_, _, rconstra, sons) ->
        List.iter rebuild_hyp sons;
        constra := rconstra @ (!constra)
  in
  rebuild_hyp tree;

  let (hyp', concl', constra') = 
    Terms.auto_cleanup (fun () ->
      (List.map Terms.copy_fact2 (!hyp),
       Terms.copy_fact2 concl,
       List.map Terms.copy_constra2 (!constra)))
  in
  let constra'' = 
    try 
      Terms.auto_cleanup(fun () ->
	 TermsEq.simplify_constra_list (concl'::hyp') constra')
    with TermsEq.FalseConstraint ->
      Parsing_helper.internal_error "False constraints should have been excluded by revise_tree"
  in
  let hist = Rule(-1, LblNone, hyp', concl', constra'') in
  (hyp', concl', hist, constra'')

exception Loop

let rec find_fact f t =
  if 
    (match t.desc with
      FHAny | FEmpty | FRemovedWithProof _ -> false
    | _ -> true) && (Reduction_helper.equal_facts_modulo f t.thefact) then t else
  match t.desc with
    FEquation son -> find_fact f son
  | FRule(_,_,_,sons) -> find_fact_list f sons
  | _ -> raise Not_found

and find_fact_list f = function
    [] -> raise Not_found
  | a::l -> 
      try
	find_fact f a 
      with Not_found ->
	find_fact_list f l
      

type recheck_t = (reduction -> bool) option
	  
let revise_tree stepname recheck tree =
  let rec revise_tree_rec no_loop t =
    if List.memq t no_loop then
      raise Loop
    else
      { desc =
	begin
	  match t.desc with
	    FHAny | FEmpty -> 
	      begin
		match t.thefact with
                  Pred(p, l) when List.for_all (fun t' -> (match Reduction_helper.follow_link t' with Var _ -> true | _ -> false)) l -> t.desc
		| Out _ -> t.desc (* Out facts cannot be proved anyway *)
		| _ -> 
		    (* When unification has lead to instantiating a fact that need not be proved before, try to find a proof for it. *)
	            try
                      (revise_tree_rec (t::no_loop) (find_fact t.thefact tree)).desc
                    with Not_found | Loop -> FEmpty
              end
	  | FRule(n, tags, constra, sons) -> 
	      if constra != [] then
		begin
		  try 
		    let constra' = Terms.auto_cleanup (fun () ->
		      List.map Terms.copy_constra2 constra) in
		    Terms.auto_cleanup(fun () ->
		      ignore (TermsEq.simplify_constra_list [] constra'))
		  with TermsEq.FalseConstraint ->
		    Display.Def.print_line "Unification made an inequality become false.";
		    raise TermsEq.FalseConstraint
		end;
	      FRule(n, tags, constra, List.map (revise_tree_rec no_loop) sons)
	  | FRemovedWithProof t ->  FRemovedWithProof t
	  | FEquation son -> FEquation(revise_tree_rec no_loop son)
	end;
	thefact = t.thefact }
  in
  let tree' = revise_tree_rec [] tree in
  match recheck with
    None -> tree'
  | Some recheck_fun ->
      let cl' = get_clause_from_derivation tree' in
      Display.Def.print_line ("The clause after " ^ stepname ^ " is");
      if !Param.html_output then
	Display.Html.display_rule cl'
      else
	Display.Text.display_rule cl';
      if Terms.auto_cleanup (fun () -> recheck_fun cl') then
	begin
          (* cl' no longer contradicts the query *)
          Display.Def.print_line "This clause does not correspond to an attack against the query.";
	  raise TermsEq.FalseConstraint
        end
      else
        begin
          Display.Def.print_line "This clause still contradicts the query.";
          tree'
        end

(* [build_history recheck clause] builds a derivation for the clause
   [clause] using the history stored in that clause.
   When the depth or number of hypotheses of clauses is bounded,
   it may in fact return a derivation for an instance of [clause].
   In this case, it uses [recheck] to verify that the obtained
   clause still contradicts the desired security property.
   Raises [Not_found] in case of failure *)

let build_history recheck (subgoals, orig_fact, hist_done, constra) =
  assert (!current_bound_vars == []);
  if not (!Param.reconstruct_derivation) then 
    begin
      if !Param.typed_frontend then
	Display.Text.print_line "I do not reconstruct derivations.\nIf you want to reconstruct them, add\n   set reconstructDerivation = true. \nto your script."
      else
	Display.Text.print_line "I do not reconstruct derivations.\nIf you want to reconstruct them, add\n   param reconstructDerivation = true. \nto your script.";
      raise Not_found
    end
  else
  try 
    let new_tree0 = build_fact_tree hist_done in
    let new_tree1 =
      if !Param.simplify_derivation then
	begin
	  TreeHashtbl.clear tree_hashtbl;
	  let r = simplify_tree new_tree0 in
	  TreeHashtbl.clear tree_hashtbl;
	  r
	end
      else
	new_tree0
    in
    incr Param.derivation_number;
    if !Param.html_output then
      begin

	let qs = string_of_int (!Param.derivation_number) in
	if !Param.abbreviate_derivation then
	  begin
	    let (abbrev_table, new_tree2) = Display.abbreviate_derivation new_tree1 in
	    (* Display short derivation *)
	    Display.LangHtml.openfile ((!Param.html_dir) ^ "/derivation" ^ qs ^ ".html") ("ProVerif: derivation for query " ^ qs);
	    Display.Html.print_string "<H1>Derivation</H1>\n";
	    if abbrev_table != [] then Display.Html.display_abbrev_table abbrev_table;
	    Display.Html.display_history_tree "" new_tree2;
	    Display.LangHtml.close();
	    Display.Html.print_string ("<A HREF=\"derivation" ^ qs ^ ".html\">Derivation</A> ");
	    (* Display explained derivation *)
	    Display.LangHtml.openfile ((!Param.html_dir) ^ "/derivationexplained" ^ qs ^ ".html") ("ProVerif: derivation for query " ^ qs);
	    Display.Html.print_string "<H1>Explained derivation</H1>\n";
	    if abbrev_table != [] then Display.Html.display_abbrev_table abbrev_table;
	    Display.Html.explain_history_tree new_tree2;
	    Display.LangHtml.close();
	    Display.Html.print_string ("<A HREF=\"derivationexplained" ^ qs ^ ".html\">Explained derivation</A><br>\n")
	  end
	else
	  begin
	    (* Display short derivation *)
	    Display.LangHtml.openfile ((!Param.html_dir) ^ "/derivation" ^ qs ^ ".html") ("ProVerif: derivation for query " ^ qs);
	    Display.Html.print_string "<H1>Derivation</H1>\n";
	    Display.Html.display_history_tree "" new_tree1;
	    Display.LangHtml.close();
	    Display.Html.print_string ("<A HREF=\"derivation" ^ qs ^ ".html\">Derivation</A> ");
	    (* Display explained derivation *)
	    Display.LangHtml.openfile ((!Param.html_dir) ^ "/derivationexplained" ^ qs ^ ".html") ("ProVerif: derivation for query " ^ qs);
	    Display.Html.print_string "<H1>Explained derivation</H1>\n";
	    Display.Html.explain_history_tree new_tree1;
	    Display.LangHtml.close();
	    Display.Html.print_string ("<A HREF=\"derivationexplained" ^ qs ^ ".html\">Explained derivation</A><br>\n")
	  end
      end
    else if !Param.display_derivation then
      begin
	if !Param.abbreviate_derivation then
	  let (abbrev_table, new_tree2) = Display.abbreviate_derivation new_tree1 in
	  if abbrev_table != [] then Display.Text.display_abbrev_table abbrev_table;
	  if !Param.explain_derivation then
	    Display.Text.explain_history_tree new_tree2
	  else
	    Display.Text.display_history_tree "" new_tree2
	else
	  if !Param.explain_derivation then
	    Display.Text.explain_history_tree new_tree1
	  else
	    Display.Text.display_history_tree "" new_tree1;
	Display.Text.newline()
      end;
    if ((!Param.max_hyp) >= 0) || ((!Param.max_depth) >= 0) then
      begin
	try
	  revise_tree "construction of derivation" recheck new_tree1 
	with TermsEq.FalseConstraint ->
	  print_string "You have probably found a false attack due to the limitations\non depth of terms and/or number of hypotheses.\nI do not know if there is a real attack.\n";
	  if !Param.html_output then
	    Display.Html.print_line "You have probably found a false attack due to the limitations\non depth of terms and/or number of hypotheses.\nI do not know if there is a real attack.";
          cleanup();
	  raise Not_found
      end
    else
      new_tree1
  with HistoryUnifyError ->
      if ((!Param.max_hyp) >= 0) || ((!Param.max_depth) >= 0) then
      begin
        print_string "You have probably found a false attack due to the limitations\non depth of terms and/or number of hypotheses.\nI do not know if there is a real attack.\n";
	if !Param.html_output then
	  Display.Html.print_line "You have probably found a false attack due to the limitations\non depth of terms and/or number of hypotheses.\nI do not know if there is a real attack.";
        cleanup();
	raise Not_found
      end
      else
        internal_error "Unification failed in history rebuilding"


(* [unify_derivation next_f recheck tree] implements a heuristic 
   to find traces more often, especially with complex protocols:
   it unifies rules of the derivation [tree] when possible.
   It calls [next_f] with the obtained derivation.
   Note that success is not guaranteed; however, when the heuristic fails,
   the derivation does not correspond to a trace. 

This heuristic can break inequality constraints.
We recheck them after modifying the derivation tree.
We also recheck that the derivation still contradicts the security 
property after unification, using the function [recheck].

When the heuristic fails or these checks fail, we still try to reconstruct
a trace from the original derivation, by calling [next_f tree]. *)
  
(* [simplify_tree] unifies facts with same session identifier *)

(* [first] is true when this is the first call to simplify_tree. 
   In this case, if we find no unification to do, we do not need to call
   revise_tree, since the derivation has not been modified at all *)

module HashFactId =
  struct

    type factIdElem =
	HypSpec of hypspec
      |	Term of term

    type t = 
	{ hash : int;
	  factId : factIdElem list }

    let equalFactIdElem a b =
      match (a,b) with
	HypSpec h, HypSpec h' -> h = h'
      |	Term t, Term t' -> Termslinks.equal_terms_with_links t t'
      |	_ -> false

    let equal a b = 
      (List.length a.factId == List.length b.factId) &&
      (List.for_all2 equalFactIdElem a.factId b.factId)

    type skel_term =
	SVar of int
      |	SFun of string * skel_term list

    type skel_factIdElem =
	SHypSpec of hypspec
      |	STerm of skel_term

    let rec skeleton_term = function
	Var b -> 
	  begin
	    match b.link with
	      TLink t -> skeleton_term t
	    | NoLink -> SVar(b.vname)
	    | _ -> Parsing_helper.internal_error "unexpected link in skeleton_term"
	  end
      |	FunApp(f,l) -> 
	  match f.f_cat with
	    Name _ -> SFun(f.f_name,[])
	  | _ -> SFun(f.f_name, List.map skeleton_term l)

    let skeleton_factIdElem = function
	HypSpec x -> SHypSpec x
      |	Term t -> STerm(skeleton_term t)

    let hash a = a.hash

    (* build a HashFactId.t from a fact id *)

    let build fid = { hash = Hashtbl.hash(List.map skeleton_factIdElem fid);
		      factId = fid }

  end

module FactHashtbl = Hashtbl.Make(HashFactId)

let rec simplify_tree first recheck tree =
  let unif_to_do_left = ref [] in
  let unif_to_do_right = ref [] in
  let fact_hashtbl = FactHashtbl.create 7 in
  let done_unif = ref false in

  let unif t1 t2 v =
    try
      Terms.occur_check v t2;
      if !Param.html_output then
	begin
	  Display.Html.print_string "Unified ";
	  Display.Html.WithLinks.term t1;
	  Display.Html.print_string " with ";
	  Display.Html.WithLinks.term t2;
	  Display.Html.newline()
	end
      else
	begin
	  Display.Text.print_string "Unified ";
	  Display.Text.WithLinks.term t1;
	  Display.Text.print_string " with ";
	  Display.Text.WithLinks.term t2;
	  Display.Text.newline()
	end;
      Terms.link v (TLink t2);
      done_unif := true
    with Unify -> 
      (* When the occur check fails, it might succeed
	 after rewriting the terms, so try that.

         It is important to check equality *modulo the equational
	 theory* here. Otherwise, unify_modulo may make the two terms equal
	 modulo the theory but still syntactically different, which would 
	 result in an endless iteration of unifyDerivation. *)
      if not (Reduction_helper.equal_open_terms_modulo t1 t2) then
	begin
	  unif_to_do_left := t1 :: (!unif_to_do_left);
	  unif_to_do_right := t2 :: (!unif_to_do_right)
	end
  in

  let rec add_unif_term t1 t2 =
    match t1, t2 with
      FunApp(f1, l1), FunApp(f2,l2) when TermsEq.f_has_no_eq f1 && TermsEq.f_has_no_eq f2 ->
	if f1 == f2 then List.iter2 add_unif_term l1 l2
	(* When f1 != f2, unification fails; I display no message. *)
    | Var v, Var v' when v == v' -> ()
    | Var v, _ -> 
	begin
	  match v.link with
	    NoLink ->
	      begin
		match t2 with
		  Var {link = TLink t2'} -> add_unif_term t1 t2'
		| Var v' when v.unfailing ->
             	    unif t1 t2 v
		| Var v' when v'.unfailing -> 
             	    unif t2 t1 v'
		| FunApp (f_symb,_) when f_symb.f_cat = Failure && v.unfailing = false -> ()
		      (* Unification fails; I display no message *)
		| _ -> unif t1 t2 v
	      end
	  | TLink t1' -> add_unif_term t1' t2
	  | _ -> Parsing_helper.internal_error "Unexpected link in add_unif_term 1"
	end
    | FunApp(f_symb,_), Var v ->
	begin
          match v.link with
             NoLink -> 
	       if v.unfailing = false && f_symb.f_cat = Failure 
               then () (* Unification fails; I display no message *)
               else unif t2 t1 v
           | TLink t2' -> add_unif_term t1 t2'
           | _ -> Parsing_helper.internal_error "Unexpected link in add_unif_term 2"
	end
    | _ ->
        (* It is important to check equality *modulo the equational
	   theory* here. Otherwise, unify_modulo may make the two terms equal
	   modulo the theory but still syntactically different, which would 
	   result in an endless iteration of unifyDerivation. *)
	if not (Reduction_helper.equal_open_terms_modulo t1 t2) then
	  begin
	    unif_to_do_left := t1 :: (!unif_to_do_left);
	    unif_to_do_right := t2 :: (!unif_to_do_right)
	  end
  in
  
  let add_unif_fact f1 f2 =
    if (f1 != f2) then
      match f1, f2 with
	Pred(p1,l1), Pred(p2,l2) when p1 == p2 ->
	  List.iter2 add_unif_term l1 l2
      | Out(t1,_),Out(t2,_) -> 
	  add_unif_term t1 t2
      | _ -> 
	  Display.Def.print_line "Trying to unify incompatible facts in unifyDerivation; skipping this impossible unification."

  in

  let rec check_coherent factId (concl, hyp_spec, name_params, sons) =
    match hyp_spec with
      [] -> ()
    | h1::l1 -> 
	let factId' = (HashFactId.HypSpec h1) :: factId in
	match h1 with
          ReplTag (occ,count_params) -> 
	    (* the session identifier(s) is(are) part of the fact id *)
	    check_coherent ((HashFactId.Term (List.nth name_params count_params)) :: factId') 
	      (concl, l1, name_params, sons) 
	| OutputTag occ | InsertTag occ | InputPTag occ | OutputPTag occ | BeginEvent occ ->
	    if l1 == [] then
	      (* I'm reaching the conclusion *)
	      let fact_id = HashFactId.build factId' in
	      try
		let concl' = FactHashtbl.find fact_hashtbl fact_id in
		add_unif_fact concl concl'
	      with Not_found ->
		FactHashtbl.add fact_hashtbl fact_id concl
	    else
	      check_coherent factId' (concl, l1, name_params, sons)
	| LetTag occ | TestTag occ | LetFilterTag occ | TestUnifTag2 occ | GetTagElse occ ->
	    check_coherent factId' (concl, l1, name_params, sons)
	| InputTag _ | GetTag _ | BeginFact | LetFilterFact -> 
	    let f = (List.hd sons).thefact in
	    let fact_id = HashFactId.build factId' in
	    begin
	      try
		let f' = FactHashtbl.find fact_hashtbl fact_id in
		add_unif_fact f f'
	      with Not_found -> 
		FactHashtbl.add fact_hashtbl fact_id f
	    end;
            check_coherent factId' (concl, l1, name_params, List.tl sons)
	| TestUnifTag _ -> 
	    check_coherent factId' (concl, l1, name_params, List.tl sons) 
  in

  let rec simplify_tree1 t =
    match t.desc with
      FRule(_, ProcessRule(hyp_spec, name_params), constra, sons) -> 
	check_coherent [] (t.thefact, List.rev hyp_spec, List.rev name_params, List.rev sons);
	List.iter simplify_tree1 sons
    | FRule(_,_,_,sons) ->
        List.iter simplify_tree1 sons
    | FEquation son -> simplify_tree1 son
    | FHAny -> 
	begin
	match t.thefact with
	  Pred({p_info = [AttackerGuess _ | AttackerBin _]}, [t1;t2]) ->
	    if t1 != t2 then add_unif_term t1 t2
	| _ -> ()
	end
    | _ -> ()
  in

  simplify_tree1 tree;
(*
  let n = List.length (!coh_tuples) in
  let nf = float_of_int n in
  let bf = float_of_int (!Param.unify_derivation_bound) in
  let n_to_do = ref
      (if !Param.unify_derivation_bound == 0 then -1 else
       if nf *. (nf -. 1.) /. 2. > bf then 
	 let n_to_do = int_of_float (nf -. sqrt(nf *. nf -. 2. *. bf) +. 1.)  in
	 print_string ((string_of_int n) ^ " tuples to unify, so " ^ (string_of_float (nf *. (nf -. 1.) /. 2.)) ^ " calls to check_coherent!\n");
	 print_string ("Considering only the first " ^ (string_of_int n_to_do) ^ " tuples for speed.");
	 print_newline();
	 n_to_do
       else -1)
  in
  if (!n_to_do == -1) && (n > 1000) then
    begin
      print_string ((string_of_int n) ^ " tuples to unify, so " ^ (string_of_float (nf *. (nf -. 1.) /. 2.)) ^ " calls to check_coherent!");
      print_newline()
    end;
  let rec check_coherent_list = function
      [] -> ()
    | (tup1::rest) ->
	decr n_to_do;
	if (!n_to_do) = 0 then () else
	begin
	  List.iter (check_coherent tup1) rest;
	  check_coherent_list rest
	end
  in
  check_coherent_list (!coh_tuples);
*)
  if (!unif_to_do_left) == [] then
    if !done_unif then
      begin
	Display.Def.print_line "Iterating unifyDerivation.";
        simplify_tree false recheck tree
      end
    else if first then
      begin
	(* print_string "Nothing to unify.\n"; *)
	tree
      end
    else
      begin
	Display.Def.print_line "Fixpoint reached: nothing more to unify.";
	revise_tree "unifyDerivation" recheck tree
      end
  else
    begin
      if !Param.html_output then
	begin
	  Display.Html.print_string "Trying unification ";
	  Display.Html.WithLinks.term_list (!unif_to_do_left);
	  Display.Html.print_string " with ";
	  Display.Html.WithLinks.term_list (!unif_to_do_right)
	end
      else
	begin
	  Display.Text.print_string "Trying unification ";
	  Display.Text.WithLinks.term_list (!unif_to_do_left);
	  Display.Text.print_string " with ";
	  Display.Text.WithLinks.term_list (!unif_to_do_right)
	end;
      try
	auto_cleanup (fun () ->
	  TermsEq.unify_modulo_list (fun () -> 
	    Display.Def.print_line " succeeded.";
	    Display.Def.print_line "Iterating unifyDerivation.";
	    simplify_tree false recheck tree
	       ) (!unif_to_do_left) (!unif_to_do_right)
	    )
      with Unify ->
        Display.Def.print_line " failed.";
	revise_tree "unifyDerivation" recheck tree
    end

let unify_derivation next_f recheck tree =
  if !Param.unify_derivation then
    begin
      (* print_string "Starting unifyDerivation.\n"; *)
      if !Param.html_output then
	begin
	  let qs = string_of_int (!Param.derivation_number) in
	  Display.Html.print_string ("<A HREF=\"unifyDeriv" ^ qs ^ ".html\" TARGET=\"unifderiv\">Unify derivation</A><br>\n");
	  Display.LangHtml.openfile ((!Param.html_dir) ^ "/unifyDeriv" ^ qs ^ ".html") ("ProVerif: unifying derivation for query " ^ qs);
	  Display.Html.print_string "<H1>Unifying the derivation</H1>\n"
	end;
      try
	auto_cleanup (fun () ->
	  let tree' = simplify_tree true recheck tree in
	  if !Param.html_output then
	    Display.LangHtml.close();
	  next_f tree')
      with TermsEq.FalseConstraint ->
	Display.Def.print_line "Trying with the initial derivation tree instead.";
	if !Param.html_output then
	  Display.LangHtml.close();
	next_f tree
    end
  else
    next_f tree


