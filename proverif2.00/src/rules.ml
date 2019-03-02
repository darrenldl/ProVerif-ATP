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

(* let resol_step = ref 0 *)

let sound_mode = ref false
let is_inside_query = ref false
let initialized = ref false
let not_set = ref ([]: fact list)
let elimtrue_set = ref ([]: (int * fact) list)
let close_with_equations = ref false

(* Check that two facts are smaller for all instances *)

let rec get_vars_rep vlist = function
    Var v -> vlist := v :: (!vlist)
  | FunApp(_,l) -> 
    List.iter (get_vars_rep vlist) l

let get_vars_rep_fact vlist = function
    Pred(p,l) -> List.iter (get_vars_rep vlist) l
  | Out(t,l) -> get_vars_rep vlist t;
    List.iter (fun (_,t') -> get_vars_rep vlist t') l

(* [remove_first vlist v] removes the first occurrence of
   [v] in [vlist]. Raise [Not_found] when [v] does not occur in [vlist] *)

let remove_first vlist v =
  let rec remove_first_rec v = function
      [] -> raise Not_found
    | (v'::l) -> if v' == v then l else v' :: (remove_first_rec v l)
  in
  vlist := remove_first_rec v (!vlist)

let is_smaller f1 f2 =
  (Terms.fact_size f1 < Terms.fact_size f2) && 
  (let v1 = ref [] in
   let v2 = ref [] in
   get_vars_rep_fact v1 f1;
   get_vars_rep_fact v2 f2;
   try 
     List.iter (remove_first v2) (!v1);
     true
   with Not_found ->
     false)

let equiv_set = ref ([]: (fact list * fact * int) list)

let check_equiv (hyp, concl, n) =
  (* Check that \sigma h smaller than \sigma concl for all \sigma, for all h in hyp.
     This implies termination of the replacement process *)
  if not (List.for_all (fun h -> is_smaller h concl) hyp) then
    Parsing_helper.user_error "For equivalences, the conclusion must be larger than the hypotheses\nand this must be true for all instances of these facts.";
  (* Check that only ONE replacement rule applies to a given fact.
     This implies confluence of the replacement process *)
  List.iter (fun (_, concl',_) ->
      try
        Terms.auto_cleanup (fun () -> Terms.unify_facts concl concl');
        Parsing_helper.user_error "Conflict between equivalences: two of them apply to the same fact.";
      with Unify -> ()
    ) (!equiv_set);
  match concl with
    Pred(p,((FunApp(f,_) :: _) as l)) when 
      p.p_prop land Param.pred_TUPLE != 0 &&
      f.f_cat = Tuple -> 
    begin
      try 
        let _ = reorganize_fun_app f l in
        Parsing_helper.user_error "Conflict between an equivalence and the decomposition of data constructors:\nan equivalence applies to a fact which is also decomposable by data constructors."
      with Not_found -> ()
    end
  | _ -> ()

let set_equiv set =
  (* Verify that the rules are ok *)
  List.iter check_equiv set;
  (* Store the replacement rules *)
  equiv_set := set

(*****************************************************************
   Limiting the depth of terms and number of hypotheses to
   enforce termination. Disabled in sound mode. 

   The limit function replace subterm with depth egal to 
   Param.max_deph by fresh variable.
   Furthermore, the rule can have a limited number of hypothesis,
   depending of Param.max_hyp.
 ******************************************************************)

let rec limit_depth n t =
  if n = 0 then 
    Terms.new_var_def (Terms.get_term_type t)
  else
    match t with
    | Var v -> t
    | FunApp(f,l) -> FunApp(f, List.map (limit_depth (n-1)) l)

let limit_depth_fact n = function
    Pred(chann,t) -> Pred(chann, List.map (limit_depth n) t)
  | Out(t,l) -> Out(limit_depth n t, List.map (fun (v,t) -> (v, limit_depth n t)) l)

let rec limit_depth_constra n c = List.map (function
      Neq(t1,t2) -> Neq(limit_depth n t1, limit_depth n t2)) c

let rec max_length n = function
    [] -> []
  | (a::l) -> if n = 0 then [] else a::(max_length (n-1) l)

let rec cancel_history n maxn h =
  if maxn <= n then h else 
    cancel_history n (maxn-1) (Any(n,h))

let limit_depth_rule r =
  if !sound_mode then r else
    let r =
      let max_hyp = !Param.max_hyp in
      if max_hyp < 0 then r else
        let (hyp, concl, hist,constra) = r in
        (* remove some hypotheses/constraints if they are too numerous
           Adjust the history hist accordingly *) 
        (max_length max_hyp hyp, concl,
         cancel_history max_hyp (List.length hyp) hist,
         List.map (max_length max_hyp) (max_length max_hyp constra))
    in 
    let max_depth = ! Param.max_depth in
    if max_depth < 0 then r else
      let (hyp, concl, hist,constra) = r in
      (List.map (limit_depth_fact max_depth) hyp, 
       limit_depth_fact max_depth concl, hist, 
       List.map (limit_depth_constra max_depth) constra)

(******************************************************************
   Decompose tuples and data constructors in hypotheses of rules.
   It is important for the correctness of this optimization that
   p:x is never selected when p is a predicate on which we
   perform the decomposition of data constructors, except
   when there are only such facts in the clause.

   Also eliminates duplicate hypotheses.
 ******************************************************************)

let rec pos_in_list init f = function
    [] -> -1 
  | (a::l) -> if f a then init else pos_in_list (init+1) f l

(* is_name_proj 0 s returns true when s starts with numbers, 
   followed by "-proj-". 
   The name of projections as generated by Terms.projection_fun 
   satisfies this condition, and no other function does.
   (In particular, identifiers chosen by the user cannot
   satisfy it, because they cannot contain "-".) *)

let rec is_name_proj n s =
  if String.length s < n+6 then false else
  if ('0' <= s.[n]) && ('9' >= s.[n]) then is_name_proj (n+1) s else
    (String.sub s n 6) = "-proj-"

let is_exempt_from_dectuple (_,_,h,_) =
  match h with
    Rule (_,Apply(f,p),_,_,_) -> 
    (* rules that apply constructors ... *)
    (f.f_cat = Tuple) || 
    (* or their projections *)
    (is_name_proj 0 f.f_name)
  | Rule (_,LblEquiv,_,_,_) -> true
  | _ -> false

let rec decompose_hyp_rec accu hypl = 
  List.fold_right (fun hyp1 (hypl,nl,histl) ->
      let default() = 
        let count = pos_in_list (nl+1) (equal_facts hyp1) hypl in
        if count >= 0 then
          (hypl, nl-1, Removed(nl, count, histl))
        else
          (hyp1::hypl, nl-1, histl)
      in
      match hyp1 with
        Pred(chann,l0) ->
        let rec try_equiv_set = function
            [] ->
            if chann.p_prop land Param.pred_TUPLE != 0 then
              try
                match l0 with
                | (FunApp(f,_) :: _) when f.f_cat = Tuple -> (
                    match History.get_rule_hist (RApplyFunc(f,chann)) with
                    | Rule(_, _, hyp, _, _) as hist_dec ->
                      let l = reorganize_fun_app f l0 in
                      decompose_hyp_rec (hypl, nl+(List.length l)-1, (Resolution(hist_dec, nl, histl))) 
                        (List.map2 (fun hyp x ->
                             match hyp with
                             | Pred(p', _) -> Pred(p', x)
                             | _ -> failwith "Unexpected pattern"
                           ) hyp l)
                    | _ -> failwith "Unexpected pattern"
                  )
                | _ -> default()
              with Not_found -> default()
            else default()
          | (hypeq, concleq, neq)::l ->
            try
              let hypeq' = 
                Terms.auto_cleanup (fun () ->
                    Terms.match_facts concleq hyp1;
                    List.map copy_fact3 hypeq)
              in
              let hist_dec = Rule(neq, LblEquiv, hypeq, concleq, []) in
              decompose_hyp_rec (hypl, nl+(List.length hypeq')-1, (Resolution(hist_dec, nl, histl))) hypeq'
            with NoMatch ->
              try_equiv_set l
        in
        try_equiv_set (!equiv_set)
      | _ -> default()
    ) hypl accu

let decompose_hyp_tuples ((hypl, concl, hist, constra) as rule) =
  if is_exempt_from_dectuple rule then
    rule
  else
    let (hypl', nl', histl') =  
      decompose_hyp_rec ([], (List.length hypl)-1, hist) hypl
    in
    (hypl', concl, histl',constra)


(**********************************************************************
   Counts occurrences of a variable in a list of facts
   [occur_count v l]
   returns the number of occurrences of v in the list of facts l
 ***********************************************************************)

let rec list_add f = function
    [] -> 0
  | (a::l) -> (f a) + (list_add f l)

(** [term_occur_count v t] return the number of occurrence of [v] in [t] *)
let rec term_occur_count v = function
    Var v' -> if v == v' then 1 else 0
  | FunApp(f,l) -> list_add (term_occur_count v) l

let fact_occur_count v = function
    Pred(chann, l) -> list_add (term_occur_count v) l
  | Out(t,l) ->
    term_occur_count v t + list_add (fun (_,t2) -> term_occur_count v t2) l

let occur_count v l = list_add (fact_occur_count v) l

let constra_occur_count v = function
  | Neq(t1,t2) -> term_occur_count v t1 + term_occur_count v t2

(** [occur_count_constra v f] returns the number of occurences of [v] in the formula [f]. *)
let occur_count_constra v l =
  list_add (list_add (constra_occur_count v)) l

(**********************************************************************
   Eliminate hypotheses p(x1...xn) where p has been declared "elimVar"
   or "elimVarStrict" and x1...xn do not occur elsewhere.
   Such a declaration means that p(x...x) is true for some value of x. 
   This is correct in particular when p = attacker. When p is declared
   elimVar and we are not in sound_mode, x1...xn are allowed to occur
   in inequalities.

   In sound_mode, we always require that x1...xn do not occur in 
   inequalities.
 ***********************************************************************)

let elim_any_x ((hypl', concl, histl', constra) (*as r*)) =
  let (hypl'', _, histl'') = List.fold_right (fun hyp1 (hypl, nl, histl) ->
      match hyp1 with
        Pred(chann, l) ->
        begin
          try 
            let (n, ff) = List.find (fun (_, ff) ->
                let hyp1vlist = ref [] in
                Terms.get_vars_fact hyp1vlist hyp1;
                try
                  Terms.auto_cleanup (fun () -> 
                      Terms.unify_facts ff hyp1;
                      (* check that all modified variables of hyp1 do not 
                         occur in the rest of R including inequalities *)
                      List.iter (fun v ->
                          let vt = Terms.follow_link (fun x -> Var x) (Var v) in
                          match vt with
                            Var v' when v' == v -> ()
                          | _ -> 
                            if (occur_count v (concl :: hypl') > fact_occur_count v hyp1)
                            || (occur_count_constra v constra > 0) then raise Unify
                        ) (!hyp1vlist);
                      (* all checks successful *)
                      true
                    )
                with Unify -> 
                  false 
              ) (!elimtrue_set)
            in
            (hypl, nl-1, (Resolution(Rule(n, LblClause, [], ff, []), nl, histl)))
          with Not_found ->
            if
              (chann.p_prop land Param.pred_ANY != 0 && 
               List.for_all (function
                     Var v -> (occur_count v (concl :: hypl') == fact_occur_count v hyp1)
                              && ((not (!sound_mode)) || (occur_count_constra v constra == 0))
                   | _ -> false) l)
              ||
              (chann.p_prop land Param.pred_ANY_STRICT != 0 &&
               List.for_all (function
                     Var v -> (occur_count v (concl :: hypl') == fact_occur_count v hyp1)
                              && (occur_count_constra v constra == 0)
                   | _ -> false) l)
            then
              (hypl, nl-1, (Any(nl, histl)))
            else
              (hyp1 :: hypl, nl-1, histl)
        end
      | _ -> (hyp1 :: hypl, nl-1, histl)
    ) hypl' ([], (List.length hypl')-1, histl')
  in
  (hypl'', concl, histl'',constra)


(**********************************************
   Subsumption test between rules:
   H -> F (C) => H' -> F' (C') iff exists \sigma,
   \sigma H \subseteq H', \sigma F = F', C' => sigma C

   This section consists of:
   1- Matching between hypotheses
   2- Reordering of the hypothesis
   3- Final function : [implies rule1 rule2]
 ***********************************************)

(* 1. Matching between hypotheses. Try all possible orderings
      of the hypotheses *)

(**Test \sigma H \subseteq H' for multiset inclusion *)
let rec match_fact_with_hyp nextf fact1 hyp2 passed_hyp = 
  match hyp2 with
  | [] -> raise NoMatch
  | (fact2::fact_l) -> 
    try
      Terms.auto_cleanup (fun () ->
          Terms.match_facts fact1 fact2;
          nextf (passed_hyp @ fact_l) 
        )
    with NoMatch ->
      match_fact_with_hyp nextf fact1 fact_l (fact2 :: passed_hyp)

let rec match_hyp nextf hyp1 hyp2 = 
  match hyp1 with
  | [] -> nextf ()
  | (fact1 :: fact_l1) -> 
    match_fact_with_hyp 
      (match_hyp nextf fact_l1) fact1 hyp2 []	

(* 2. Try to reorder hypotheses to speed up the subsumption test.
      Put first constant hypotheses (no unbound variable. They
      can contain variables already bound by matching the conclusion.)
      Then put other hypotheses in decreasing size order. *)

let rec has_unbound_var = function
    Var v ->
    begin
      match v.link with
        NoLink -> true
      | TLink _ -> false
      | _ -> internal_error "unexpected link in has_unbound_var"
    end
  | FunApp(_,l) -> List.exists has_unbound_var l

let fact_has_unbound_var = function
    Pred(_, tl) -> List.exists has_unbound_var tl
  | Out(t,l) -> (has_unbound_var t) || (List.exists 
                                          (fun (v,t) -> has_unbound_var t) l)

let rank f =
  if fact_has_unbound_var f then
    fact_size f
  else
    1000000 (* Something probably bigger than all sizes of terms *)

let rank_compare (_,r1) (_,r2) = r2 - r1

let reorder hyp = 
  if List.length hyp > 4 then
    let hyp_rank = List.map (fun f -> (f, rank f)) hyp in
    let hyp_sorted = List.sort rank_compare hyp_rank in
    List.map (fun (f,_) -> f) hyp_sorted
  else
    hyp

(* 3. The final function for subsumption test *)

let implies ((hyp1, concl1, _, constr1) (*as r1*)) ((hyp2, concl2, _, constr2) (*as r2*)) =
  if List.length hyp1 > List.length hyp2 then false else
    (* let t0 = Unix.times() in *)
    try 
      Terms.auto_cleanup (fun () ->
          begin
            match concl1 with
            | Pred(p, []) when p == Param.bad_pred -> ()
            | _ -> Terms.match_facts concl1 concl2
          end;
          match_hyp (TermsEq.implies_constra_list (concl2 :: hyp2) constr2 constr1)
            (reorder hyp1) hyp2;
          (* let t1 = Unix.times() in
             if t1.Unix.tms_utime -. t0.Unix.tms_utime > 1.0 then
             begin
             print_string "testing implication ";
             Display.Text.display_rule r1;
             print_string "=> ";
             Display.Text.display_rule r2;
             print_string "implication true, took ";
             print_float (t1.Unix.tms_utime -. t0.Unix.tms_utime);
             print_string " seconds.";
             Display.Text.newline()
             end; *)
          true
        )
    with NoMatch -> 
      (* let t1 = Unix.times() in
         if t1.Unix.tms_utime -. t0.Unix.tms_utime > 1.0 then
         begin
         print_string "testing implication ";
         Display.Text.display_rule r1;
         print_string "=> ";
         Display.Text.display_rule r2;
         print_string "implication false, took ";
         print_float (t1.Unix.tms_utime -. t0.Unix.tms_utime);
         print_string " seconds.";
         Display.Text.newline()
         end; *)
      false
(* let implies = Profile.f2 "implies" implies *)

(********************************************
   Check usage of may-fail variables and fail
 *********************************************)

let rec check_no_fail = function
    Var v -> assert(not v.unfailing)
  | FunApp(f,l) ->
    assert(f.f_cat != Failure);
    List.iter check_no_fail l

let check_top_fail = function
    Var v -> ()
  | FunApp(f,l) -> List.iter check_no_fail l

let check_constra_fail = function
    Neq(t1,t2) ->
    check_no_fail t1;
    check_no_fail t2

let check_fact_fail = function
    Pred({p_info = [TestUnifP _]}, [t1;t2]) ->
    begin
      (* testunif: allow fail at the top, plus possibly inside a tuple *)
      match (t1,t2) with
        FunApp(f1,l1), FunApp(f2,l2) when f1 == f2 && f1.f_cat == Tuple ->
        List.iter check_top_fail l1;
        List.iter check_top_fail l2
      | _ ->
        check_top_fail t1;
        check_top_fail t2
    end
  | Pred(p,l) ->
    (* attacker predicates: allow fail at the top
       other predicates: don't allow fail at all *)
    begin
      match p.p_info with
        [Attacker _ | AttackerBin _ | AttackerGuess _ ] (* attacker *) -> 
        List.iter check_top_fail l
      | [PolymPred _] (* user-defined *)
      | [] (* user-defined + plus a few others: end_pred, end_pred_inj, bad_pred, ... *)
      | [Equal _] (* equal; used in user-defined clauses *)
      | [Mess _ | InputP _ | OutputP _ | MessBin _ | InputPBin _ 
        | OutputPBin _ | Table _ | TableBin _ | Compromise _ ] ->
        List.iter check_no_fail l
      | _ -> Parsing_helper.internal_error "Terms.check_rule: unexpected predicate info"
    end
  | Out(t,l) ->
    check_no_fail t;
    List.iter (fun (_,t) -> check_no_fail t) l

let check_rule ((hyp, concl, hist, constra) as r) =
  try 
    List.iter check_fact_fail hyp;
    check_fact_fail concl;
    List.iter (List.iter check_constra_fail) constra
  with x ->
    Display.Text.display_rule r;
    raise x

(* The rule base. We distinguish rules that have no selected hypothesis
   [rule_base_ns] and rules that have a selected hypothesis [rule_base_sel].
   The number of the selected hypothesis is stored with the rule
   in the second case. *)

let rule_queue = Pvqueue.new_queue()

let rule_count = ref 0

let rule_base_ns = ref ([] : reduction list)
let rule_base_sel = ref ([] : (reduction * int) list)

(* [add_rule] adds the rule in the rule base.
   It also eliminates subsumed rules. *)

let add_rule rule = 
  (* Check that the rule is not already in the rule base or in the queue *)
  let test_impl = fun r -> implies r rule in
  if (List.exists test_impl (!rule_base_ns)) ||
     (List.exists (function (r,_) -> implies r rule) (!rule_base_sel)) ||
     (Pvqueue.exists rule_queue test_impl) then () else
    begin
      (* eliminates from the rule_base the rules implied by rule *)
      let test_impl = fun r -> not(implies rule r) in
      rule_base_ns := List.filter test_impl (!rule_base_ns);
      rule_base_sel := List.filter
          (function (r,_) -> not (implies rule r)) (!rule_base_sel);
      Pvqueue.filter rule_queue test_impl;
      check_rule rule;
      Pvqueue.add rule_queue rule
    end



(* Several simplification functions for rules *)

(* 1. Simplify the constraints *)

let simplify_rule_constra next_stage (hyp, concl, hist, constraint_list) =
  try
    let constraint_list' = TermsEq.simplify_constra_list (concl::hyp) constraint_list in
    next_stage (hyp, concl, hist, constraint_list')
  with TermsEq.FalseConstraint -> ()

(** Debug mode  
    let simplify_rule_constra next_stage (hyp, concl, hist,constra) =
    if constra <> [] then
    begin
    Printf.printf "Before simplification";
    Display.Text.display_rule (hyp, concl, hist,constra)
    end;
    simplify_rule_constra (fun rule ->
    if constra <> [] then
    begin
    Printf.printf "After simplfication";
    Display.Text.display_rule rule
    end;
    next_stage rule) (hyp, concl, hist,constra) *)

(* 2. eliminate rules that have in hypothesis a "not" fact
      (secrecy assumption) *)

let elim_not next_stage ((hyp', _, _,_) as r) =
  if (List.exists (fun h -> List.exists (matchafact h) (!not_set)) hyp') then
    ()
  else
    next_stage r

(* 3. eliminate tautologies (rules that conclude a fact already in their
      hypothesis) *)

let elim_taut next_stage ((hyp', concl, _,_) as r) =
  if List.exists (equal_facts concl) hyp' then
    ()
  else
    next_stage r

(* 4. eliminate hypotheses p(x1...xn) where p has been declared "elimVar"
   or "elimVarStrict" and x1...xn do not occur elsewhere.
   Such a declaration means that p(x...x) is true for some value of x. 
   This is correct in particular when p = attacker. When p is declared
   elimVar and we are not in sound_mode, x1...xn are allowed to occur
   in inequalities.

   In sound_mode, we always require that x1...xn do not occur in 
   inequalities. *)

let elim_any_x2 next_stage r =
  next_stage (elim_any_x r)

(* 5. decompose tuples and data constructors in hypotheses
   It is important for the correctness of this optimization that
   p:x is never selected when p is a predicate on which we
   perform the decomposition of data constructors, except
   when there are only such facts in the clause.

   Also eliminates duplicate hypotheses.
*)

let decompose_hyp_tuples2 next_stage r =
  next_stage (decompose_hyp_tuples r)

(* 6. decompose tuples and data constructors in conclusion
   It is important for the correctness of this optimization that
   p:x is never selected when p is a predicate on which we
   perform the decomposition of data constructors. *)

let decompose_concl_tuples next_stage ((hyp', concl, hist', constra) as r) =
  if is_exempt_from_dectuple r then
    next_stage r
  else
    let put_clause first_fact hist =
      assert (!current_bound_vars == []);
      let r = (List.map copy_fact hyp', copy_fact first_fact, hist, List.map copy_constra constra) in
      cleanup();
      next_stage r
    in
    let rec tuple_dec hist concl =
      match concl with
        Pred(chann, l0) ->
        let rec try_equiv_set = function
            [] ->
            if chann.p_prop land Param.pred_TUPLE != 0 then
              match l0 with
                FunApp(f,_) :: _ when f.f_cat = Tuple ->
                let l = reorganize_fun_app f l0 in
                List.iteri (fun n first ->
                    match History.get_rule_hist (RApplyProj(f, n, chann)) with
                    | Rule(_,_,_,Pred(p',_), _) as hist_dec ->
                      let concl' = Pred(p', first) in
                      let hist'' = Resolution(hist, 0, hist_dec) in
                      rec_call concl' hist''
                    | _ -> failwith "Unexpected pattern"
                  ) l
              | _ -> raise Not_found
            else
              raise Not_found
          | (hypeq, concleq, neq)::l ->
            try
              let hypeq' =
                Terms.auto_cleanup (fun () ->
                    Terms.match_facts concleq concl;
                    List.map copy_fact3 hypeq)
              in
              List.iteri (fun n concl' ->
                  let hist_dec = Rule(neq + n + 1, LblEquiv, [concleq], List.nth hypeq n, []) in
                  let hist'' = Resolution(hist, 0, hist_dec) in
                  rec_call concl' hist''
                ) hypeq'
            with NoMatch ->
              try_equiv_set l
        in
        try_equiv_set (!equiv_set)
      | _ -> raise Not_found
    and rec_call concl hist =
      try 
        tuple_dec hist concl
      with Not_found ->
        put_clause concl hist
    in
    begin
      try
        tuple_dec hist' concl
      with Not_found ->
        next_stage r
    end

(* 7. Element simplification 
     att(x) /\ elem(M_1, x) /\ ... /\ elem(M_n, x)
   becomes
     att(M_1) /\ ... /\ att(M_n)
   when x does not occur elsewhere in the clause.
   When x occurs elsewhere, the simplification can be done when the
   clause has no selected fact. It leads to a loss of precision in
   this case. (So the latter case is disabled in sound mode.)

   "att" can be any predicate declared with data decomposition (pred_TUPLE).
   The predicate "elem" must be declared pred_ELEM.
*)

let rec collect_preds v = function
    [] -> []
  | (f::l) -> 
    match f with
      Pred(p, [Var v']) when p.p_prop land Param.pred_TUPLE != 0 
                          && v' == v ->
      p :: (collect_preds v l)
    | _ -> collect_preds v l


let rec transform_hyp preds v hist n = function
    [] -> ([], hist)
  | (f::l) ->
    match f with
    | Pred(p, [t1; Var v']) when p.p_prop land Param.pred_ELEM != 0
                              && v == v' -> (
        match History.get_rule_hist (RElem(preds, p)) with
        | Rule(_, _, hyp, _, _) as hist_dec ->
          let hist' = Resolution(hist_dec, n,  hist) in
          let (l', hist'') = transform_hyp preds v hist' (n + List.length preds) l in
          ((List.map (function 
                 (Pred(p',_)) -> Pred(p', [t1])
               | Out _ -> Parsing_helper.internal_error "rules.ml: Pred expected") hyp) @ l', hist'')
        | _ -> failwith "Unexpected pattern"
      )
    | _ ->
      let (l', hist') = transform_hyp preds v hist (n+1) l in
      (f :: l', hist')

let transform_rule v (hyp, concl, hist, constra) =
  let preds = collect_preds v hyp in
  let (hyp', hist') = transform_hyp preds v hist 0 hyp in
  (hyp', concl, hist', constra)

let check_occurs_fact p0 v = function
    Pred(p, [Var v']) when p.p_prop land Param.pred_TUPLE != 0 
                        && v == v' -> false
  | Pred(p, [t1; Var v']) when p.p_prop land Param.pred_ELEM != 0 && p == p0
                               && v == v' -> occurs_var v t1
  | Pred(p, tl) -> List.exists (occurs_var v) tl
  | Out(t, env) -> (occurs_var v t) || (List.exists (fun (_, t) -> occurs_var v t) env)

let check_occurs_concl v = function
  | Pred(p, tl) -> List.exists (occurs_var v) tl
  | Out(t, env) -> internal_error "Out fact should not occur in conclusion"

let check_occurs_constra v c = List.exists 
    (function Neq(t1,t2) -> occurs_var v t1 || occurs_var v t2) c

let check_occurs_rule p0 v (hyp, concl, hist, constra) =
  List.exists (check_occurs_fact p0 v) hyp ||
  (check_occurs_concl v concl) ||
  List.exists (check_occurs_constra v) constra

(* 8.1 Apply the simplification only when x does not occur
   in bad positions. No loss of precision in this case *)

let rec elem_simplif next_stage repeat_next_stage ((hyp, concl, hist, constra) as r) =
  let rec find_optim seen_vars = function
      [] -> next_stage r
    | (f::l) ->
      match f with
        Pred(p,[t1;Var v]) when p.p_prop land Param.pred_ELEM != 0 
                             && not (List.memq v seen_vars) ->
        if check_occurs_rule p v r then
          find_optim (v::seen_vars) l
        else
          repeat_next_stage (transform_rule v r)
      | _ -> find_optim seen_vars l
  in
  find_optim [] hyp

(* 8.2 When the conclusion is selected, apply the simplification
   event at the cost of a loss of precision
   Disabled in sound mode. *)

let rec elem_simplif2 next_stage repeat_next_stage ((hyp, concl, hist, constra) as r) =
  let rec find_optim = function
      [] -> next_stage r
    | (f::l) ->
      match f with
        Pred(p,[t1;Var v]) when (p.p_prop land Param.pred_ELEM != 0)
                             && (collect_preds v hyp <> []) ->
        if Selfun.selection_fun r = -1 then
          let r' = transform_rule v r in
          print_string "Warning: simplifying ";
          Display.Text.display_rule r;
          print_string "into ";
          Display.Text.display_rule r';
          print_string "with loss of precision.\n";
          repeat_next_stage r'
        else
          next_stage r
      | _ -> find_optim l
  in
  if !sound_mode then
    next_stage r 
  else
    find_optim hyp

(* 9. Eliminate redundant hypotheses 
   When R = H /\ H' -> C, and there exists \sigma such that
   \sigma H \subseteq H' and \sigma does not modify variables
   of H' and C, then R can be replaced with R' = H' -> C.
   This is a generalization of elimination of duplicate hypotheses.
   The function below does not really remove redundant hypotheses,
   but transforms them into duplicate hypotheses, so that
   they will be removed by the elimination of duplicate hypotheses.
   (In particular, in the history, they are coded as duplicate hypotheses.)

   Redundant hypotheses appear in particular when there are 
   begin facts. They can slow down the subsumption test
   considerably.

   Note: it is important that elim_redundant_hyp comes as last 
   simplification. In particular, it should come after elimination
   of attacker(x) (so that we don't have many hypotheses attacker(x) 
   remaining, which can be mapped to any hypothesis attacker(..) in
   the instantiated clause) and after simplification of inequalities
   (so that we don't have inequalities with variables not
   used elsewhere, which cause problems for the subsumption test).
*)

let rec match_hyp1 f success match_done h1 = function
    [] -> raise NoMatch
  | (h2::hl2) -> 
    try
      Terms.auto_cleanup (fun () ->
          Terms.match_facts h1 h2;
          let success' = success || 
                         (* h2 has already been used in the matching;
                            if the matching succeeds, then at least
                            one hypothesis will be removed. *)
                         (List.exists (fun (_, h2') -> h2' == h2) match_done)
          in
          f success' ((h1,h2)::match_done)
        )
    with NoMatch ->
      match_hyp1 f success match_done h1 hl2 

let rec match_hyp f hyp1 hyp2 success match_done =
  match hyp1 with
    [] -> f success match_done
  | (h1 :: hl1) -> match_hyp1 (match_hyp f hl1 hyp2) success match_done h1 hyp2

let implies2 f (hyp1, concl1, _, constr1) (hyp2, concl2, _, constr2) =
  Terms.auto_cleanup (fun () ->
      Terms.match_facts concl1 concl2;
      match_hyp (fun success match_done -> 
          if not success then
            (* All hypotheses used in this matching;
               it does not allow eliminating anything,
               try to find a better matching. *)
            raise NoMatch;
          TermsEq.implies_constra_list (concl2 :: hyp2) constr2 constr1 ();
          f match_done)
        (reorder hyp1) hyp2 false []
    )

(*** Just a sanity check 

     let implies3 ((hyp1, concl1, _, constr1) as r1) ((hyp2, concl2, _, constr2) as r2) =
     try
     Terms.auto_cleanup (fun () ->
      Terms.match_facts concl1 concl2;
      List.iter2 Terms.match_facts hyp1 hyp2;
      TermsEq.implies_constra_list (concl2 :: hyp2) constr2 constr1 ()
     )
     with NoMatch -> Parsing_helper.internal_error "elim_redundant_hyp"

     End sanity check ***)

let elim_redundant_hyp next_stage repeat_next_stage ((hyp, _, _, _) as r) =
  if (!Param.redundant_hyp_elim) && 
     ((not (!Param.redundant_hyp_elim_begin_only)) ||
      (List.exists (function 
             Pred({p_info = [TestUnifP _]}, _) -> false
           | Pred(p,_) -> p.p_prop land Param.pred_BLOCKING != 0
           | Out _ -> true) hyp))
  then
    let r' = copy_rule r in
    (*print_string "elim_redundant_hyp starts for";  
      Display.Text.display_rule r; *)
    try
      let r'' = 
        implies2 (fun match_list ->
            let (hyp,_,_,_) = r in
            let (_,concl',hist',constra') = r' in
            let hyp' = List.map (fun h -> List.assq h match_list) hyp in
            (hyp', concl', hist', constra') 
          ) r r'
      in	
      (*if not (implies3 r r'') then
        Parsing_helper.internal_error "elim_redundant_hyp"; 
        print_string "elim_redundant_hyp: found "; 
        Display.Text.display_rule r''; *)
      repeat_next_stage r''
    with NoMatch ->
      (* print_string "elim_redundant_hyp: no redundant hyp found\n"; *)
      next_stage r
  else
    next_stage r

(* 10. Simplification using the equational theory *)

let simp_eq_rule next_stage repeat_next_stage ((hyp, concl, hist, constra) as rule) =
  if TermsEq.hasEquations() then
    try
      let redo_all_optim = ref false in
      let simp_eq_fact = function
          Pred(p,l) when p.p_prop land Param.pred_SIMPEQ != 0 ->
          Pred(p, List.map (fun t ->
              let t' = TermsEq.simp_eq t in
              if not (Terms.equal_terms t t') then redo_all_optim := true;
              t') l)
        | f -> f
      in
      let rule' = (List.map simp_eq_fact hyp, simp_eq_fact concl, hist, constra) in
      if !redo_all_optim then
        repeat_next_stage rule'
      else
        next_stage rule'
    with TermsEq.Reduces ->
      () (* Remove the clause when Param.simpeq_remove is true and an argument
            of attacker2 reduces. *)
  else
    next_stage rule

(* Combines the previous simplication functions, then add the
   simplified rule to the rule base *)

let simplify_rule_constra_normal next_stage r =
  assert (!Terms.current_bound_vars == []);
  simplify_rule_constra next_stage r

let rec normal_rule r = 
  assert (!Terms.current_bound_vars == []);
  decompose_hyp_tuples2 (simp_eq_rule 
                           (elim_not (Weaksecr.simplify (Noninterf.simplify 
                                                           (decompose_concl_tuples (elim_taut (elim_any_x2 
                                                                                                 (simplify_rule_constra_normal (elem_simplif (elem_simplif2
                                                                                                                                                (elim_redundant_hyp (fun r -> add_rule (limit_depth_rule r)) normal_rule) 
                                                                                                                                                normal_rule) normal_rule) ))))
                                                           normal_rule) normal_rule)) normal_rule) r

(* [compos] unifies [concl1] with the selected hypothesis of [hyp2]
   and builds the resulting rule 
   There must be no selected fact in [rule1], and a selected fact in [rule2]

   R = F1 & ... & Fn -> F0
   R' = F'1 & ... & F'n' -> F'0
   can be composed into
      s F1 & ... & s Fn & s F'2 & ... & s F'n -> s F'0
   where s is the most general unifier of F0 and F'1
   if 
    F'1 selected 
   and for all Fi, Fi not selected

*)

let rec replace_nth_list l1 n = function
    [] -> internal_error "replace_nth_list error"
  | (a::l) -> if n = 0 then l1 @ l else a::(replace_nth_list l1 (n-1) l)

let compos next_stage (hyp1, concl1, hist1,constra1) ((hyp2, concl2, hist2,constra2), sel_index) =
  let a = List.nth hyp2 sel_index in
  (* compose with the selected fact *)
  assert (!current_bound_vars == []);
  try
    unify_facts concl1 a;
    let hyp' = List.map copy_fact2 (replace_nth_list hyp1 sel_index hyp2) in
    (* Careful ! The order of hypotheses is important for the history *)
    let concl' = copy_fact2 concl2 in
    let hist' = Resolution(hist1, sel_index, hist2) in
    let constra' = ((List.map copy_constra2 constra1) @ (List.map copy_constra2 constra2)) in
    cleanup();
    (*  incr resol_step; *)
    next_stage (hyp', concl', hist', constra')
  with Unify -> 
    cleanup()

(* Redundancy test 
   [rulelist] and [firstrulelist] must be lists of rules with empty selection
   [initrule] must be a rule with empty selection
   The test returns true if and only if the rule [initrule] can be derived 
   with a derivation containing a rule in [firstrulelist] as top rule 
   and other rules in [rulelist].
*)

let dummy_fact = Pred(Param.dummy_pred, [])

exception Redundant

let redundant rulelist firstrulelist ((_,initconcl,_,_) as initrule) =
  let rec redundant_rec firstrulelist ((hyp, concl, hist, constra) as rule) seen_list =
    if matchafact initconcl concl then
      let sel_index = Selfun.selection_fun (hyp, dummy_fact, hist, constra) in
      if sel_index != -1 then
        if not (List.exists (fun r -> implies r rule) seen_list) then 
          let seen_list = rule :: seen_list in
          List.iter (fun ((hyp1, _, _, _) as rule1) ->
              if List.for_all is_unselectable hyp1 then
                compos (simplify_rule_constra (fun r -> 
                    let r' = elim_any_x (decompose_hyp_tuples r) in
                    if implies r' initrule then
                      raise Redundant
                    else
                      redundant_rec rulelist r' seen_list)) 
                  rule1 (rule,sel_index)
            ) firstrulelist
  in
  try
    redundant_rec firstrulelist ([initconcl], initconcl, Empty(initconcl), []) [];
    false
  with Redundant ->
    if !Param.verbose_redundant then
      begin
        print_string "Redundant rule eliminated:\n";
        Display.Text.display_rule initrule
      end;
    true

let redundant_glob initrule =
  match !Param.redundancy_test with
    Param.NoRed -> false
  | Param.SimpleRed -> 
    redundant (!rule_base_ns) (!rule_base_ns) initrule 
  | Param.BestRed -> 
    if redundant (!rule_base_ns) (!rule_base_ns) initrule then true else
      let rec all_redundant accu = function
          [] -> accu
        | (a::l) -> 
          let rlist = initrule :: (accu @ l) in
          if redundant rlist rlist a then 
            all_redundant accu l
          else
            all_redundant (a::accu) l
      in
      rule_base_ns := List.rev (all_redundant [] (!rule_base_ns));
      false 


let redundant_res res_list =
  let rec all_redundant accu = function
      [] -> accu
    | (a::l) ->
      if redundant (!rule_base_ns) (accu @ l) a then
        all_redundant accu l
      else
        all_redundant (a::accu) l
  in
  all_redundant [] res_list

(* Saturates the rule base, by repeatedly applying the composition [compos] *)

let rec complete_rules () =
  match Pvqueue.get rule_queue with
    None -> !rule_base_ns
  | Some rule -> 
    let sel_index = Selfun.selection_fun rule in
    if sel_index == -1 then
      begin
        if not (redundant_glob rule) then
          begin
            rule_base_ns := rule :: (!rule_base_ns);
            List.iter (compos normal_rule rule) (!rule_base_sel)
          end
      end
    else
      begin
        let rule_sel = (rule, sel_index) in
        rule_base_sel := rule_sel :: (!rule_base_sel);
        List.iter (fun rule2 -> compos normal_rule rule2 rule_sel) (!rule_base_ns)
      end;

    (* display the rule *)
    if !Param.verbose_rules then
      Display.Text.display_rule rule
    else
      begin
        incr rule_count;
        if (!rule_count) mod 200 = 0 then
          begin
            print_string ((string_of_int (!rule_count)) ^ 
                          " rules inserted. The rule base contains " ^
                          (string_of_int ((List.length (!rule_base_ns))
                                          + (List.length (!rule_base_sel)))) ^
                          " rules. " ^
                          (string_of_int (Pvqueue.length rule_queue)) ^
                          " rules in the queue.");
            Display.Text.newline()
          end
      end;

    complete_rules()


(* Search algo *)

let normal_rule_hyp restwork r = 
  let rec normal_rule_hyp_rec r =
    assert (!Terms.current_bound_vars == []);
    decompose_hyp_tuples2
      (elim_any_x2 
         (simplify_rule_constra_normal (elem_simplif (elem_simplif2
                                                        (elim_redundant_hyp restwork normal_rule_hyp_rec) 
                                                        normal_rule_hyp_rec) normal_rule_hyp_rec))) r
  in
  normal_rule_hyp_rec r

let resolve_hyp r0 =
  assert (!initialized);
  let success_accu = ref [] in
  let rec goal_reachable_rec ((subgoals, orig_fact, hist_done, constra) as rule) 
      seen_list =
    if not (List.exists (fun old_rule -> implies old_rule rule) (!success_accu))
    then
      (* if already found a way to generate a more general pattern,
         stop here; otherwise, continue search *)
      let sel_index = Selfun.selection_fun (subgoals, dummy_fact, hist_done, constra) in
      if sel_index == -1 then
        success_accu := rule :: (!success_accu)
      else
        begin
          if not (List.exists (fun r -> implies r rule) seen_list) then 
            let seen_list = rule :: seen_list in
            List.iter (fun rule1 ->
                compos (normal_rule_hyp (fun r -> goal_reachable_rec r seen_list)) 
                  rule1 (rule,sel_index)
              ) (!rule_base_ns)
        end
  in
  TermsEq.close_rule_hyp_eq (normal_rule_hyp (fun r -> goal_reachable_rec r [])) r0;
  redundant_res (!success_accu)
(*
  let r = redundant_res (!success_accu) in
  print_int (!resol_step);
  print_string " resolution steps since the beginning\n";
  r
*)

let query_goal_std g =
  resolve_hyp ([g], g, Empty(g),[])

let query_goal g = 
  match query_goal_std g with
    [] -> 
    print_string "RESULT goal unreachable: ";
    Display.Text.display_fact g;
    Display.Text.newline();
    if !Param.html_output then
      begin
        Display.Html.print_string "<span class=\"result\">RESULT <span class=\"trueresult\">goal unreachable</span>: ";
        Display.Html.display_fact g;
        Display.Html.print_string "</span>";
        Display.Html.newline();
      end
  | l -> 
    List.iter (fun rule ->
        print_string "goal reachable: ";
        Display.Text.display_rule rule;
        if !Param.html_output then
          begin
            Display.Html.print_string "goal reachable: ";
            Display.Html.display_rule rule
          end;
        begin
          try 
            ignore (History.build_history None rule)
          with Not_found -> ()
        end;
        cleanup()
      ) l;
    print_string "RESULT goal reachable: ";
    Display.Text.display_fact g;
    Display.Text.newline();
    if !Param.html_output then
      begin
        Display.Html.print_string "<span class=\"result\">RESULT <span class=\"unknownresult\">goal reachable</span>: ";
        Display.Html.display_fact g;
        Display.Html.print_string "</span>";
        Display.Html.newline();
      end


let query_goal_not g = 
  match query_goal_std g with
    [] -> 
    print_string "ok, secrecy assumption verified: fact unreachable ";
    Display.Text.display_fact g;
    Display.Text.newline();
    if !Param.html_output then
      begin
        Display.Html.print_string "ok, secrecy assumption verified: fact unreachable ";
        Display.Html.display_fact g;
        Display.Html.newline()
      end
  | l -> 
    List.iter (fun rule ->
        print_string "goal reachable: ";
        Display.Text.display_rule rule;
        if !Param.html_output then
          begin
            Display.Html.print_string "goal reachable: ";
            Display.Html.display_rule rule
          end;
        begin
          try 
            ignore (History.build_history None rule)
          with Not_found -> ()
        end;
        cleanup()
      ) l;
    if !Param.html_output then
      Display.Html.print_line "Error: you have given a secrecy assumption that I could not verify.";
    (* TO DO close HTML files properly before this error *)
    Parsing_helper.user_error "you have given a secrecy assumption that I could not verify."

let completion rulelist =
  (* Enter the rules given in "rulelist" in the rule base *)
  if !Param.html_output then
    begin
      let qs = 
        if !is_inside_query then
          "inside" ^ (string_of_int (!Param.inside_query_number))
        else
          (string_of_int (!Param.current_query_number))
      in
      Display.LangHtml.openfile ((!Param.html_dir) ^ "/clauses" ^ qs ^ ".html") ("ProVerif: clauses for query " ^ qs);
      Display.Html.print_string "<H1>Initial clauses</H1>\n";
      Display.Html.display_initial_clauses rulelist;
      Display.LangHtml.close();
      Display.Html.print_string ("<A HREF=\"clauses" ^ qs ^ ".html\" TARGET=\"clauses\">Clauses</A><br>\n")
    end
  else if (!Param.verbose_explain_clauses != Param.NoClauses) || 
          (!Param.explain_derivation = false) then
    begin
      Display.Text.print_string "Initial clauses:";
      Display.Text.display_initial_clauses rulelist
    end;

  (* Reinit the rule base *)
  rule_base_ns := [];
  rule_base_sel := [];
  rule_count := 0;

  (* Insert the initial rules in the queue,
     possibly completing them with equations *) 
  if (!close_with_equations) && (TermsEq.hasEquations()) then
    begin
      print_string "Completing with equations...\n";
      List.iter (fun rule ->
          if !Param.verbose_rules then
            begin
              print_string "Completing ";
              Display.Text.display_rule rule
            end
          else
            begin
              incr rule_count;
              if (!rule_count) mod 200 = 0 then
                begin
                  print_string ((string_of_int (!rule_count)) ^ " rules completed.");
                  Display.Text.newline()
                end
            end;
          TermsEq.close_rule_eq normal_rule (copy_rule rule)
        ) rulelist;
      (* Convert the queue of rules into a list, to display it *)
      let rulelisteq =
        let l = ref [] in
        Pvqueue.iter rule_queue (fun r -> l := r::(!l));
        !l
      in
      if !Param.html_output then
        begin
          Display.LangHtml.openfile ((!Param.html_dir) ^ "/eqclosure.html") "ProVerif: clauses completed with equations";
          Display.Html.print_string "<H1>Clauses completed with equations</H1>\n";
          Display.Html.display_item_list Display.Html.display_rule_nonewline rulelisteq;
          Display.LangHtml.close();	
          Display.Html.print_string "<A HREF=\"eqclosure.html\">Clauses completed with equations</A><br>\n"
        end
      else if !Param.verbose_completed then
        begin
          Display.Text.print_string "Clauses completed with equations:";
          Display.Text.display_item_list Display.Text.display_rule_nonewline rulelisteq
        end
    end
  else
    List.iter normal_rule rulelist;

  (* Initialize the selection function *)
  Selfun.guess_no_unif rule_queue;

  (* Complete the rule base *)
  print_string "Completing...\n";
  let completed_rules = complete_rules() in
  if !Param.html_output then
    begin
      let qs = 
        if !is_inside_query then
          "inside" ^ (string_of_int (!Param.inside_query_number))
        else
          string_of_int (!Param.current_query_number) 
      in
      Display.LangHtml.openfile ((!Param.html_dir) ^ "/compclauses" ^ qs ^ ".html") ("ProVerif: completed clauses for query " ^ qs);
      Display.Html.print_string "<H1>Completed clauses</H1>\n";
      Display.Html.display_item_list Display.Html.display_rule_nonewline completed_rules;
      Display.LangHtml.close();
      Display.Html.print_string ("<A HREF=\"compclauses" ^ qs ^ ".html\">Completed clauses</A><br>\n")
    end
  else if !Param.verbose_completed then
    begin
      Display.Text.print_string "Completed clauses:";
      Display.Text.display_item_list Display.Text.display_rule_nonewline completed_rules
    end;

  (* Query the goals *)
  List.iter query_goal_not (!not_set)


(* Test whether bad is derivable from rulelist; 
   this function does not alter rule_base_ns, so that it can be called
   even if I am calling query_goal_std afterwards to test whether some fact
   is derivable from other completed clauses.
   It is guaranteed to say that bad is not derivable only if it is
   actually not derivable. *)

let internal_bad_derivable rulelist =
  completion rulelist;
  List.filter (function
        (_, Pred(p, []), _, _) when p == Param.bad_pred -> 
	      true
      | _ -> false) (!rule_base_ns)

(* Test whether bad is derivable from rulelist; 
   this function does not alter rule_base_ns, so that it can be called
   even if I am calling query_goal_std afterwards to test whether some fact
   is derivable from other completed clauses.
   Furthermore, it is guaranteed to say that that bad is derivable only
   if it is actually derivable *)

let sound_bad_derivable rulelist =
  assert (!initialized);
  let old_rule_base_ns = !rule_base_ns in
  let old_sound_mode = !sound_mode in
  is_inside_query := true;
  sound_mode := true;
  let r = internal_bad_derivable rulelist in
  is_inside_query := false;
  sound_mode := old_sound_mode;
  rule_base_ns := old_rule_base_ns;
  rule_base_sel := [];
  r

let initialize state =
  initialized := true;
  not_set := state.h_not;
  elimtrue_set := state.h_elimtrue;
  set_equiv state.h_equiv;
  Selfun.initialize state.h_nounif state.h_solver_kind;
  List.iter (fun r -> ignore (Selfun.selection_fun r)) state.h_clauses_to_initialize_selfun;
  Weaksecr.initialize state.h_solver_kind;
  Noninterf.initialize state.h_solver_kind;
  (* This assertions aims to check that equations have already been 
     recorded *)
  assert ((state.h_equations != []) = (TermsEq.hasEquations()));
  close_with_equations := state.h_close_with_equations

let reset() =
  initialized := false;
  not_set := [];
  elimtrue_set := [];
  set_equiv [];
  Selfun.initialize [] Solve_Standard;
  Weaksecr.initialize Solve_Standard;
  Noninterf.initialize Solve_Standard;
  rule_base_ns := [];
  rule_base_sel := [];
  rule_count := 0;
  close_with_equations := false

let bad_derivable state =
  assert (state.h_solver_kind <> Solve_Standard);
  initialize state;
  let r = internal_bad_derivable state.h_clauses in
  reset();
  r

let corresp_initialize state =
  assert (state.h_solver_kind = Solve_Standard);
  initialize state;
  completion state.h_clauses
(* We allow subsequent calls to resolve_hyp, query_goal_std,
   sound_bad_derivable after this initialization and completion *)

let main_analysis state goal_set =
  assert (state.h_solver_kind = Solve_Standard);
  initialize state;
  completion state.h_clauses;
  List.iter query_goal goal_set;
  reset()
