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


type encode_step =
    Public_vars of (term * funsymb(* public channel *)) list
  | Secret_reach of term list * funsymb (* event *)
  | Secret_ror of term list * funsymb (* public channel *)

let apply_encode_step new_def p = function
  | Public_vars (l) ->
      begin
	try
	  let (_,pub_ch) = List.find (fun (v, _) -> Terms.equal_terms new_def v) l in
	  Output(FunApp(pub_ch, []), new_def, p, Terms.new_occurrence())
	with Not_found -> 
	  p
      end
  | Secret_reach(l, ev) ->
      if List.exists (Terms.equal_terms new_def) l then
	Event(FunApp(ev, [new_def]), (None, Stringmap.StringMap.empty),
	      p, Terms.new_occurrence())
      else
	p
  | Secret_ror(l, pub_ch) ->
      if List.exists (Terms.equal_terms new_def) l then
	let ty = Terms.get_term_type new_def in
	let rand = Terms.create_name "rand" "rand" (Param.tmp_type, ty) true in
	Restr(rand, (None, Stringmap.StringMap.empty),
	      Output(FunApp(pub_ch, []),
		     Terms.make_choice new_def (FunApp(rand, [])), p,
		     Terms.new_occurrence()),
	      Terms.new_occurrence())
      else
	p

let apply_encode_steps new_def p step_list =
  List.fold_left (apply_encode_step new_def) p step_list

let apply_encode_vars vars p1 step_list =
  List.fold_left (fun p v ->
    apply_encode_steps (Var v) p step_list
      ) p1 vars
    
let rec encode_process step_list = function
    Nil -> Nil
  | Par(p1,p2) ->
      Par(encode_process step_list p1,
	  encode_process step_list p2)
  | Repl(p,occ) ->
      Repl(encode_process step_list p, occ)
  | Restr(f, new_args, p, occ) ->
      let new_def = FunApp(f, []) in
      let p1 = encode_process step_list p in
      let p2 = apply_encode_steps new_def p1 step_list in
      Restr(f, new_args, p2, occ)
  | Test(t, p1, p2, occ) ->
      Test(t, encode_process step_list p1, encode_process step_list p2, occ)
  | Input(ch, pat, p, occ) ->
      let vars = Terms.get_vars_pat [] pat in
      let p1 = encode_process step_list p in
      let p2 = apply_encode_vars vars p1 step_list in
      Input(ch, pat, p2, occ)
  | Output(ch, t, p, occ) ->
      Output(ch, t, encode_process step_list p, occ)
  | Let(pat, t, p1, p2, occ) ->
      let vars = Terms.get_vars_pat [] pat in
      let p1' = encode_process step_list p1 in
      let p1'' = apply_encode_vars vars p1' step_list in
      let p2' = encode_process step_list p2 in
      Let(pat, t, p1'', p2', occ)
  | LetFilter(vars, f, p1, p2, occ) ->
      let p1' = encode_process step_list p1 in
      let p1'' = apply_encode_vars vars p1' step_list in
      let p2' = encode_process step_list p2 in
      LetFilter(vars, f, p1'', p2', occ)
  | Event(t, new_args, p, occ) ->
      Event(t, new_args, encode_process step_list p, occ)
  | Insert(t, p, occ) ->
      Insert(t, encode_process step_list p, occ)
  | Get(pat, t, p1, p2, occ) ->
      let vars = Terms.get_vars_pat [] pat in
      let p1' = encode_process step_list p1 in
      let p1'' = apply_encode_vars vars p1' step_list in
      let p2' = encode_process step_list p2 in
      Get(pat, t, p1'', p2', occ)
  | Phase(n, p, occ) ->
      Phase(n, encode_process step_list p, occ)
  | Barrier(n, tag, p, occ) ->
      Barrier(n, tag, encode_process step_list p, occ)
  | AnnBarrier _ ->
      Parsing_helper.internal_error "Annotated barriers should not appear in encode_process"
  | NamedProcess(s, tl, p) ->
      NamedProcess(s, tl, encode_process step_list p)

let encode_process step_list p =
  Simplify.reset_occurrence (encode_process step_list p)
	
(* Treat real-or-random secrecy queries *)
	
let get_name = function
    FunApp(f,_) -> f.f_orig_name
  | Var v -> v.v_orig_name

let get_public_vars_encode_step public_vars =
  let pub_vars_and_channels =
    List.map (fun v ->
      let ch_name = "pub_ch_" ^(get_name v) in
      (v,Terms.create_name ch_name ch_name ([], Param.channel_type) false)
	) public_vars
  in
  (Public_vars(pub_vars_and_channels), List.map snd pub_vars_and_channels)
	
let rec encode_ror_secret_corresp_q next_f pi_state p accu = function
    [] ->
      (* Return the queries that still need to be handled *)
      List.rev accu
  | (QSecret(secrets, public_vars, RealOrRandom) as q)::ql ->
      (* Encode the Real-or-Random secrecy query *)
      let encoded_query = ChoiceQEnc(q) in
      let (pub_vars_encode_step, pub_channels) = get_public_vars_encode_step public_vars in
      let pub_channel = Terms.create_name "pub_ch" "pub_ch" ([], Param.channel_type) false in
      let encoded_process =
	encode_process [ pub_vars_encode_step;
			 Secret_ror(secrets, pub_channel)] p
      in
      let pi_state' =
	{ pi_state with
	  pi_process_query = SingleProcessSingleQuery(encoded_process, encoded_query);
	  pi_freenames = pub_channels @ pub_channel :: pi_state.pi_freenames }
      in
      next_f pi_state';
      (* Handle the other queries *)
      encode_ror_secret_corresp_q next_f pi_state p accu ql
  | q::ql ->
      encode_ror_secret_corresp_q next_f pi_state p (q::accu) ql
    
let encode_ror_secret1 next_f pi_state p = function
    CorrespQuery ql -> CorrespQuery(encode_ror_secret_corresp_q next_f pi_state p [] ql)
  | (NonInterfQuery _ | WeakSecret _) as q -> q
  | QueryToTranslate _ ->
      Parsing_helper.internal_error "Query should have been translated before encoding"
  | CorrespQEnc _ | ChoiceQEnc _ ->
      Parsing_helper.internal_error "Encoded queries should not appear before encoding"
  | ChoiceQuery ->
      Parsing_helper.internal_error "Choice query should have been treated before"

let is_put_begin = function
  | PutBegin _ -> true
  | _ -> false
	
let only_put_begin ql =
  List.for_all is_put_begin ql

let rec encode_ror_secret next_f pi_state p accu = function
    [] -> List.rev accu
  | q::ql ->
      let q' = encode_ror_secret1 next_f pi_state p q in
      let accu' =
	match q' with
	| CorrespQuery ql when only_put_begin ql -> accu 
	| _ -> q' :: accu
      in
      encode_ror_secret next_f pi_state p accu' ql

(* Treat other queries: public_vars, secret [reach] *)

let rec find_one_public_vars_corresp = function
    [] -> Parsing_helper.internal_error "Empty CorrespQuery (or only putbegin)"
  | (PutBegin _)::ql -> find_one_public_vars_corresp ql
  | (RealQuery(_,public_vars) | QSecret(_,public_vars,_))::_ -> public_vars
	
let find_one_public_vars = function
    CorrespQuery ql -> find_one_public_vars_corresp ql
  | NonInterfQuery _ | WeakSecret _ -> []
  | QueryToTranslate _ ->
      Parsing_helper.internal_error "Query should have been translated before encoding"
  | CorrespQEnc _ | ChoiceQEnc _ ->
      Parsing_helper.internal_error "Encoded queries should not appear before encoding"
  | ChoiceQuery ->
      Parsing_helper.internal_error "Choice query should have been treated before"
    
let includes pv1 pv2 =
  List.for_all (fun v1 -> List.exists (Terms.equal_terms v1) pv2) pv1
	
let equal_public_vars pv1 pv2 =
  (includes pv1 pv2) && (includes pv2 pv1)

let has_public_vars public_vars = function
    PutBegin _ -> false
  | RealQuery (_,public_vars') | QSecret(_,public_vars',_) ->
      equal_public_vars public_vars public_vars'

let rec partition_public_vars public_vars = function
  | [] -> ([],[])
  | (CorrespQuery ql)::rest ->
      let (r1, r2) = partition_public_vars public_vars rest in
      let (ql1, ql2) = List.partition (has_public_vars public_vars) ql in
      (* The previous partition puts the "put_begin" in ql2.
         We want them in both lists, so we add them to ql1 *)
      let ql1 = (List.filter is_put_begin ql) @ ql1 in
      let l1 = if only_put_begin ql1 then r1 else (CorrespQuery ql1)::r1 in
      let l2 = if only_put_begin ql2 then r2 else (CorrespQuery ql2)::r2 in
      (l1, l2)
  | ((NonInterfQuery _ | WeakSecret _) as q)::rest ->
      let (r1, r2) = partition_public_vars public_vars rest in
      if public_vars == [] then
	(q::r1, r2)
      else
	(r1, q::r2)
  | (QueryToTranslate _)::_ ->
      Parsing_helper.internal_error "Query should have been translated before encoding"
  | (CorrespQEnc _ | ChoiceQEnc _)::_ ->
      Parsing_helper.internal_error "Encoded queries should not appear before encoding"
  | ChoiceQuery :: _ ->
      Parsing_helper.internal_error "Choice query should have been treated before"

let encode_corresp_query pi_state encode_steps = function
  | (PutBegin _) as x -> x
  | (RealQuery(q, public_vars)) as x ->
      if public_vars == [] then
	x
      else
	(* Remove the public variables: they are encoded in the process *)
	RealQuery(q, [])
  | QSecret(secrets, public_vars, Reachability) ->
      let ty = Terms.get_term_type (List.hd secrets) in
      let tyarg = if !Param.key_compromise = 0 then [ty] else [Param.sid_type; ty] in
      let name = Terms.fresh_id ((get_name (List.hd secrets)) ^ "_contains") in
      let ev = { f_orig_name = name;
		 f_name = name;
		 f_type = tyarg, Param.event_type;
		 f_cat = Eq[];
		 f_initial_cat = Eq[];
		 f_private = true;
		 f_options = 0 }
      in
      encode_steps := (Secret_reach(secrets, ev)) :: (!encode_steps);
      let v = Terms.new_var_def ty in
      let arg = if !Param.key_compromise = 0 then [v] else [Terms.new_var_def Param.sid_type; v] in
      let att_pred = Param.get_pred (Attacker(pi_state.pi_max_used_phase, ty)) in
      (* The query event(x_contains(v)) && attacker(v) ==> false.
	 false is encoded as an empty disjunction. *)
      RealQuery(Before([QSEvent(false,FunApp(ev, arg)); QFact(att_pred, [v])], []), [])
  | QSecret(_,_,RealOrRandom) ->
      Parsing_helper.internal_error "secret .. [real_or_random] should have been already encoded" 
	
let encode_reach_secret pi_state encode_steps = function
  | CorrespQuery(ql) ->
      let ql' = List.map (encode_corresp_query pi_state encode_steps) ql in
      if List.for_all2 (==) ql ql' then
	CorrespQuery(ql)
      else
	CorrespQEnc(List.combine ql ql')
  | x -> x

let rec get_events = function
    [] -> []
  | (Secret_reach(_,e))::r -> e :: (get_events r)
  | _::r -> get_events r
    
let rec encode_public_vars next_f pi_state p rest =
  match rest with
    [] -> (* All queries already handled *) ()
  | q::_ ->
      (* find one public_vars *)
      let public_vars = find_one_public_vars q in
      (* separate the queries that have this public_vars from others *)
      let (set1, rest) = partition_public_vars public_vars rest in
      (* encode the queries that have this public_vars *)
      let encode_steps = ref [] in
      let encoded_queries = List.map (encode_reach_secret pi_state encode_steps) set1 in
      let new_events = get_events (!encode_steps) in
      let encode_steps', new_free_names =
	if public_vars == [] then
	  (!encode_steps), []
	else
	  let (pub_vars_encode_step, pub_channels) = get_public_vars_encode_step public_vars in
	  pub_vars_encode_step::(!encode_steps), pub_channels
      in
      let encoded_p =
	if encode_steps' == [] then
	  p
	else
	  encode_process encode_steps' p
      in
      next_f { pi_state with
	  pi_process_query = SingleProcess(encoded_p, encoded_queries);
	  pi_freenames = new_free_names @ pi_state.pi_freenames;
	  pi_events = new_events @ pi_state.pi_events };
      (* treat the rest *)
      encode_public_vars next_f pi_state p rest
	
(* Main encoding functions *)
    
let encode_aux next_f pi_state p ql =
  let rest = encode_ror_secret next_f pi_state p [] ql in
  encode_public_vars next_f pi_state p rest
	
let encode_secret_public_vars next_f pi_state =
  match pi_state.pi_process_query with
    Equivalence _ | SingleProcessSingleQuery(_, ChoiceQuery) -> 
      next_f pi_state
  | SingleProcessSingleQuery(p,q) ->
      encode_aux next_f pi_state p [q]
  | SingleProcess(p,ql) ->
      encode_aux next_f pi_state p ql

  
    
  
(* Give the fact to query from the detailed query
   This is used only to create a resembling specification for SPASS
 *)

let query_to_facts pi_state =
  let facts = ref [] in
  let q_to_facts = function 
      PutBegin _ -> ()
    | RealQuery(Before(el,_), []) ->
	List.iter (function
	    QSEvent(_,(FunApp(f,l) as param)) ->
	      facts :=
		 (if (Pievent.get_event_status pi_state f).end_status = Inj then
		   Pred(Param.end_pred_inj, [Var(Terms.new_var "endsid" Param.sid_type);param])
		 else
		   Pred(Param.end_pred, [param])) :: (!facts)
	  | QSEvent(_, _) ->
	      Parsing_helper.user_error "Events should be function applications"
	  | QFact(p,l) ->
	      facts := (Pred(p,l)) :: (!facts)
	  | QNeq _ | QEq _ -> Parsing_helper.internal_error "no Neq/Eq queries"
		) el
    | QSecret _ | RealQuery _ ->
	Parsing_helper.internal_error "Query secret and queries with public variables should have been encoded before query_to_facts"
  in
  let q2_to_facts = function
      CorrespQuery(ql) -> List.iter q_to_facts ql
    | CorrespQEnc(qql) -> List.iter (fun (_,q) -> q_to_facts q) qql
    | _ ->
	Parsing_helper.internal_error "query_to_facts applies only to correspondence queries"
  in
  begin
    match pi_state.pi_process_query with
    | Equivalence _ ->
	Parsing_helper.internal_error "query_to_facts does not apply to equivalence queries"
    | SingleProcess(_, ql) -> List.iter q2_to_facts ql
    | SingleProcessSingleQuery(_,q) -> q2_to_facts q
  end;
  !facts

