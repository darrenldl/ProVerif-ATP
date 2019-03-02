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

(* Functions that handle processes *)

(* Return the maximum phase number *)
       
let rec get_max_used_phase = function
    Nil -> 0
  | NamedProcess(_, _, p)
  | Repl (p,_)
  | Restr(_,_,p,_)
  | Input(_,_, p,_)
  | Output(_,_,p,_)
  | Event(_,_,p,_) 
  | Insert(_,p,_)
  | Barrier(_,_,p,_) -> get_max_used_phase p
  | Par(p1,p2)
  | Test(_,p1,p2,_)
  | Let(_,_,p1, p2,_)
  | Get(_,_,p1, p2,_)
  | LetFilter(_,_,p1,p2,_) -> max (get_max_used_phase p1) (get_max_used_phase p2)
  | Phase(n,p,_) ->
      max n (get_max_used_phase p)
  | AnnBarrier _ ->
      Parsing_helper.internal_error "Annotated barriers should not occur in the initial process"

(* Reset the type of arguments of names.
   Useful to be able to retranslate the same process or
   a process that contains the same names with
   possibly different arguments in the names *)

let rec reset_name_args = function
    Nil -> ()
  | Restr(name,_,p,_) ->
     name.f_type <- Param.tmp_type, snd name.f_type;
     reset_name_args p
  | NamedProcess(_, _, p)
  | Repl (p,_)
  | Input(_,_, p,_)
  | Output(_,_,p,_)
  | Event(_,_,p,_) 
  | Insert(_,p,_)
  | Phase(_,p,_) 
  | Barrier(_,_,p,_) -> reset_name_args p
  | Par(p1,p2)
  | Test(_,p1,p2,_)
  | Let(_,_,p1, p2,_)
  | Get(_,_,p1, p2,_)
  | LetFilter(_,_,p1,p2,_) -> reset_name_args p1; reset_name_args p2
  | AnnBarrier _ ->
      Parsing_helper.internal_error "Annotated barriers should not occur in the initial process"
                               
                                    
(* [check_inj_coherent q] returns a correspondence query [q'] 
equivalent to [q] with injective markers correctly put in assumption
and conclusion. Stops with an error if this is not possible. *)
	
let rec has_inj = function
    Before(_,ll) ->
      List.exists (List.exists (function
	  NestedQuery q -> has_inj q
	| QEvent (QSEvent (i,_)) -> i
	| QEvent (_) -> false)) ll

let rec get_inj accu = function
    [] -> (None, List.rev accu)
  | (QSEvent(true,_) as inj_goal)::rest ->
      if List.exists (function
	  QSEvent(inj,_) -> inj
	| _ -> false) rest then
	Parsing_helper.user_error "At most one injective event can occur before ==> in a query.";
      (Some inj_goal, List.rev_append accu rest)
  | goal::rest ->
      get_inj (goal::accu) rest
	
let rec check_inj_coherent_r q =
  if has_inj q then
    match q with
      Before(el,ll) ->
	let el' =
	  match get_inj [] el with
	    Some inj_goal, othergoals ->
	      (* We reorder the elements before ==> so that the injective
		 event comes first *)
	      inj_goal::othergoals
	  | None,_ ->
	      match el with
		[QFact _] | [QNeq _] | [QEq _] -> Parsing_helper.user_error "In a query e ==> h, if h contains an injective event, then e must be an event ev or better evinj"
	      | [QSEvent(_,t)] -> [QSEvent(true, t)] (* set the event injective *)
	      | _ -> Parsing_helper.user_error "If a query contains several elements before ==> and has injective events, then it must have at least one injective event before ==>" 
	in
	Before(el', List.map (List.map (function
	    QEvent e -> QEvent e
	  | NestedQuery q' -> NestedQuery (check_inj_coherent_r q'))) ll)
  else q

let check_inj_coherent = function
    (PutBegin _ | QSecret _) as q -> q
  | RealQuery (q,l) -> RealQuery (check_inj_coherent_r q,l)

       
(* Generate a variable from a pattern, reusing variable names as much
   as possible *)

let new_var_pat1 = function
    PatVar b -> copy_var b
  | PatEqual (Var b) -> copy_var b
  | PatTuple (f,l) -> new_var Param.def_var_name (snd f.f_type)
  | PatEqual t -> new_var Param.def_var_name (get_term_type t)

let new_var_pat pat = Var (new_var_pat1 pat)

(* Get the variables that are defined in a pattern *)

let rec get_pat_vars accu = function
    PatVar b -> if List.memq b accu then accu else b :: accu
  | PatTuple(_,l) -> List.fold_left get_pat_vars accu l
  | PatEqual _ -> accu

(* Test whether a variable occurs in a pattern/process *)

let rec occurs_var_pat v = function
    PatVar _ -> false
  | PatTuple(f,l) -> List.exists (occurs_var_pat v) l
  | PatEqual t -> Terms.occurs_var v t

let rec occurs_var_proc v = function
    Nil -> false
  | NamedProcess(_, _, p) -> occurs_var_proc v p
  | Par(p1,p2) -> (occurs_var_proc v p1) || (occurs_var_proc v p2)
  | Repl(p,_) -> occurs_var_proc v p
  | Restr(_,_,p,_) -> occurs_var_proc v p
  | Test(t,p1,p2,_) ->
      (Terms.occurs_var v t) ||
      (occurs_var_proc v p1) || (occurs_var_proc v p2)
  | Input(t,pat,p,_) ->
      (Terms.occurs_var v t) || (occurs_var_pat v pat) ||
      (occurs_var_proc v p)
  | Output(t1,t2,p,_) ->
      (Terms.occurs_var v t1) || (Terms.occurs_var v t2) ||
      (occurs_var_proc v p)
  | Let(pat, t, p1, p2, _) ->
      (Terms.occurs_var v t) || (occurs_var_pat v pat) ||
      (occurs_var_proc v p1) || (occurs_var_proc v p2)
  | LetFilter(_,f,p1,p2,_) ->
      (Terms.occurs_var_fact v f) ||
      (occurs_var_proc v p1) || (occurs_var_proc v p2)
  | Event(t,(args,_),p,_) ->
      (Terms.occurs_var v t) ||
      (match args with
	None -> false
      |	Some l -> List.memq v l) ||
      (occurs_var_proc v p)
  | Insert(t,p,_) ->
      (Terms.occurs_var v t) || (occurs_var_proc v p)
  | Get(pat,t,p,q,_) ->
      (occurs_var_pat v pat) || (Terms.occurs_var v t) ||
      (occurs_var_proc v p) || (occurs_var_proc v q)
  | Phase(_,p,_) -> occurs_var_proc v p
  | Barrier _ | AnnBarrier _ ->
     Parsing_helper.internal_error "Barriers should not appear here (13)"

(* Functions for finding the arguments to include in names *)

(* Determine which variables should be included as arguments of names,
   so that queries can be answered

   If we have a query in which NI occurs several
   times and NI corresponds to a restriction in the process, then
   NI designates any name created at that restriction, possibly
   different names at different occurrences in the query. To say
   that several occurrences of NI correspond to the same name, we
   define a binding "let v = NI[...]" and use several times the variable
   v.

*)

let get_need_vars pi_state s =
  let need_vars_in_names = 
    match pi_state.pi_need_vars_in_names with
    | Function _ ->
       Parsing_helper.internal_error "pi_need_vars_in_names must be computed before Reduction_helper.get_need_vars"
    | Computed x -> x
  in
  let rec get_need_list_rec = function
      [] -> []
    | (s1,s2,e)::l ->
	let rest = get_need_list_rec l in
	if (s = s1) && (not (List.exists (fun (s2',_) -> s2 = s2') rest)) then
	  (s2,e) :: rest
	else
	  rest
  in
  get_need_list_rec need_vars_in_names

(* Gives the string [x] to use in the construct "new a[x = ...]"
   to designate an argument of a name with that meaning *)

let meaning_encode = function
    MUnknown -> ""
  | MSid n -> "!" ^ (string_of_int n)
  | MCompSid -> "!comp"
  | MAttSid -> "!att"
  | MVar(_,None) -> ""
  | MVar(_,Some s) -> s

(* Variant of [meaning_encode] more suitable for generating the
   name of a fresh variable *)

let meaning_name = function
    MUnknown -> Param.def_var_name
  | MSid n -> "!" ^ (string_of_int n)
  | MCompSid -> "!comp"
  | MAttSid -> "!att"
  | MVar(b,_) -> b.sname

(* Add a counter to each element of a list *)

let add_count l =
  List.map (fun x -> (x, ref 0)) l

(* Build the include information used by include_arg and final_check,
   by adding counters when needed *)

type include_info_t =
  envElement Stringmap.StringMap.t *
  (binder * int ref) list option *
  (Ptree.ident * int ref) list

let prepare_include_info env args need_list =
  let args' = match args with
    None -> None
  | Some l -> Some (add_count l)
  in
  (env, args', add_count need_list)

(* Find an element, and increase its counter if found *)

let rec find_count s = function
  [] -> false
| (((a,ext),n)::l) ->
    if s = a then
      begin
        incr n;
        true
      end
    else
      find_count s l

(* Find an element (comparison with physical equality), and increase its counter if found *)

let rec findq_count s = function
  [] -> false
| ((a,n)::l) ->
    if s == a then
      begin
        incr n;
        true
      end
    else
      findq_count s l

(* Does the string [s] correspond to the variable [b]? *)

let is_var env s b =
  try
    match Stringmap.StringMap.find s env with
      EVar b' -> b' == b
    | _ -> false
  with Not_found -> false

(* Determine if an argument should be included in the internal representation
   of a name or not *)

let include_arg (env, args, need_list) m always =
match m with
  MVar(b,_) ->
    let found_in_need_list = (is_var env b.sname b) && (find_count b.sname need_list) in
    let new_meaning =
      if found_in_need_list then MVar(b, Some b.sname) else MVar(b, None)
    in
    begin
    match args with
      None ->
        if (always = Always) || found_in_need_list then Some(new_meaning) else None
    | Some args_content ->
        let found_in_args = findq_count b args_content in
        if found_in_args || found_in_need_list then Some(new_meaning) else None
    end
| m -> Some m

(* Check that all needed variables have been found *)

let final_check (env, args, need_list) sf =
  List.iter (fun ((s,ext), n) ->
    if !n = 0 then
      Parsing_helper.input_error ("variable " ^ s ^ " not defined at restriction " ^ sf) ext) need_list;
  match args with
    None -> ()
  | Some args_content ->
    List.iter (fun (b, n) ->
      if !n = 0 then
        Parsing_helper.internal_error ("variable " ^ (Display.Text.varname b) ^ " not found at restriction " ^ sf)) args_content

let rec count_name_params = function
    [] -> 0
  | (_,_,Always)::l -> 1+count_name_params l
  | (_,_,IfQueryNeedsIt)::l -> count_name_params l

let rec extract_name_params_noneed = function
    [] -> []
  | (_,t,Always)::l ->
      t::(extract_name_params_noneed l)
  | (_,t,IfQueryNeedsIt)::l ->
      extract_name_params_noneed l

let rec extract_name_params sf include_info = function
    [] ->
      final_check include_info sf;
      []
  | (m,t,always)::l ->
      match include_arg include_info m always with
	Some _ -> t::(extract_name_params sf include_info l)
      | None -> extract_name_params sf include_info l

let rec extract_name_params_meaning sf include_info = function
    [] ->
      final_check include_info sf;
      []
  | (m,_,always)::l ->
      match include_arg include_info m always with
	Some m' ->
	  m'::(extract_name_params_meaning sf include_info l)
      | None ->
	  extract_name_params_meaning sf include_info l

let rec extract_name_params_types sf include_info l lt =
  match (l,lt) with
    [],[] ->
      final_check include_info sf;
      []
  | (m,_,always)::l, ty::lt ->
      begin
      match include_arg include_info m always with
	Some _ ->
	  ty::(extract_name_params_types sf include_info l lt)
      | None ->
	  extract_name_params_types sf include_info l lt
      end
  | _ -> Parsing_helper.internal_error "lists should have same length in extract_name_params_types"

(*====================================================================*)
(* Functions to help trace reconstruction algorithms *)

(* Find an element of the list x such that f x is true and
   return (index of x in the list, x). The first element of the list
   has index 0. Raise [Not_found] when not found *)

let findi f l =
  let rec findrec n = function
      [] -> raise Not_found
    | (a::r) ->
	if f a then (n, a) else findrec (n+1) r
  in
  findrec 0 l

(* Remove the first n elements of the list l *)

let rec skip n l =
  if n = 0 then l else
  match l with
    [] -> Parsing_helper.internal_error "skip"
  | (_::l) -> skip (n-1) l

(* replace the n-th element of the list with a' *)

let rec replace_at n a' = function
  [] -> Parsing_helper.internal_error "replace_at"
| (a::l) -> if n = 0 then a'::l else a::(replace_at (n-1) a' l)

(* remove the n-th element of the list *)

let rec remove_at n = function
   [] -> Parsing_helper.internal_error "remove_at"
| (a::l) -> if n = 0 then l else a::(remove_at (n-1) l)

(* add a' as n-th element of the list l *)

let rec add_at n a' l =
  if n = 0 then a' :: l else
  match l with
    [] -> Parsing_helper.internal_error "add_at"
  | (a::l) -> a::(add_at (n-1) a' l)

(* Test equality. t1 and t2 must be closed, but they
   may contain variables linked with TLink
   Optimized code when we have no equations *)

let equal_terms_modulo t1 t2 =
  if TermsEq.hasEquations() then
    try
      auto_cleanup (fun () ->
	TermsEq.unify_modulo (fun () -> ()) t1 t2);
      true
    with Unify ->
      false
  else
    Termslinks.equal_closed_terms t1 t2

(* Matching modulo the equational theory
   t2 must be closed, but may contain variables linked with TLink
   Optimize the code when we have no equations *)

let match_modulo next_f t1 t2 =
  if TermsEq.hasEquations() then
    TermsEq.unify_modulo next_f t1 t2
  else
    begin
      Termslinks.match_terms t1 t2;
      next_f ()
    end

let match_modulo_list next_f l1 l2 =
  if TermsEq.hasEquations() then
    TermsEq.unify_modulo_list next_f l1 l2
  else
    begin
      List.iter2 Termslinks.match_terms l1 l2;
      next_f ()
    end

(* Creates a new name *)

let new_name p s t =
  Terms.create_name s (Terms.fresh_id s) ([], t) p

let rec get_name_charac t =
  match t with
    FunApp({f_cat = Name { prev_inputs_meaning = sl}} as f,l) ->
      let rec find_first_sid sl l =
	match (sl,l) with
	  [],[] -> [f]
	| (((MSid _ | MCompSid | MAttSid) as sid_meaning)::_,sid::_) ->
	    begin
	      match sid with
		FunApp(fsid,[]) -> [f;fsid]
	      | Var {link = TLink t} -> find_first_sid [sid_meaning] [t]
	      | _ -> Parsing_helper.internal_error "a session identifier should be a function symbol without argument"
	    end
	| (_::sl', _::l') ->
	    find_first_sid sl' l'
	| _ -> Parsing_helper.internal_error "different length in find_first_sid"
      in
      find_first_sid sl l
  | Var { link = TLink t } -> get_name_charac t
  | _ -> Parsing_helper.internal_error "unexpected term in get_name_charac"

module Rev_name_tab = Hashtbl.Make (struct
  type t = Types.term
  let equal = equal_terms_modulo
  let hash p =  Hashtbl.hash (get_name_charac p)
end)

let name_mapping = Rev_name_tab.create 7

let init_name_mapping freenames =
  Rev_name_tab.clear name_mapping;
  List.iter (fun n ->
    Rev_name_tab.add name_mapping (FunApp(n,[])) n) freenames

let add_name_for_pat t =
  try
    Rev_name_tab.find name_mapping t
  with Not_found ->
    let n = new_name true (
      match t with
	FunApp(f,_) -> f.f_name
      |	_ -> "a") (Terms.get_term_type t)
    in
    (*
    print_string "New abbreviation: ";
    print_string n.f_name;
    print_string " = ";
    Display.Text.display_term t;
    print_newline();
    *)
    Rev_name_tab.add name_mapping t n;
    n


let add_new_name t =
  let n = new_name false "a" t in
  Rev_name_tab.add name_mapping (FunApp(n,[])) n;
  n

(* Display for debugging *)

let display_hyp_spec = function
  ReplTag (o,_) -> print_string "!"; print_string (string_of_int o)
| InputTag o -> print_string "i"; print_string (string_of_int o)
| BeginEvent o -> print_string "b"; print_string (string_of_int o)
| BeginFact -> print_string "bf"
| LetFilterTag o -> print_string "s"; print_string (string_of_int o)
| LetFilterFact -> print_string "sf"
| OutputTag o -> print_string "o"; print_string (string_of_int o)
| TestTag o -> print_string "t"; print_string (string_of_int o)
| LetTag o -> print_string "l"; print_string (string_of_int o)
| TestUnifTag o -> print_string "u"; print_string (string_of_int o)
| TestUnifTag2 o -> print_string "ud"; print_string (string_of_int o)
| InputPTag o -> print_string "ip"; print_string (string_of_int o)
| OutputPTag o -> print_string "op"; print_string (string_of_int o)
| InsertTag o -> print_string "it"; print_string (string_of_int o)
| GetTag o -> print_string "gt"; print_string (string_of_int o)
| GetTagElse o -> print_string "gte"; print_string (string_of_int o)

let display_tag hsl nl =
  print_string "Process(";
  Display.Text.display_list display_hyp_spec "," hsl;
  print_string "; ";
  Display.Text.WithLinks.term_list nl;
  print_string ")"

(* Equivalence between facts *)

let public_free = ref []

let corresp_att_mess p1 p2 =
  match p1.p_info, p2.p_info with
    [Attacker(i,ta)], [Mess(j,tm)] -> i == j && (ta == tm)
  | _ -> false

let corresp_att_mess_bin p1 p2 =
  match p1.p_info, p2.p_info with
    [AttackerBin(i,ta)], [MessBin(j,tm)] -> i == j && (ta == tm)
  | _ -> false

let match_equiv next_f f1 f2 =
  match (f1,f2) with
    Out(t1,l1), Out(t2,l2) -> match_modulo next_f t2 t1
  | Pred(p1,l1), Pred(p2,l2) when p1 == p2 -> match_modulo_list next_f l2 l1
  | Pred(p1,[t1]), Pred(p2, [t2';t2])
        when (corresp_att_mess p1 p2)
	&& (List.mem t2' (!public_free)) -> match_modulo next_f t2 t1
  | Pred(p1,[t1;t2]), Pred(p2, [t3';t3;t4';t4])
        when (corresp_att_mess_bin p1 p2)
	&& (List.mem t3' (!public_free))
        && (List.mem t4' (!public_free)) -> match_modulo_list next_f [t3;t4] [t1;t2]
  | _ -> raise Unify

let rec match_equiv_list next_f l1 l2 =
  match (l1,l2) with
    [],[] -> next_f()
  | (a1::l1,a2::l2) ->
      match_equiv (fun () -> match_equiv_list next_f l1 l2) a1 a2
  | _ -> Parsing_helper.internal_error "match_equiv_list"

(* Substitute a name for another name *)

let term_subst t n1 n2 =
  Terms.replace_name n1 n2 t

let fact_subst f n1 n2 =
  match f with
    Pred(p,l) -> Pred(p, List.map (fun t -> term_subst t n1 n2) l)
  | Out(t,l) -> Out(term_subst t n1 n2, List.map(fun (b,t) -> (b, term_subst t n1 n2)) l)

let rec pat_subst p n1 n2 =
  match p with
    PatVar b -> PatVar b
  | PatTuple (f,l) -> PatTuple(f,List.map (fun p -> pat_subst p n1 n2) l)
  | PatEqual t -> PatEqual (term_subst t n1 n2)

let rec process_subst p n1 n2 =
  match p with
    Nil -> Nil
  | NamedProcess(s, tl, p) ->
      NamedProcess(s, List.map (fun t -> term_subst t n1 n2) tl, process_subst p n1 n2)
  | Par(p1,p2) -> Par(process_subst p1 n1 n2, process_subst p2 n1 n2)
  | Restr(n,args,p,occ) -> Restr(n, args, process_subst p n1 n2,occ)
  | Repl(p,occ) -> Repl(process_subst p n1 n2, occ)
  | Let(pat,t,p,q,occ) -> Let(pat_subst pat n1 n2, term_subst t n1 n2, process_subst p n1 n2, process_subst q n1 n2,occ)
  | Input(t, pat, p, occ) -> Input(term_subst t n1 n2, pat_subst pat n1 n2, process_subst p n1 n2, occ)
  | Output(tc, t, p, occ) -> Output(term_subst tc n1 n2, term_subst t n1 n2, process_subst p n1 n2, occ)
  | Test(t, p, q, occ) -> Test(term_subst t n1 n2, process_subst p n1 n2, process_subst q n1 n2, occ)
  | Event(t, args, p, occ) -> Event(term_subst t n1 n2, args, process_subst p n1 n2, occ)
  | Insert(t, p, occ) -> Insert(term_subst t n1 n2, process_subst p n1 n2, occ)
  | Get(pat, t, p, q, occ) -> Get(pat_subst pat n1 n2, term_subst t n1 n2, process_subst p n1 n2, process_subst q n1 n2, occ)
  | Phase(n,p,occ) -> Phase(n,process_subst p n1 n2,occ)
  | LetFilter(bl, f, p, q, occ) -> LetFilter(bl, fact_subst f n1 n2, process_subst p n1 n2, process_subst q n1 n2, occ)
  | Barrier(n,tag,p,occ) -> Barrier(n,tag,process_subst p n1 n2,occ)
  | AnnBarrier _ ->
     Parsing_helper.internal_error "Annotated barriers should not appear here (14)"

(* let process_subst = Profile.f4 "process_subst" process_subst *)

(* Copy a process *)

let copy_binder b =
  let b' = Terms.copy_var b in
  match b.link with
    NoLink ->
      Terms.link b (VLink b');
      b'
  | _ -> Parsing_helper.internal_error "unexpected link in copy_binder"

let update_env env =
  Stringmap.StringMap.map (function
      (EVar b) as x ->
	begin
	match b.link with
	  VLink b' -> EVar b'
	| _ -> x
	end
    | x -> x) env

let update_args_opt lopt =
  match lopt with
    None -> None
  | Some l -> Some (List.map (fun b ->
	begin
	match b.link with
	  VLink b' -> b'
	| _ -> b
	end) l)

let rec copy_pat = function
    PatVar b -> PatVar (copy_binder b)
  | PatTuple(f,l) -> PatTuple(f, List.map copy_pat l)
  | PatEqual(t) -> PatEqual (copy_term2 t)

let rec copy_process = function
    Nil -> Nil
  | NamedProcess(s, tl, p) ->
      NamedProcess(s, List.map (fun t -> copy_term2 t) tl, copy_process p)
  | Par(p1,p2) -> Par(copy_process p1, copy_process p2)
  | Restr(n,(args,env),p,occ) -> Restr(n, (update_args_opt args,update_env env), copy_process p,occ)
  | Repl(p,occ) -> Repl(copy_process p, occ)
  | Let(pat, t, p, q, occ) -> let pat' = copy_pat pat in Let(pat', copy_term2 t, copy_process p, copy_process q, occ)
  | Input(t, pat, p, occ) -> let pat' = copy_pat pat in Input(copy_term2 t, pat', copy_process p, occ)
  | Output(tc,t,p, occ) -> Output(copy_term2 tc, copy_term2 t, copy_process p, occ)
  | Test(t,p,q,occ) -> Test(copy_term2 t, copy_process p, copy_process q,occ)
  | Event(t, (args, env), p, occ) -> Event(copy_term2 t, (update_args_opt args,update_env env), copy_process p, occ)
  | Insert(t, p, occ) -> Insert(copy_term2 t, copy_process p, occ)
  | Get(pat, t, p, q, occ) -> let pat' = copy_pat pat in Get(pat', copy_term2 t, copy_process p, copy_process q, occ)
  | Phase(n,p,occ) -> Phase(n, copy_process p,occ)
  | LetFilter(bl, f, p, q, occ) -> let bl' = List.map copy_binder bl in LetFilter(bl', copy_fact2 f, copy_process p, copy_process q, occ)
  | Barrier _ | AnnBarrier _ ->
     Parsing_helper.internal_error "Barriers should not appear here (15)"


(* Close all terms after term_evaluation. Indeed, new variables may
   be introduced by term evaluation, when some constructor/destructor
   rules have more variables in their right-hand side than in
   their left-hand side. This may happen when the equational
   theory itself contains linear equations with different variables
   in their left/right-hand sides.
   Also close facts of the derivation tree. *)

let rec close_term = function
    Var v ->
      begin
	 match v.link with
	   NoLink ->
            let name = add_new_name v.btype in
	    let valname = FunApp(name, []) in
	    Terms.link v (TLink valname)
         | TLink t -> close_term t
         | _ -> Parsing_helper.internal_error "unexpected link in close_term"
      end
  | FunApp(f,l) -> List.iter close_term l

let close_fact = function
    Pred(p,l) -> List.iter close_term l
  | Out(t,l) -> close_term t; List.iter (fun (_,t') -> close_term t') l

let rec close_tree tree =
  close_fact tree.thefact;
  match tree.desc with
    FHAny | FEmpty | FRemovedWithProof _ -> ()
  | FEquation son -> close_tree son
  | FRule(_,tags,constra,sons) ->
      List.iter close_tree sons;
      List.iter (List.iter (function
      	| Neq(t1,t2) -> close_term t1; close_term t2)) constra;
      match tags with
        ProcessRule (hsl,nl) -> List.iter close_term nl
      | _ -> ()

(* Close terms for testing equality modulo of open terms
   In contrast to close_term above, it does not register the names
   in rev_name_tab since these names will be immediately forgotten
   after the equality test. *)

let rec close_term_tmp = function
    Var v ->
      begin
	 match v.link with
	   NoLink ->
            let name = new_name false "a" v.btype in
	    let valname = FunApp(name, []) in
	    Terms.link v (TLink valname)
         | TLink t -> close_term_tmp t
         | _ -> Parsing_helper.internal_error "unexpected link in close_term"
      end
  | FunApp(f,l) -> List.iter close_term_tmp l

(* Equality of terms modulo the equational theory
   Works for terms that may not be closed.  *)
let equal_open_terms_modulo t1 t2 =
  if TermsEq.hasEquations() then
    try
      auto_cleanup (fun () ->
	close_term_tmp t1;
	close_term_tmp t2;
	TermsEq.unify_modulo (fun () -> ()) t1 t2);
      true
    with Unify ->
      false
  else
    Termslinks.equal_terms_with_links t1 t2

(* Equality of facts modulo the equational theory
   Works for facts that may not be closed. Note that the equality
   of environments for Out facts is not verified *)
let equal_facts_modulo f1 f2 =
  match f1, f2 with
    Pred(p1,l1), Pred(p2,l2) ->
      (p1 == p2) && (List.for_all2 equal_open_terms_modulo l1 l2)
  | Out(t1,_),Out(t2,_) ->
      equal_open_terms_modulo t1 t2
  | _ -> false

(* Close constraints. Also uses close_term_tmp since the
   names do not need to be registered in Rev_name_tab. *)

let close_constraints constra =
  List.iter (List.iter (function
    | Neq(t1,t2) -> close_term_tmp t1; close_term_tmp t2)) constra

(* Collect constraints that occur in a derivation tree *)

let rec collect_constraints_rec accu tree =
  match tree.desc with
    FHAny | FEmpty -> ()
  | FRemovedWithProof _ -> ()
  | FRule(_,_,constra, l) ->
      accu := constra @ (!accu);
      List.iter (collect_constraints_rec accu) l
  | FEquation t -> collect_constraints_rec accu t

let collect_constraints tree =
  let accu = ref [] in
  collect_constraints_rec accu tree;
  !accu

(* Copy a closed term *)

let rec copy_closed = function
    FunApp(f,l) -> FunApp(f, List.map copy_closed l)
  | Var v -> match v.link with
      TLink l -> copy_closed l
    | _ -> Parsing_helper.internal_error "unexpected link in copy_closed"

let non_syntactic f =
  match f.f_cat  with
    Syntactic f' -> f'
  | _ -> f

let rec copy_closed_remove_syntactic = function
 | FunApp(f,l) -> FunApp(non_syntactic f, List.map copy_closed_remove_syntactic l)
 | Var v ->
     match v.link with
       TLink l -> copy_closed_remove_syntactic l
     | _ -> Parsing_helper.internal_error "unexpected link in copy_closed"

(* Reverse-apply a name substitution
   The pattern must be closed. *)

let rec rev_name_subst = function
    Var v ->
      begin
	match v.link with
	  TLink t ->
	    let t' = rev_name_subst t in
	    v.link <- TLink2 t'; (* Store the image of the translated term, to avoid redoing work *)
	    t'
	| TLink2 t' -> t'
        | _ -> Parsing_helper.internal_error "unexpected link in rev_name_subst"
      end
  | FunApp(f,l) ->
      let f = non_syntactic f in
      match f.f_cat with
	Name _ ->
	  let t' = FunApp(f, rev_name_subst_list l) in
	  FunApp(add_name_for_pat t',[])
      | _ -> (*hash_cons*) (FunApp(f, rev_name_subst_list l))

and rev_name_subst_list l = List.map rev_name_subst l

(* let rev_name_subst = Profile.f1 "rev_name_subst" rev_name_subst *)

(* let rev_name_subst_list = Profile.f1 "rev_name_subst_list" rev_name_subst_list *)

let rev_name_subst_fact = function
    Pred(p,l) -> Pred(p, rev_name_subst_list l)
  | Out(t,l) -> Out(rev_name_subst t, List.map (fun (v,t') -> (v,rev_name_subst t')) l)

(* Check if a term is an allowed channel *)

let rec follow_link = function
    Var { link = TLink t } -> follow_link t
  | Var { link = TLink2 t } -> t
  | t -> t

let rec close_term_collect_links links = function
    Var v ->
      begin
	match v.link with
	  NoLink ->
            let name = add_new_name v.btype in
	    let valname = FunApp(name, []) in
	    Terms.link v (TLink valname);
	    links := (v,v.link) :: (!links);
        | TLink t ->
	    if not (List.exists (fun (v',_) -> v == v') (!links)) then
	       (* If v is in links, we have already done this, so no need to redo it *)
	      begin
		links := (v,v.link) :: (!links);
		close_term_collect_links links t
	      end
        | _ -> Parsing_helper.internal_error "unexpected link in close_term"
      end
  | FunApp(f,l) -> List.iter (close_term_collect_links links) l

let close_fact_collect_links links = function
    Pred(p,l) -> List.iter (close_term_collect_links links) l
  | Out(t,l) -> close_term_collect_links links t; List.iter (fun (_,t') -> close_term_collect_links links t') l

let rec close_tree_collect_links links tree =
  close_fact_collect_links links tree.thefact;
  match tree.desc with
    FHAny | FEmpty | FRemovedWithProof _ -> ()
  | FEquation son -> close_tree_collect_links links son
  | FRule(_,tags,constra,sons) ->
      List.iter (close_tree_collect_links links) sons;
      List.iter (List.iter (function
      	| Neq(t1,t2) -> close_term_collect_links links t1; close_term_collect_links links t2)) constra;
      match tags with
	ProcessRule (hsl,nl) -> List.iter (close_term_collect_links links) nl
      |	_ -> ()

(* Compute the phase number of a predicate *)

let getphase p =
  match p.p_info with
    [Attacker(n,_)] | [Mess(n,_)] | [InputP(n)] | [OutputP(n)]
  | [AttackerBin(n,_)] | [MessBin(n,_)] | [InputPBin(n)] | [OutputPBin(n)]
  | [Table n] | [TableBin n] ->
      n
  | _ -> Parsing_helper.internal_error "Bad predicate for getphase"

(* Evaluates an inequality constraint of a destructor *)

let disequation_evaluation (t1,t2) =
  let assoc_gen_with_var = ref [] in (* Association list general var * var *)
  (* all general variable in [constra] are replaced by classic variables *)
  let t1' = replace_f_var assoc_gen_with_var t1
  and t2' = replace_f_var assoc_gen_with_var t2 in
  Terms.auto_cleanup (fun () ->
    try
      TermsEq.unify_modulo (fun () -> false) t1' t2'
    with Unify -> true)

(* Test if the term is "fail" *)

let is_fail = function
  | FunApp(f,[]) when f.f_cat = Failure -> true
  | _ -> false

(* Update the value of name_params after pattern-matching *)

let rec update_name_params put_var name_params = function
    PatVar b -> (MVar(b, None), copy_closed_remove_syntactic (Var b), put_var)::name_params
  | PatTuple(f,l) -> update_name_params_list put_var name_params l
  | PatEqual _ -> name_params

and update_name_params_list put_var name_params = function
    [] -> name_params
  | (a::l) -> update_name_params_list put_var (update_name_params put_var name_params a) l

(* Check is a term may be represented by several patterns,
   equal modulo the equational theory. In this case, if
   Param.eq_in_names is true, we add the considered term
   to the arguments of names defined afterwards.

Note: it is important that terms are added in name_params in exactly
the same cases in the generation of clauses and in attack
reconstruction.  In the generation of clauses, we use the function
transl_check_several_patterns to check if this addition should be
done. However, we cannot use the same function in attack
reconstruction. Indeed, terms are substituted during the evaluation of
the process, so the result of transl_check_several_patterns would not
be the same in pitransl and in reduction, leading to different values
of name_params, so errors.  Hence, in transl_check_several_patterns we
store in terms_to_add_in_name_params which terms are added to
name_params (by storing their occurrence occ), and we reuse the stored
value in reduction_check_several_patterns, which we call in attack
reconstruction.

*)

let rec check_several_patterns_rec = function
    Var _ -> false
  | FunApp(f,l) ->
      (List.exists check_several_patterns_rec l) ||
      (match f.f_cat with
       	Red rules ->
	  begin
	    match f.f_initial_cat with
	      Red init_rules -> List.length rules > List.length init_rules
	    | _ -> Parsing_helper.internal_error "Reduction_helper.check_several_patterns_rec: f_initial_cat Red expected"
	  end
      | Eq rules -> List.length rules > 0
      | _ -> false)

let transl_check_several_patterns terms_to_add_in_name_params occ t =
  let add_name_param = (!Param.eq_in_names) && (check_several_patterns_rec t) in
  if add_name_param &&
    (not (List.mem occ (!terms_to_add_in_name_params))) then
    terms_to_add_in_name_params := occ :: (!terms_to_add_in_name_params);
  add_name_param

(* This function uses Param.current_state *) 
    
let reduction_check_several_patterns occ =
  let terms_to_add_in_name_params =
    match (!Param.current_state).pi_terms_to_add_in_name_params with
      Unset -> Parsing_helper.internal_error "pi_terms_to_add_in_name_params should be set"
    | Set x -> x
  in
  (!Param.eq_in_names) &&
  (List.mem occ terms_to_add_in_name_params)

(* After the translation of the query in pisyntax/pitsyntax,
   bound names used in the query may not be fully translated,
   because we need first to generate clauses to know the exact arguments of
   the names. The following functions translate the remaining names *)

let rec check_delayed_names_t = function
    Var v ->
      begin
	match v.link with
	  PGLink f ->
	    let t' = f() in
	    v.link <- TLink t';
	    t'
	| TLink t -> t
	| NoLink -> Var v
	| _ -> Parsing_helper.internal_error "unexpected link in check_delayed_names_t"
      end
  | FunApp(f,l) -> FunApp(f, List.map check_delayed_names_t l)


let check_delayed_names_e = function
    QSEvent(b,t) -> QSEvent(b, check_delayed_names_t t)
  | QFact(p,tl) -> QFact(p, List.map check_delayed_names_t tl)
  | QNeq(t1,t2) -> QNeq(check_delayed_names_t t1, check_delayed_names_t t2)
  | QEq(t1,t2) -> QEq(check_delayed_names_t t1, check_delayed_names_t t2)

let rec check_delayed_names_r = function
    Before(evl,hypll) ->
      Before(List.map check_delayed_names_e evl,
	     List.map (List.map check_delayed_names_h) hypll)

and check_delayed_names_h = function
    QEvent(ev) -> QEvent(check_delayed_names_e ev)
  | NestedQuery(q) -> NestedQuery(check_delayed_names_r q)

let check_delayed_names = function
    (PutBegin _ | QSecret _) as q -> q
  | RealQuery (q,l) -> RealQuery(check_delayed_names_r q,l)
      

(* create a pdf file representing the trace in final_state *)
let create_pdf_trace a_to_term noninterf_test_to_string inj_string final_state =
  if !Param.html_output && !Param.graph_output then
    Parsing_helper.user_error ("\"-html\" and \"-graph\" options have both been specified. This is not allowed.")
  else
    if !Param.trace_backtracking && (((!Param.html_output)
				      || (!Param.trace_display_graphicx = Param.GraphDisplay))&& (!Param.trace_display <> Param.NoDisplay)) then
      begin
	if (Sys.command ("cd " ^ !Param.html_dir)) <> 0 then
	  Parsing_helper.user_error ("The directory that you specified, " ^ (!Param.html_dir) ^ ", probably does not exist.")
	else
	  begin
	    let qs = string_of_int (!Param.derivation_number) in
	    let output = (!Param.html_dir ^ "/trace" ^ inj_string ^ qs) in
            Display.AttGraph.write_state_to_dot_file (output ^ ".dot") a_to_term noninterf_test_to_string final_state true;
	    let replace input output =
	      Str.global_replace (Str.regexp_string input) output in
	    let command = replace "%1" output !Param.command_line_graph in
	    let dot_err = Sys.command command in
	    if dot_err <> 0 then
	      if (!Param.command_line_graph) = "dot -Tpdf %1.dot -o %1.pdf" then
		print_string ("Warning: Could not create PDF version of the trace.\nPlease verify that graphviz is installed in your computer.\n")
	      else
		print_string ("Warning: The command line you specified to create the graph trace from the dot file does not seem to work.\n");
	    dot_err
	  end;
      end
    else
      -1
