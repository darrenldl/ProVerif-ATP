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

(* split function
   [split_term bv bn t] returns a pair [(t',subst)] where
   [t'] is a term and [subst] is a substitution
   (represented as a list of pairs (variable, image)), such that
   [t = t' subst], the image of [subst] consists of the largest
   possible subterms of [t] that do not contain
   the variables in [bv] and the names in [bn], the domain of
   [subst] consists of fresh variables.

[bv] contains the variables bound under the considered barrier and above [t]
[bn] contains the names bound under the considered barrier and above [t].
 *)

let rec has_destr = function
    Var _ -> false
  | FunApp(f,l) ->
      (match f.f_cat with
	Red _ | Failure -> true
      |	Syntactic _ ->
	  Parsing_helper.internal_error "syntactic symbols should never occur in processes"
      |	_ -> false) &&
      (List.exists has_destr l)

let rec split_term bv bn t =
  if List.exists (fun v -> Terms.occurs_var v t) bv
  || List.exists (fun n -> Terms.occurs_f n t) bn
  || has_destr t then
    match t with
      Var v -> (Var v, [])
    | FunApp(f, l) ->
	let (l', lsubst) = List.split (List.map (split_term bv bn) l) in
	(FunApp(f,l'), List.concat lsubst)
  else
    let x = Terms.new_var Param.def_var_name (Terms.get_term_type t) in
    (Var x, [x,t])

(* This code uses the convention that patterns cannot use variables
   bound in the pattern itself. This is coherent with the rest of ProVerif. *)

let rec split_pattern bv bn = function
    PatVar b -> (PatVar b, [])
  | PatTuple(f,l) ->
      let (l', lsubst) = List.split (List.map (split_pattern bv bn) l) in
      (PatTuple(f,l'), List.concat lsubst)
  | PatEqual t ->
      let (t',s) = split_term bv bn t in
      (PatEqual t', s)

let rec get_pat_var bv = function
    PatVar b -> b::bv
  | PatEqual _ -> bv
  | PatTuple(_,l) -> List.fold_left get_pat_var bv l

(* split function
   [split_process bv bn p] returns a pair [(p',subst)] where
   [p'] is a process and [subst] is a substitution
   (represented as a list of pairs (variable, image)), such that
   [p = p' subst], the image of [subst] consists of the largest
   possible subterms of [p] that do not contain
   the variables in [bv] and the names in [bn], the domain of
   [subst] consists of fresh variables.

[bv] contains the variables bound under the considered barrier and above [p]
[bn] contains the names bound under the considered barrier and above [p].
 *)
let rec split_process bv bn = function
    Nil -> (Nil, [])
  | NamedProcess(s, tl, p) ->
      let (p', s') = split_process bv bn p in
      (* It is difficult to keep the arguments of NamedProcess (tl).
	  If we apply split_process to them, we are going to add useless elements to
          the substitution. *)
      (NamedProcess(s, [], p'), s')
  | Par(p1,p2) ->
      let (p1',s1) = split_process bv bn p1 in
      let (p2',s2) = split_process bv bn p2 in
      (Par(p1',p2'), s1 @ s2)
  | Repl(p,occ) ->
      let (p',s) = split_process bv bn p in
      (Repl(p',occ), s)
  | Restr(f,args,p,occ) ->
      let (p',s) = split_process bv (f::bn) p in
      (Restr(f,args,p',occ), s)
  | Test(t,p1,p2,occ) ->
      let (t',s) = split_term bv bn t in
      let (p1',s1) = split_process bv bn p1 in
      let (p2',s2) = split_process bv bn p2 in
      (Test(t',p1',p2',occ), s @ s1 @ s2)
  | Input(t,pat,p,occ) ->
      let (t',ts) = split_term bv bn t in
      let (pat',pats) = split_pattern bv bn pat in
      let bv' = get_pat_var bv pat in
      let (p',ps) = split_process bv' bn p in
      (Input(t',pat',p',occ), ts @ pats @ ps)
  | Output(t1,t2,p,occ) ->
      let (t1',s1) = split_term bv bn t1 in
      let (t2',s2) = split_term bv bn t2 in
      let (p',s) = split_process bv bn p in
      (Output(t1',t2',p',occ), s1 @ s2 @ s)
  | Let(pat,t,p1,p2,occ) ->
      let (t',ts) = split_term bv bn t in
      let (pat',pats) = split_pattern bv bn pat in
      let bv' = get_pat_var bv pat in
      let (p1',p1s) = split_process bv' bn p1 in
      let (p2',p2s) = split_process bv bn p2 in
      (Let(pat',t',p1',p2',occ), pats @ ts @ p1s @ p2s)
  | Insert(t,p,occ) ->
      let (t',ts) = split_term bv bn t in
      let (p',ps) = split_process bv bn p in
      (Insert(t',p',occ), ts @ ps)
  | Get(pat,t,p1,p2,occ) ->
      let (pat',pats) = split_pattern bv bn pat in
      let bv' = get_pat_var bv pat in
      let (t',ts) = split_term bv' bn t in
      let (p1',p1s) = split_process bv' bn p1 in
      let (p2',p2s) = split_process bv bn p2 in
      (Get(pat',t',p1',p2',occ), pats @ ts @ p1s @ p2s)
  | Event(t,args,p,occ) ->
      (* Events cannot be ignored in case their arguments contain destructors:
	 they may stop the process *)
      let (t',ts) = split_term bv bn t in
      let (p',ps) = split_process bv bn p in
      (Event(t',args,p',occ), ts @ ps)
  | Phase _ ->
      Parsing_helper.user_error "Phases are incompatible with sync"
  | LetFilter _ ->
      Parsing_helper.user_error "Let ... suchthat is incompatible with choice"
  | Barrier(n,tag,p,occ) ->
      let (p',s) = split_process bv bn p in
      (Barrier(n,tag,p',occ), s)
  | AnnBarrier _ ->
      Parsing_helper.internal_error "Annotated barriers should not occur in split"

(* [check_no_barrier p] stops with an error message
   when [p] contains a barrier. *)

let rec check_no_barrier = function
    Nil -> ()
  | NamedProcess(_, _, p) ->
      check_no_barrier p
  | Par(p1,p2) | Test(_,p1,p2,_) | Let(_,_,p1,p2,_) | Get(_,_,p1,p2,_)
  | LetFilter(_,_,p1,p2,_) ->
      check_no_barrier p1; check_no_barrier p2
  | Repl(p,_) | Restr(_,_,p,_) | Input(_,_,p,_) | Output(_,_,p,_)
  | Insert(_,p,_) | Event(_,_,p,_) ->
      check_no_barrier p
  | Phase _ ->
      Parsing_helper.user_error "Phases are incompatible with sync."
  | Barrier _ ->
      Parsing_helper.user_error "Sync should not occur under replication."
  | AnnBarrier _ ->
      Parsing_helper.internal_error "Annotated barriers should not occur in check_no_barrier"

(* [annotate p] transforms all barriers in [p] into
   annotated barriers, and returns the resulting process.
   It also checks that no barriers occur under replication. *)

let seen_tags = ref []
let all_tags = ref []
let additional_channel_names = ref []
                   
let rec annotate = function
    Nil -> Nil
  | NamedProcess(s, tl, p) -> NamedProcess(s, tl, annotate p)
  | Par(p1,p2) -> Par(annotate p1, annotate p2)
  | Repl(p,occ) ->
      (* Barriers should not occur under replication *)
      check_no_barrier p; Repl(p, occ)
  | Restr(f,args,p,occ) -> Restr(f,args, annotate p, occ)
  | Test(t,p1,p2,occ) -> Test(t,annotate p1, annotate p2, occ)
  | Input(t,pat,p,occ) -> Input(t,pat,annotate p, occ)
  | Output(t1,t2,p,occ) -> Output(t1,t2,annotate p, occ)
  | Let(pat,t,p1,p2,occ) -> Let(pat,t,annotate p1, annotate p2, occ)
  | Insert(t,p,occ) -> Insert(t,annotate p,occ)
  | Get(pat,t,p1,p2,occ) -> Get(pat,t,annotate p1,annotate p2,occ)
  | Event(t,args,p,occ) -> Event(t,args,annotate p,occ)
  | Phase _ ->
      Parsing_helper.user_error "Phases are incompatible with sync"
  | LetFilter _ ->
      Parsing_helper.user_error "Let ... suchthat is incompatible with choice"
  | Barrier(n,tag,p,occ) ->
      let (p',s) = split_process [] [] p in
      let a = Terms.create_name "@a" (Terms.fresh_id "a") ([],Param.channel_type) true in
      let c = Terms.create_name "@c" (Terms.fresh_id "c") ([],Param.channel_type) true in
      additional_channel_names := a::c::(!additional_channel_names);
      let tag' =
	match tag with
	  None -> Terms.fresh_id "@"
	| Some s ->
	    if s <> "noswap" then
	      begin
		(* Make sure that the tags are all distinct *)
		if List.mem s (!seen_tags) then
		  Parsing_helper.user_error ("The tags of barriers should be all distinct; " ^ s ^ " appears several times.");
		seen_tags := s :: (!seen_tags)
	      end;
	    s
      in
      all_tags := tag' :: (!all_tags);
      AnnBarrier(n,tag',a,c,s,annotate p',occ)
  | AnnBarrier _ ->
      Parsing_helper.internal_error "Annotated barriers should not occur in annotate"


(* Compilation function: [compile p], where [p] is a process with
   annotated barriers, returns the implementation of [p] using inputs
   and outputs. *)

let rec compile = function
    Nil -> Nil
  | NamedProcess(s, tl, p) ->
      NamedProcess(s, tl, compile p)
  | Par(p1,p2) -> Par(compile p1, compile p2)
  | Repl(p,occ) ->
      (* Barriers should not occur under replication
	 This has been checked by annotate *)
      Repl(p, occ)
  | Restr(f,args,p,occ) -> Restr(f,args, compile p, occ)
  | Test(t,p1,p2,occ) -> Test(t,compile p1, compile p2, occ)
  | Input(t,pat,p,occ) -> Input(t,pat,compile p, occ)
  | Output(t1,t2,p,occ) -> Output(t1,t2,compile p, occ)
  | Let(pat,t,p1,p2,occ) -> Let(pat,t,compile p1, compile p2, occ)
  | Insert(t,p,occ) -> Insert(t,compile p,occ)
  | Get(pat,t,p1,p2,occ) -> Get(pat,t,compile p1,compile p2,occ)
  | Event(t,args,p,occ) -> Event(t,args,compile p,occ)
  | LetFilter(l,f,p1,p2,occ) -> LetFilter(l,f,compile p1,compile p2,occ)
  | Phase _ ->
      Parsing_helper.user_error "Phases are incompatible with sync."
  | AnnBarrier(n,tag,a,c,subst,p,occ) ->
      let p' = compile p in
      let tl = List.map snd subst in
      let type_list = List.map Terms.get_term_type tl in
      let tuple_symb = Terms.get_tuple_fun type_list in
      let pin = Input(FunApp(c,[]), PatTuple(tuple_symb, List.map (fun (b,_) -> PatVar b) subst),
		      p', Terms.new_occurrence()) in
      Output(FunApp(a,[]), FunApp(tuple_symb, tl), pin, Terms.new_occurrence())
  | Barrier _ ->
      Parsing_helper.internal_error "Unannotated barriers should not occur in compile"

(* Barrier function: [barriers [] p] returns the list of all barriers in [p].
   The barriers must be annotated, and the image of the substitution inside
   the annotated barriers is removed. *)

let rec barriers accu = function
    Nil -> accu
  | Par(p1,p2) | Test(_,p1,p2,_) | Let(_,_,p1,p2,_) | Get(_,_,p1,p2,_)
  | LetFilter(_,_,p1,p2,_) ->
      barriers (barriers accu p1) p2
  | Repl(p,_) | Restr(_,_,p,_) | Input(_,_,p,_) | Output(_,_,p,_)
  | Insert(_,p,_) | Event(_,_,p,_) | NamedProcess(_, _, p) ->
      barriers accu p
  | Phase _ ->
      Parsing_helper.user_error "Phases are incompatible with sync."
  | Barrier _ ->
      Parsing_helper.internal_error "All barriers should have been annotated"
  | AnnBarrier(n,tag,a,c,subst,p,_) ->
      barriers ((n,tag,a,c,List.map fst subst,p)::accu) p

(* Comparison function for sorting of barriers.
   We sort according to the barrier number. *)

let compare_barriers (n1,_,_,_,_,_) (n2,_,_,_,_,_) = n1 - n2

(* Equality of processes modulo renaming of bound names and variables
   and of channel names in annotated barriers. *)

let get_link v =
  match v.link with
    NoLink -> v
  | VLink v' -> v'
  | _ -> Parsing_helper.internal_error "unexpected link in Proswapper.get_link"

let get_ren ren f =
  try
    List.assq f ren
  with Not_found ->
    f

let rec eq_term ren1 ren2 t1 t2 =
  match t1,t2 with
    Var v1, Var v2 ->
      let v1' = get_link v1 in
      let v2' = get_link v2 in
      v1' == v2'
  | FunApp(f1,[]), FunApp(f2,[]) ->
      let f1' = get_ren ren1 f1 in
      let f2' = get_ren ren2 f2 in
      f1' == f2'
  | FunApp(f1,l1), FunApp(f2,l2) ->
      (f1 == f2) && (List.for_all2 (eq_term ren1 ren2) l1 l2)
  | _ -> false

let rec eq_pat ren1 ren2 pat1 pat2 =
  match pat1, pat2 with
    PatVar v1, PatVar v2 ->
      (v1.btype == v2.btype) &&
      (let v' = Terms.new_var v1.sname v1.btype in
       Terms.link v1 (VLink v');
       Terms.link v2 (VLink v');
       true)
  | PatTuple(f1,l1), PatTuple(f2,l2) ->
      (f1 == f2) && (List.for_all2 (eq_pat ren1 ren2) l1 l2)
  | PatEqual t1, PatEqual t2 ->
      eq_term ren1 ren2 t1 t2
  | _ -> false

let rec eq_proc ren1 ren2 p1 p2 =
  match p1,p2 with
    Nil, Nil -> true
  | NamedProcess(_, _, p1'), NamedProcess(_, _, p2') ->
     eq_proc ren1 ren2 p1' p2'
  | Par(p1',p1''), Par(p2',p2'') ->
      (eq_proc ren1 ren2 p1' p2') &&
      (eq_proc ren1 ren2 p1'' p2'')
  | Repl(p1',_), Repl(p2',_) ->
      eq_proc ren1 ren2 p1' p2'
  | Restr(f1,_,p1',_), Restr(f2,_,p2',_) ->
      (snd f1.f_type == snd f2.f_type) &&
      (let f' = Terms.create_name f1.f_orig_name (Terms.fresh_id f1.f_name) ([],snd f1.f_type) true in
       eq_proc ((f1,f')::ren1) ((f2,f')::ren2) p1' p2')
  | Test(t1,p1',p1'',_), Test(t2,p2',p2'',_) ->
      (eq_term ren1 ren2 t1 t2) &&
      (eq_proc ren1 ren2 p1' p2') &&
      (eq_proc ren1 ren2 p1'' p2'')
  | Input(t1,pat1,p1',_), Input(t2,pat2,p2',_) ->
      (eq_term ren1 ren2 t1 t2) &&
      (Terms.auto_cleanup (fun () ->
         if eq_pat ren1 ren2 pat1 pat2 then
           eq_proc ren1 ren2 p1' p2'
         else
           false))
  | Output(t1,t1',p1',_), Output(t2,t2',p2',_) ->
      (eq_term ren1 ren2 t1 t2) &&
      (eq_term ren1 ren2 t1' t2') &&
      (eq_proc ren1 ren2 p1' p2')
  | Let(pat1,t1,p1',p1'',_), Let(pat2,t2,p2',p2'',_) ->
      (eq_term ren1 ren2 t1 t2) &&
      (Terms.auto_cleanup (fun () ->
         if eq_pat ren1 ren2 pat1 pat2 then
           eq_proc ren1 ren2 p1' p2'
         else
           false)) &&
      (eq_proc ren1 ren2 p1'' p2'')
  | Insert(t1,p1',_), Insert(t2,p2',_) ->
      (eq_term ren1 ren2 t1 t2) &&
      (eq_proc ren1 ren2 p1' p2')
  | Get(pat1,t1,p1',p1'',_), Get(pat2,t2,p2',p2'',_) ->
      (Terms.auto_cleanup (fun () ->
         if eq_pat ren1 ren2 pat1 pat2 then
           (eq_term ren1 ren2 t1 t2) &&
           (eq_proc ren1 ren2 p1' p2')
         else
           false)) &&
      (eq_proc ren1 ren2 p1'' p2'')
  | Event(t1,_,p1',_), Event(t2,_,p2',_) ->
      (eq_term ren1 ren2 t1 t2) &&
      (eq_proc ren1 ren2 p1' p2')
  | Phase _, _ | _, Phase _ ->
      Parsing_helper.user_error "Phases are incompatible with sync."
  | LetFilter _, _ | _, LetFilter _ ->
      Parsing_helper.user_error "let ... suchthat is incompatible with choice."
  | Barrier _, _ | _, Barrier _ ->
      Parsing_helper.internal_error "Unannotated barriers should not occur in eq_proc"
  | AnnBarrier(n1,_,_,_,subst1,p1',_), AnnBarrier(n2,_,_,_,subst2,p2',_) ->
      (n1 == n2) &&
      (List.length subst1 == List.length subst2) &&
      (List.for_all2 (fun (_,t1) (_,t2) -> eq_term ren1 ren2 t1 t2) subst1 subst2) &&
      (Terms.auto_cleanup (fun () ->
         List.iter2 (fun (v1,_) (v2,_) ->
           let v' = Terms.new_var v1.sname v1.btype in
           Terms.link v1 (VLink v');
           Terms.link v2 (VLink v')) subst1 subst2;
         eq_proc ren1 ren2 p1' p2'))
  | _ -> false

(* [swappable b1 b2] returns true when the two barriers [b1] and [b2]
   can be swapped *)

let swappable (n1,_,_,_,vl1,p1) (n2,_,_,_,vl2,p2) =
  (n1 == n2) &&
  (List.length vl1 == List.length vl2) &&
  (List.for_all2 (fun v1 v2 -> v1.btype == v2.btype) vl1 vl2) &&
  (Terms.auto_cleanup (fun () ->
    let vlfresh = List.map (fun v1 -> Terms.new_var v1.sname v1.btype) vl1 in
    List.iter2 (fun v1 vfresh -> Terms.link v1 (VLink vfresh)) vl1 vlfresh;
    List.iter2 (fun v2 vfresh -> Terms.link v2 (VLink vfresh)) vl2 vlfresh;
    eq_proc [] [] p1 p2))

(* [partition_swappable barriers] returns a list of lists of barriers,
   containing the same elements as [barriers], with swappable barriers
   grouped in the same sublist. *)

let partition_swappable barriers =
  let partition = ref [] in
  let rec add_in_partition bar = function
      [] -> partition := (ref [bar])::(!partition)
    | (part1::rest) ->
	if swappable (List.hd (!part1)) bar then
	  part1 := bar :: (!part1)
	else
	  add_in_partition bar rest
  in
  List.iter (fun bar ->
    match bar with
      (_,"noswap",_,_,_,_) ->
	(* When a barrier is tagged "noswap", put it in a partition
           by itself, so that it is not swapped *)
	partition := (ref [bar])::(!partition)
    | _ ->
	add_in_partition bar (!partition)) barriers;
  List.map (!) (!partition)

(* [get_min [] l] returns a pair [l1,l2] containing
   in [l1] the list of the first barriers of [l] that have the same
   integer barrier (the smallest one since the list [l] is supposed
   to be sorted by increasing integer barrier), and in [l2] the rest of [l] *)

let rec get_min accu = function
    [] -> (accu, [])
  | ((n1,_,_,_,_,_)as bar1)::rest ->
      match accu with
	[] -> get_min [bar1] rest
      | (n0,_,_,_,_,_)::_ ->
	  if n1 == n0 then get_min (bar1::accu) rest else (accu, bar1::rest)

(* [add_in_list barll vll p] returns [in(a1,v1)...in(an,vn).p]
   where [barll] is a list of lists of barriers t[ai,ci,zli]::qi
   and   [vll] is a corresponding list of lists of variables [vi],
   for i in {1...n} *)

let add_in_list barll vll p =
  List.fold_left2 (List.fold_left2 (fun p (_,_,a,_,_,_) v ->
    Input(FunApp(a,[]), PatVar v, p, Terms.new_occurrence()))) p barll vll

(* [add_out barl vl1 vl2 p] returns [out(c1,choice[x1,y1])...out(cn,choice[xn,yn]).p]
   where [barl] is a list of barriers t[ai,ci,zli]::qi,
         [vl1] is a list of variables [xi],
   and   [vl2] is a list of variables [yi] for i in {1...n} *)

let rec add_out barl vl1 vl2 p =
  match barl, vl1, vl2 with
    [],[],[] -> p
  | (_,_,_,c,_,_)::rbarl, v1::rvl1, v2::rvl2 ->
      Output(FunApp(c,[]), FunApp(Param.choice_fun v1.btype, [Var v1; Var v2]),
	  add_out rbarl rvl1 rvl2 p, Terms.new_occurrence())
  | _ -> Parsing_helper.internal_error "barl, vl1, and vl2 should have the same length in Proswapper.add_out"

(* [choose next_f [] l] calls [next_f a l'] where
   [a] is an element of [l]
   [l'] is [l] without the element [a] *)

let rec choose next_f seen = function
    [] -> ()
  | a::l ->
      next_f a (List.rev_append seen l);
      choose next_f (a::seen) l

(* [permut next_f l] calls [next_f] with all permutations
   of the list [l] *)

let rec permut next_f = function
    [] -> next_f []
  | l -> choose (fun a rest -> permut (fun rest' -> next_f (a::rest')) rest) [] l

(* [add_out_permut next_f barl vl p] calls [next_f] on each process
   [out(c1,choice[x1,y1])...out(cn,choice[xn,yn]).p]
   where [barl] is a list of barriers t[ai,ci,zli]::qi,
         [vl] is a list of variables [xi] for i in {1...n}
   and   y1...yn is a permutation of the list x1...xn  *)

let add_out_permut next_f barl vl p =
  permut (fun vl' -> next_f (add_out barl vl vl' p)) (List.rev vl)
  (* The first permutation we try is the one that reverses the order of the full partition *)

(* [add_out_permut_list next_f barll vll p] *)

let rec add_out_permut_list (next_f : process -> unit) barll vll p =
  match barll, vll with
    [], [] -> next_f p
  | barl::rbarll, vl::rvll ->
      add_out_permut (add_out_permut_list next_f rbarll rvll) barl vl p
  | _ -> Parsing_helper.internal_error "barll and vll should have the same length in Proswapper.add_out_permut_list"

(* [compute_partitions barriers] splits the sorted list of barriers [barriers]
   into barriers of the same level, and inside each level, into a partition
   of swappable barriers. *)

let rec compute_partitions = function
    [] -> []
  | barr ->
      let first_barr, rest_barr = get_min [] barr in
      (partition_swappable first_barr) :: (compute_partitions rest_barr)

(* [display_partitions bar_partition] displays [bar_partition] *)

let rec display_partition part =
  let (t,_,_,_,_,_) = List.hd (List.hd part) in
  print_string ("At level " ^ (string_of_int t) ^ ":");
  let useful_elems = List.filter (function [] | [_] -> false | _ -> true) part in
  if useful_elems == [] then
    print_string " nothing can be swapped.\n"
  else
    print_newline();
  List.iter (fun part_elem ->
    print_string " - the barriers ";
    Display.Text.display_list (fun (_,tag,_,_,_,_) -> print_string tag) ", " part_elem;
    print_string " can be permuted.\n"
      ) useful_elems

let rec display_partitions = function
    [] -> ()
  | part1::l ->
      display_partition part1;
      display_partitions l

(* [count_permuts_parts partitions] counts the number of possible permutations
   of the partitions *)

let rec count_permut = function
    [] -> 1
  | (a::l) ->
      (1+List.length l) * (count_permut l)

let rec count_permuts = function
    [] -> 1
  | part1::l ->
      (count_permut part1) * (count_permuts l)

let rec count_permuts_parts = function
    [] -> 1
  | part1::l ->
      (count_permuts part1) * (count_permuts_parts l)

(* [synch next_f barriers] calls [next_f p] for each process [p] in [chi(barriers)]
   for the function [chi] defined in the paper. *)

let rec synch (next_f : process -> unit) = function
    [] -> next_f Nil
  | partition_barr::rest_barr ->
      let vars = List.map (List.map (fun _ ->
	Terms.new_var Param.def_var_name Param.bitstring_type)) partition_barr
      in
      synch
	(add_out_permut_list (fun p ->
	  next_f (add_in_list partition_barr vars p)
	     )  partition_barr vars
	   ) rest_barr

(* [string_to_permut s] converts a string [s] into the internal representation
   of a permutation (list of list of barrier tags with their extent) *)

let string_to_permut (s,ext0) =
  let lexbuf = Lexing.from_string s in
  Parsing_helper.set_start lexbuf ext0;
  let permut =
    try
      Pitparser.permut Pitlexer.token lexbuf
    with Parsing.Parse_error ->
      Parsing_helper.input_error "Syntax error in permutation"
	(Parsing_helper.extent lexbuf)
  in
  (* Check that all tags of the permutation occur in barriers *)
  List.iter (List.iter (fun (s,ext) ->
    if not (List.mem s (!all_tags)) then
      Parsing_helper.input_error ("Tag " ^ s ^ " not found in tags of barriers") ext
	)) permut;
  (* Check that the tags of the permutation are pairwise distinct *)
  let seen_tags = ref [] in
  List.iter (List.iter (fun (s,ext) ->
    if List.mem s (!seen_tags) then
      Parsing_helper.input_error ("Tag " ^ s ^ " occurs several times in the permutation") ext;
    seen_tags := s :: (!seen_tags)
	)) permut;
  permut

(* [get_image_permut s permut] returns the image of [s] by the permutation
   [permut] *)

let rec get_image s orig_list = function
    [s',_] ->
      if s' = s then
	(* [s] is the last element of the cycle, its image is
	   the first element of the cycle *)
	fst (List.hd orig_list)
      else
	raise Not_found
  | [] -> raise Not_found
  | ((s',_)::(((s'',_)::_) as rest)) ->
      if s' = s then
	(* [s] is found in the cycle, its image is the next element
	   of the cycle *)
	s''
      else
	get_image s orig_list rest

let rec get_image_permut s = function
    [] ->
      (* When [s] is not found in the permutation,
         its image is itself *)
      s
  | a::r ->
      (* Try to find [s] in each cycle of the permutation *)
      try
	get_image s a a
      with Not_found ->
	get_image_permut s r


(* [get_elem tag tag' [] barl [] vl] returns [rest_barl, rest_vl, v]
   such that [tag] has image [tag'] by the permutation, the barrier of
   tag [tag'] in [barl] is associated to variable [v], and
   [rest_barl, rest_vl] are obtained by removing the barrier of tag [tag']
   from [barl] and the associated variable [v] from [vl]. *)

let rec get_elem tag tag' seen_barl barl seen_vl vl =
  match (barl, vl) with
    [], [] ->
      Parsing_helper.user_error ("Tag " ^ tag' ^ " is not an authorized image of " ^ tag ^ ".")
  | ((_, bar_tag, _,_,_,_) as bar1)::rest_barl , v1::rest_vl ->
      if bar_tag = tag' then
	(List.rev_append seen_barl rest_barl, List.rev_append seen_vl rest_vl, v1)
      else
	get_elem tag tag' (bar1::seen_barl) rest_barl (v1::seen_vl) rest_vl
  | _ -> Parsing_helper.internal_error "barl and vl should have the same length in Proswapper.get_elem"

(* [compute_permut permut barl barl' vl] returns the permutation of
   the list of variables [vl] specified by [permut].
   [barl] is the list of barriers whose image is not defined yet.
   [barl'] is the list of barriers whose antecedent is not defined yet.
   Each variable in [vl] is associated with the corresponding barrier in [barl'].
   The permutation [permut] maps tags of barriers in [barl] to tags
   of barriers in [barl']. *)

let rec compute_permut permut barl barl' vl =
  match barl with
    [] -> []
  | (_, tag, _,_,_,_)::rest_barl ->
      let tag' = get_image_permut tag permut in
      let (rest_barl', rest_vl, v) = get_elem tag tag' [] barl' [] vl in
      v::(compute_permut permut rest_barl rest_barl' rest_vl)

(* [add_out_permut permut barl vl p] returns a process
   [out(c1,choice[x1,y1])...out(cn,choice[xn,yn]).p]
   where [barl] is a list of barriers t[ai,ci,zli]::qi,
         [vl] is a list of variables [xi] for i in {1...n}
   and   y1...yn is the permutation of the list x1...xn
         specified by [permut] *)

let fixed_add_out_permut permut barl vl p =
  let vl' = compute_permut permut barl barl vl in
  add_out barl vl vl' p

let rec fixed_add_out_permut_list permut barll vll p =
  match barll, vll with
    [], [] -> p
  | barl::rbarll, vl::rvll ->
      fixed_add_out_permut_list permut rbarll rvll (fixed_add_out_permut permut barl vl p)
  | _ -> Parsing_helper.internal_error "barll and vll should have the same length in Proswapper.fixed_add_out_permut_list"

(* [fixed_sync permut barriers] returns [chi(barriers)]
   for the function [chi] defined in the paper and the permutation [permut]. *)

let rec fixed_synch permut = function
    [] -> Nil
  | partition_barr::rest_barr ->
      let vars = List.map (List.map (fun _ ->
	Terms.new_var Param.def_var_name Param.bitstring_type)) partition_barr
      in
      add_in_list partition_barr vars
	(fixed_add_out_permut_list permut partition_barr vars
	   (fixed_synch permut rest_barr))

(* The main proswapper function:
   [compile_barriers_equiv next_f p] calls [next_f] on each process obtained by
   compiling the barriers in [p], with swapping. *)

let compile_barriers_equiv next_f p =
  let pann = annotate p in
  (* For debugging: *)
  print_string "Annotated process:\n";
  Display.Text.display_process "" pann;
  let pcomp = compile pann in
  let barr = barriers [] pann in
  let sorted_barr = List.sort compare_barriers barr in
  let bar_partition = compute_partitions sorted_barr in
  display_partitions bar_partition;
  Display.Text.print_string ("There are " ^ (string_of_int (count_permuts_parts bar_partition)) ^ " possible swappings.\n");
  match !Param.set_swapping with
    Some sext ->
      (* Permutation fixed in the input file *)
      let permut = string_to_permut sext in
      next_f (Par(pcomp, fixed_synch permut bar_partition))
  | None ->
      if !Param.interactive_swapping then
	(* Ask the user for the permutations he wants to try *)
	let rec interactive_swap() =
	  print_string "Please choose the permutation you would like to try:\n";
	  print_string ("(Format: t1 -> t2 -> ... -> tn; t1' -> t2' -> ...; ...\n" ^
			"meaning that t1 has image t2, t2 has image t3, ..., tn has image t1,\n" ^
			"and similarly for t1' -> t2' -> ..., and so on.\n" ^
			"Enter stop to stop ProVerif.)\n");
	  let s = read_line () in
	  if s = "stop" then exit 0 else
	  let permut = string_to_permut (s, Parsing_helper.dummy_ext) in
	  next_f (Par(pcomp, fixed_synch permut bar_partition));
	  interactive_swap()
	in
	interactive_swap()
      else
	(* Try all permutations *)
	synch (fun psync -> next_f (Par(pcomp, psync))) bar_partition

(**** Compilation of barriers "sync" for correspondence assertions.
    That is much easier: no need to swap terms ****)

(* [annotate p] transforms all barriers in [p] into
   annotated barriers, and returns the resulting process.
   It also checks that no barriers occur under replication. *)

let rec annotate = function
    Nil -> Nil
  | NamedProcess(s, tl, p) ->
      NamedProcess(s, tl, annotate p)
  | Par(p1,p2) -> Par(annotate p1, annotate p2)
  | Repl(p,occ) ->
      (* Barriers should not occur under replication *)
      check_no_barrier p; Repl(p, occ)
  | Restr(f,args,p,occ) -> Restr(f,args, annotate p, occ)
  | Test(t,p1,p2,occ) -> Test(t,annotate p1, annotate p2, occ)
  | Input(t,pat,p,occ) -> Input(t,pat,annotate p, occ)
  | Output(t1,t2,p,occ) -> Output(t1,t2,annotate p, occ)
  | Let(pat,t,p1,p2,occ) -> Let(pat,t,annotate p1, annotate p2, occ)
  | Insert(t,p,occ) -> Insert(t,annotate p,occ)
  | Get(pat,t,p1,p2,occ) -> Get(pat,t,annotate p1,annotate p2,occ)
  | Event(t,args,p,occ) -> Event(t,args,annotate p,occ)
  | LetFilter(l,f,p1,p2,occ) -> LetFilter(l,f,annotate p1, annotate p2, occ)
  | Phase _ ->
      Parsing_helper.user_error "Phases are incompatible with sync."
  | Barrier(n,tag,p,occ) ->
      let a = Terms.create_name "@a" (Terms.fresh_id "a") ([],Param.channel_type) true in
      let c = Terms.create_name "@c" (Terms.fresh_id "c") ([],Param.channel_type) true in
      additional_channel_names := a::c::(!additional_channel_names);
      let tag' =
	match tag with
	  None -> Terms.fresh_id "@"
	| Some s -> s
      in
      AnnBarrier(n,tag',a,c,[],annotate p,occ)
  | AnnBarrier _ ->
      Parsing_helper.internal_error "Annotated barriers should not occur in annotate"

(* [synch next_f barriers] calls [next_f p] for each process [p] in [chi(barriers)]
   for the function [chi] defined in the paper. *)

let rec synch = function
    [] -> Nil
  | barr ->
      let first_barr, rest_barr = get_min [] barr in
      let empty_tuple = Terms.get_tuple_fun [] in
      let prest = synch rest_barr in
      let pout =
	List.fold_left (fun p (_,_,_,c,_,_) ->
	  Output(FunApp(c,[]), FunApp(empty_tuple, []), p, Terms.new_occurrence())) prest first_barr
      in
      List.fold_left (fun p (_,_,a,_,_,_) ->
	Input(FunApp(a,[]), PatTuple(empty_tuple, []), p, Terms.new_occurrence())) pout first_barr

(* The main compilation function for barriers for correspondence assertions:
   [compile_barriers p] returns the process obtained by
   compiling the barriers in [p], without swapping. *)

let compile_barriers_corresp p =
  let pann = annotate p in
  (* For debugging: *)
  print_string "Annotated process:\n";
  Display.Text.display_process "" pann;
  let pcomp = compile pann in
  let barr = barriers [] pann in
  let sorted_barr = List.sort compare_barriers barr in
  Par(pcomp, synch sorted_barr)

let reset() =
  seen_tags := [];
  all_tags := [];
  additional_channel_names := []

open Pitypes
                                
let compile_barriers next_f pi_state =
  reset();
  begin
    match pi_state.pi_process_query with
    | SingleProcessSingleQuery(p, q) ->
       begin
         match q with
         | CorrespQuery _ | CorrespQEnc _ | NonInterfQuery _ | WeakSecret _ ->
            next_f
              { pi_state with
                pi_process_query = SingleProcessSingleQuery(compile_barriers_corresp p, q);
                pi_freenames = List.rev_append (!additional_channel_names) pi_state.pi_freenames
              }
         | ChoiceQuery | ChoiceQEnc _ ->
            compile_barriers_equiv (fun p' ->
                next_f
                { pi_state with
                  pi_process_query = SingleProcessSingleQuery(p', q);
                  pi_freenames = List.rev_append (!additional_channel_names) pi_state.pi_freenames
                }
              ) p
         | QueryToTranslate _ ->
            Parsing_helper.internal_error "queries should be translated before compiling barriers"
       end
    | SingleProcess(p,ql) ->
       next_f
         { pi_state with
           pi_process_query = SingleProcess(compile_barriers_corresp p, ql);
           pi_freenames = List.rev_append (!additional_channel_names) pi_state.pi_freenames
         }
    | Equivalence _ ->
       Parsing_helper.user_error "When showing equivalence of two processes, the processes cannot contain sync"
  end;
  reset()
