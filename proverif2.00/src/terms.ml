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

(* [ends_with s sub] is true when the string [s] ends with [sub] *)

let ends_with s sub =
  let l_s = String.length s in
  let l_sub = String.length sub in
  (l_s >= l_sub) && (String.sub s (l_s - l_sub) l_sub = sub)

(* [starts_with s sub] is true when the string [s] starts with [sub] *)

let starts_with s sub =
  let l_s = String.length s in
  let l_sub = String.length sub in
  (l_s >= l_sub) && (String.sub s 0 l_sub = sub)
    
(* TO DO The current code works, but in principle, 
   it would be nicer if [tuple_taple] was a field in
   [t_pi_state/t_horn_state], to avoid keeping tuple
   functions when they are no longer useful. 
   That would probably complicate the code, however. *)
let tuple_table = Hashtbl.create 1

let get_tuple_fun tl =
  let tl =
    if Param.get_ignore_types() then
      List.map (fun t -> Param.any_type) tl
    else
      tl
  in
  try
    Hashtbl.find tuple_table tl
  with Not_found ->
    let r = { f_orig_name = "";
              f_name = "";
              f_type = tl, Param.bitstring_type;
              f_cat = Tuple;
              f_initial_cat = Tuple;
              f_private = false;
	      f_options = 0 }
    in
    Hashtbl.add tuple_table tl r;
    r

let get_term_type = function
    Var b -> b.btype
  | FunApp(f,_) -> snd f.f_type

let equal_types t1 t2 =
  (Param.get_ignore_types()) || t1 == t2

(* Get the type of a pattern *)

let get_pat_type = function
    PatVar b -> b.btype
  | PatTuple (f,l) -> snd f.f_type
  | PatEqual t -> get_term_type t

let get_format_type = function
    FVar b -> b.btype
  | FAny b -> b.btype
  | FFunApp(f,_) -> snd f.f_type

let term_of_pattern_variable = function
  | PatVar(v) -> Var(v)
  | _ -> internal_error "[term_of_pattern_variable] The pattern must be a variable"

let rec copy_n n v =
  if n <= 0 then [] else v :: (copy_n (n-1) v)

let rec tl_to_string sep = function
    [] -> ""
  | [a] -> a.tname
  | (a::l) -> a.tname ^ sep ^ (tl_to_string sep l)

let rec eq_lists l1 l2 =
  match l1,l2 with
    [],[] -> true
  | a1::q1,a2::q2 -> (a1 == a2) && (eq_lists q1 q2)
  | _,_ -> false

(* These functions are used to guarantee the freshness of new identifiers
   Each identifier is represented by a pair (s,n):
   - if n = 0, then (s,n) is displayed s
   - otherwise, (s,n) is displayed s_n
   Invariant: n has at most 9 digits (supports one billion of variables);
   when n = 0, s is never of the form N_xxx where xxx is a non-zero
   number of at most 9 digits.
   This guarantees that for each identifier, (s,n) is unique.
   We guarantee the freshness by changing the value of n
*)

(* [get_id_n s] converts [s] into a pair [(s',n)] displayed [s] *)

let get_id_n s =
  let l = String.length s in
  if '0' <= s.[l-1] && s.[l-1] <= '9' then
    let rec underscore_number n =
      if (n > 0) && (l-n<=10) then
        if s.[n] = '_' then n
        else if '0' <= s.[n] && s.[n] <= '9' then underscore_number (n-1) else
				raise Not_found
						else
				raise Not_found
    in
    try
      let pos_underscore = underscore_number (l-2) in
      if s.[pos_underscore+1] = '0' then raise Not_found;
      let n' = int_of_string (String.sub s (pos_underscore+1) (l-pos_underscore-1)) in
      let s' = String.sub s 0 pos_underscore in
      (* print_string (s ^ " split into " ^ s' ^ "  " ^ (string_of_int n') ^ "\n"); *)
      (s',n')
    with Not_found ->
      (* s does not end with _xxx *)
      (s,0)
  else
    (s,0)

(* Counter incremented to generate fresh variable names *)
let var_idx = ref 0

(* The maximum xxx such N_xxx occurs and xxx does not come from var_idx *)
let max_source_idx = ref 0

(* Set of pairs (s,n) used, stored in a hash table.
   All pairs (_,n) where 0 < n <= !var_idx are considered as always used,
   so we need not add them to the hash table.
   All pairs (s,n) in [used_ids] satisfy [n <= !max_source_idx] *)
let used_ids = Hashtbl.create 7

(* [record_id s ext] records the identifier [s] so that it will not be reused elsewhere.
   [record_id] must be called only before calls to [fresh_id] or [new_var_name], so that
   [s] cannot collide with an identifier generated by [fresh_id] or [new_var_name].
   Moreover, !var_idx = 0, there are no pairs (_,n) with 0 < n <= !var_idx,
   so the used pairs are exactly those in the hash table used_ids. *)


(* Clear useds_ids. Used to reload a file in proverif interact mode *)
let init_used_ids () = Hashtbl.clear used_ids

let record_id s ext =
  let (_,n) as s_n = get_id_n s in
  if n > !max_source_idx then max_source_idx := n;
  if Hashtbl.mem used_ids s_n then
    input_error ("identifier " ^ s ^ " already defined (as a free name, a function, a predicate, a type, an event, or a table)") ext
  else
    Hashtbl.add used_ids s_n ()




(***************************************************
		           Function for Var
****************************************************)

(* [new_var_name s] creates a fresh pair [(s,n)] using [!var_idx]. *)

let rec new_var_name s =
  incr var_idx;
  let n = !var_idx in
  if (n <= !max_source_idx) && (Hashtbl.mem used_ids (s,n)) then
    new_var_name s
  else
    (s,n)

(* [fresh_id s] creates a fresh identifier [s'] corresponding to
   identifier [s], preferably [s] itself. If [s] is already used,
   create a fresh identifier by changing the number suffix of [s], or
   adding a number suffix to [s] if there is none, using [new_var_name] *)

let fresh_id s =
  if not (!Param.typed_frontend) then
    (* When the front-end is not typed, we do not try to reuse exactly [s];
       free names may be discovered after some bound names in the untyped
       front-end, so we do not know when we could use a bound name without
       renaming. *)
    let (s',n') = new_var_name s in
    s' ^ "_" ^ (string_of_int n')
  else
  let ((s',n) as s_n) = get_id_n s in
  if ((n != 0) && (n <= !var_idx)) || (Hashtbl.mem used_ids s_n) then
    let (s',n') = new_var_name s' in
    s' ^ "_" ^ (string_of_int n')
  else
    begin
      if n > !max_source_idx then max_source_idx := n;
      Hashtbl.add used_ids s_n ();
      s
    end

(* [fresh_id_keep_s s] creates a fresh pair [(s,n)] corresponding to
   identifier [s], preferably the pair [(s,0)], which displays exactly as [s],
   if possible, that is, if [s] does not end with _number and this pair is
   not already used. Otherwise, create a fresh pair using [new_var_name] *)

let fresh_id_keep_s s =
  if not (!Param.typed_frontend) then
    (* When the front-end is not typed, we do not try to reuse exactly [s];
       free names may be discovered after some bound names in the untyped
       front-end, so we do not know when we could use a bound name without
       renaming. *)
    new_var_name s
  else
  let ((s',n) as s_n) = get_id_n s in
  if (n != 0) || (Hashtbl.mem used_ids s_n) then 
    new_var_name s
  else
    begin
      (* n = 0, so no need to increase max_source_idx, it is already >= n *)
      Hashtbl.add used_ids s_n ();
      s_n
    end


(* [new_var s t] creates a fresh variable with name [s] and type [t] *)

let new_var s t =
  let (s',n) = fresh_id_keep_s s in
  { v_orig_name = s;
    sname = s'; vname = n; unfailing = false; btype = t; link = NoLink }

(* [new_var s t] creates a fresh variable with name [s] and type [t] *)

let new_unfailing_var s t =
  let s_mfail = if s = "" then "@mayfail" else "@mayfail_" ^ s in
  let (s',n) = fresh_id_keep_s s_mfail in
  { v_orig_name = s;
    sname = s'; vname = n; unfailing = true; btype = t; link = NoLink }

(* [new_var_noren s t] creates a fresh variable with name [s] and type [t]
   The name of this variable is exactly [s], without renaming it to
   a fresh name even if s is already used. Such variables should never
   be displayed. *)

let new_var_noren s t =
  { v_orig_name = s;
    sname = s; vname = -1; unfailing = false; btype = t;  link = NoLink }

(* [new_var_noren_with_fail s t may_fail] creates a fresh variable with
   name [s], type [t], and may_fail value [may_fail].
   The name of this variable is exactly [s], without renaming it to
   a fresh name even if s is already used. Such variables should never
   be displayed. *)

let new_var_noren_with_fail s t may_fail =
  { v_orig_name = s;
    sname = s; vname = -1; unfailing = may_fail; btype = t;  link = NoLink }

(* [copy_var v] creates a fresh variable with the same sname and type as [v]
   Invariant: if vname = 0, then sname never contains N_xxx where xxx is a non-zero
   number of at most 9 digits. As a consequence, we don't need to split v.sname
   using fresh_id_n. *)

let copy_var v =
  let (s',n) = new_var_name v.sname in
  { v_orig_name = v.v_orig_name;
    sname = s'; vname = n; unfailing = v.unfailing;
    btype = v.btype; link = NoLink }

(* [copy_var_noren v] creates a fresh variable with the same name and type
   as [v]. The name is exactly the same as [v], without renaming to a fresh
   name. *)

let copy_var_noren v =
  { v_orig_name = v.v_orig_name;
    sname = v.sname; vname = v.vname; unfailing = v.unfailing;
    btype = v.btype; link = NoLink }

(* [new_var_def t] creates a fresh variable with a default name and type [t] *)
let new_var_def t =
  Var (new_var Param.def_var_name t)

let new_unfailing_var_def t =
  Var (new_unfailing_var "" t)

(* [val_gen tl] creates new variables of types [tl] and returns them in a
   list *)
let var_gen tl = List.map new_var_def tl

(* [occurs_var v t] determines whether the variable [v] occurs in the term [t] *)

let rec occurs_var v = function
    Var v' -> v == v'
  | FunApp(f,l) -> List.exists (occurs_var v) l

let occurs_var_fact v = function
    Pred(_,l) -> List.exists (occurs_var v) l
  | Out (t, bt_list) -> List.exists (fun (_,t) -> occurs_var v t) bt_list || occurs_var v t

(* [occurs_f f t] determines whether the function symbol [f] occurs in the term [t] *)

let rec occurs_f f = function
    Var _ -> false
  | FunApp(f',l) ->
      (f == f') || (List.exists (occurs_f f) l)

let rec occurs_f_pat f = function
    PatVar v -> false
  | PatTuple (_,l) -> List.exists (occurs_f_pat f) l
  | PatEqual t -> occurs_f f t

let occurs_f_fact f = function
    Pred(_,l) -> List.exists (occurs_f f) l
  | Out(t, l) ->
      (occurs_f f t) ||
      (List.exists(fun (_,t) -> occurs_f f t) l)

let is_may_fail_term = function
  | FunApp(f,[]) when f.f_cat = Failure -> true
  | Var(v) when v.unfailing -> true
  | _ -> false

let is_unfailing_var = function
  | Var(v) when v.unfailing -> true
  | _ -> false

let is_failure = function
  | FunApp(f,[]) when f.f_cat = Failure -> true
  | _ -> false

(* Equality tests *)

let rec equal_terms t1 t2 = match (t1,t2) with
   | (FunApp(f1,l1), FunApp(f2,l2)) ->
        (f1 == f2) && (List.for_all2 equal_terms l1 l2)
   | (Var v1, Var v2) -> v1 == v2
   | (_,_) -> false

let equals_term_pair (v, t) (v', t') = (v == v') && (equal_terms t t')

let equal_facts f1 f2 =
  match (f1,f2) with
    Pred(chann1, t1),Pred(chann2, t2) ->
      (chann1 == chann2) && (List.for_all2 equal_terms t1 t2)
  | Out(t1,l1),Out(t2,l2) ->
      (equal_terms t1 t2) && (List.length l1 = List.length l2)
	&& (List.for_all2 equals_term_pair l1 l2)
  | _ -> false

let equals_simple_constraint c1 c2 =
  match (c1,c2) with
    (Neq(t1, t2), Neq(t1', t2')) -> (equal_terms t1 t1') && (equal_terms t2 t2')

(* Copy and cleanup *)

let current_bound_vars = ref []

let link v l =
  (* Check that message variables are linked only to messages,
     not to fail or to may-fail variables *)
  if not v.unfailing then
    begin
      match l with
	VLink v' -> assert (not v'.unfailing)
      |	TLink t ->
	  begin
	    match t with
	      Var v' -> assert (not v'.unfailing)
	    | FunApp(f, _) -> assert (f.f_cat != Failure)
	  end
      |	TLink2 _ ->
	  (* TLink2 is not used with function link *)
	  assert false
      |	NoLink ->
	  (* NoLink should not be used with function link,
	     it is set by cleanup *)
	  assert false
      |	FLink _ | PGLink _ -> ()
    end;
  (* Check that types are correct, when they are not ignored *)
  begin
    match l with
      VLink v' -> assert (equal_types v.btype v'.btype)
    | TLink t -> assert (equal_types v.btype (get_term_type t))
    | _ -> ()
  end;
  current_bound_vars := v :: (!current_bound_vars);
  v.link <- l

let link_var t l = match t with
  |Var(v) -> link v l
  |_ -> internal_error "[link_var] The term must be a variable"

let cleanup () =
  List.iter (fun v -> v.link <- NoLink) (!current_bound_vars);
  current_bound_vars := []

let auto_cleanup f =
  let tmp_bound_vars = !current_bound_vars in
  current_bound_vars := [];
  try
    let r = f () in
    List.iter (fun v -> v.link <- NoLink) (!current_bound_vars);
    current_bound_vars := tmp_bound_vars;
    r
  with x ->
    List.iter (fun v -> v.link <- NoLink) (!current_bound_vars);
    current_bound_vars := tmp_bound_vars;
    raise x

(* We could also define the following functions instead of cleanup:

let in_auto_cleanup = ref false

let link v l =
  if not (!in_auto_cleanup) then
    Parsing_helper.internal_error "should be in auto_cleanup to use link";
  current_bound_vars := v :: (!current_bound_vars);
  v.link <- l

let auto_cleanup f =
  let tmp_in_auto_cleanup = !in_auto_cleanup in
  in_auto_cleanup := true;
  let tmp_bound_vars = !current_bound_vars in
  current_bound_vars := [];
  try
    let r = f () in
    List.iter (fun v -> v.link <- NoLink) (!current_bound_vars);
    current_bound_vars := tmp_bound_vars;
    in_auto_cleanup := tmp_in_auto_cleanup;
    r
  with x ->
    List.iter (fun v -> v.link <- NoLink) (!current_bound_vars);
    current_bound_vars := tmp_bound_vars;
    in_auto_cleanup := tmp_in_auto_cleanup;
    raise x

Use
   auto_cleanup (fun () -> ...)
instead of
   let tmp_bound_vars = !current_bound_vars in
   current_bound_vars := [];
   ...
   cleanup();
   current_bound_vars := tmp_bound_vars
and of
   if !current_bound_vars != [] then
      Parsing_helper.internal_error "...";
   ...
   cleanup()
This would be a better programming style, but this conflicts
with the way the function Rules.build_rules_eq is written...
and would probably also slow down a bit the system.

*)

(***************************************************
   Functions for General Variables
****************************************************)

let gen_var_counter = ref 0

let new_gen_var t may_fail =
  incr gen_var_counter;
  let f_cat = if may_fail then General_mayfail_var else General_var in
  let name = (if !Param.tulafale != 1 then "@gen" else "gen") ^
               (if may_fail then "mf" else "") ^
                 (string_of_int (!gen_var_counter))
  in
  { f_orig_name = name;
    f_name = name;
    f_type = [], t;
    f_cat = f_cat;
    f_initial_cat = f_cat;
    f_private = true;
    f_options = 0 }

let rec generalize_vars_not_in vlist = function
    Var v ->
      begin
	if List.memq v vlist then Var v else
	match v.link with
	| NoLink ->
	    let v' = FunApp(new_gen_var v.btype v.unfailing, []) in
	    link v (TLink v');
	    v'
	| TLink l -> l
	| _ -> internal_error "Unexpected link in generalize_vars"
      end
  | FunApp(f, l) ->
      FunApp(f, List.map (generalize_vars_not_in vlist) l)

let rec generalize_vars_in vlist = function
    Var v ->
      begin
	if not (List.memq v vlist) then Var v else
	match v.link with
	  NoLink ->
	    let v' = FunApp(new_gen_var v.btype v.unfailing, []) in
	    link v (TLink v');
	    v'
	| TLink l -> l
	| _ -> internal_error "Unexpected link in generalize_vars"
      end
  | FunApp(f, l) ->
      FunApp(f, List.map (generalize_vars_in vlist) l)


(***************************************************
	      Copy term functions
****************************************************)

let rec copy_term = function
  | FunApp(f,l) -> FunApp(f, List.map copy_term l)
  | Var v ->
      match v.link with
	NoLink ->
	  let r = copy_var v in
	  link v (VLink r);
	  Var r
      | VLink l -> Var l
      | _ -> internal_error "Unexpected link in copy_term"

let copy_term_pair = fun (v,t) -> (v, copy_term t)

let copy_fact = function
    Pred(chann, t) -> Pred(chann, List.map copy_term t)
  | Out(t, l) -> Out(copy_term t, List.map copy_term_pair l)

let copy_constra c = List.map (function
      Neq(t1,t2) -> Neq(copy_term t1, copy_term t2)) c

let copy_rule (hyp,concl,hist,constra) =
  let tmp_bound = !current_bound_vars in
  current_bound_vars := [];
  let r = (List.map copy_fact hyp, copy_fact concl, hist, List.map copy_constra constra) in
  cleanup();
  current_bound_vars := tmp_bound;
  r

let copy_red (left_list, right, side_c) =
  assert (!current_bound_vars == []);
  let left_list' = List.map copy_term left_list in
  let right' = copy_term right in
  let side_c' = List.map (function (t1,t2) ->
  	copy_term t1, copy_term t2) side_c in
  cleanup();
  (left_list', right', side_c')

(* Unification *)

exception Unify

let rec occur_check v t =
  match t with
    Var v' ->
      begin
        if v == v' then raise Unify;
        match v'.link with
          NoLink -> ()
        | TLink t' -> occur_check v t'
        | _ -> internal_error "unexpected link in occur_check"
      end
  | (FunApp(_,l)) -> List.iter (occur_check v) l

let term_string = function
    FunApp(f,l) -> if l = [] then f.f_name else f.f_name ^ "(...)"
  | Var(b) -> b.sname ^ "_" ^ (string_of_int b.vname)

let unify t1 t2 =
  (* Printf.printf "Unifying %s with %s\n" (term_string t1) (term_string t2); *)
  let rec aux t1 t2 =
    (* Commented out this typing checking test for speed
       if not (Param.get_ignore_types()) then
       begin
       if get_term_type t1 != get_term_type t2 then
        Parsing_helper.internal_error
       ("Type error in unify: " ^
       (term_string t1) ^ " has type " ^ (get_term_type t1).tname ^
       " while " ^
       (term_string t2) ^ " has type " ^ (get_term_type t2).tname)
       end; *)
    match (t1,t2) with
      (Var v, Var v') when v == v' -> ()
    | (Var v, _) ->
      begin
        match v.link with
        | NoLink ->
          begin
            match t2 with
            | Var {link = TLink t2'} -> aux t1 t2'
            | Var v' when v.unfailing ->
              link v (TLink t2)
            | Var v' when v'.unfailing ->
              link v' (TLink t1)
            | FunApp (f_symb,_) when f_symb.f_cat = Failure && v.unfailing = false -> raise Unify
            | Var v' when v'.sname = Param.def_var_name ->
              link v' (TLink t1)
            | _ ->
              occur_check v t2;
              link v (TLink t2)
          end
        | TLink t1' -> aux t1' t2
        | _ -> internal_error "Unexpected link in unify 1"
      end
    | (FunApp(f_symb,_), Var v) ->
      begin
        match v.link with
          NoLink ->
          if v.unfailing = false && f_symb.f_cat = Failure
          then raise Unify
          else
            begin
              occur_check v t1;
              link v (TLink t1)
            end
        | TLink t2' -> aux t1 t2'
        | _ -> internal_error "Unexpected link in unify 2"
      end
    | (FunApp(f1, l1), FunApp(f2,l2)) ->
      if f1 != f2 then raise Unify;
      List.iter2 aux l1 l2
  in
  (* try *)
    aux t1 t2
  (* with
   *   Unify -> () *)

let rec skip n l =
  if n = 0 then l else
  match l with
    (a::l) -> skip (n-1) l
  | [] -> internal_error "skip error"

let unify_facts f1 f2 =
  match (f1,f2) with
    Pred(chann1, t1),Pred(chann2,t2) ->
      if chann1 != chann2 then raise Unify;
      List.iter2 unify t1 t2
  | Out(t1,l1),Out(t2,l2) ->
      unify t1 t2;
      (* Warning: this might be a bit insecure?
	 if List.length l1 != List.length l2 then raise Unify; *)
      let len1 = List.length l1 in
      let len2 = List.length l2 in
      if len2 < len1 then
	begin
	  let l1 = skip (len1-len2) l1 in
	  List.iter2 (fun (v1,t1) (v2,t2) ->
	    if v1 != v2 then raise Unify;
	    unify t1 t2) l1 l2
	end
      else
	begin
	  let l2 = skip (len2-len1) l2 in
	  List.iter2 (fun (v1,t1) (v2,t2) ->
	    if v1 != v2 then raise Unify;
	    unify t1 t2) l1 l2
	end
  | _ -> raise Unify


let rec copy_term2 = function
  | FunApp(f,l) -> FunApp(f, List.map copy_term2 l)
  | Var v ->
      match v.link with
	| NoLink ->
	    let r = copy_var v in
	    link v (VLink r);
	    Var r
	| TLink l -> copy_term2 l
	| VLink r -> Var r
	| _ -> internal_error "unexpected link in copy_term2"

let copy_term2_pair = fun (v,t) -> (v, copy_term2 t)

let copy_fact2 = function
    Pred(chann, t) -> Pred(chann, List.map copy_term2 t)
  | Out(t,l) -> Out(copy_term2 t, List.map copy_term2_pair l)

let rec copy_constra2 c = List.map (function
      Neq(t1,t2) -> Neq(copy_term2 t1, copy_term2 t2)) c

let copy_rule2 (hyp, concl, hist, constra) =
	let tmp_bound = !current_bound_vars in
  current_bound_vars := [];
  let r = (List.map copy_fact2 hyp, copy_fact2 concl, hist, List.map copy_constra2 constra) in
  cleanup();
  current_bound_vars := tmp_bound;
  r

(* Matching *)

exception NoMatch

let rec match_terms t1 t2 =
  (* Commented out this typing checking test for speed
  if not (Param.get_ignore_types()) then
  begin
    if get_term_type t1 != get_term_type t2 then
      Parsing_helper.internal_error
	("Type error in match_terms: " ^
	 (term_string t1) ^ " has type " ^ (get_term_type t1).tname ^
	 " while " ^
	 (term_string t2) ^ " has type " ^ (get_term_type t2).tname)
  end; *)
   match (t1,t2) with
     (Var v), t ->
       begin
	 match v.link with
           NoLink ->
             if v.unfailing
             then link v (TLink t)
             else
	       begin
	       	 match t with
	           | Var v' when v'.unfailing -> raise NoMatch
	           | FunApp(f_symb,_) when f_symb.f_cat = Failure -> raise NoMatch
	           | _ -> link v (TLink t)
	       end
         | TLink t' -> if not (equal_terms t t') then raise NoMatch
	 | _ -> internal_error "Bad link in match_terms"
       end
   | (FunApp (f1,l1')), (FunApp (f2,l2')) ->
       if f1 != f2 then raise NoMatch;
       List.iter2 match_terms l1' l2'
   | _,_ -> raise NoMatch

let match_facts f1 f2 =
  match (f1,f2) with
    Pred(chann1, t1),Pred(chann2, t2) ->
      if chann1 != chann2 then raise NoMatch;
      List.iter2 match_terms t1 t2
  | Out(t1,l1),Out(t2,l2) ->
      match_terms t1 t2;
      let len1 = List.length l1 in
      let len2 = List.length l2 in
      if len2 < len1 then raise NoMatch;
      let l2 = skip (len2-len1) l2 in
      List.iter2 (fun (v1,t1) (v2,t2) ->
	if v1 != v2 then raise NoMatch;
	match_terms t1 t2) l1 l2
  | _ -> raise NoMatch

let matchafact finst fgen =
  assert (!current_bound_vars == []);
  try
    match_facts fgen finst;
    cleanup();
    true
  with NoMatch ->
    cleanup();
    false

(* [occurs_test_loop seen_vars v t] returns true when
   variable [v] occurs in term [t], following links
   inside terms. It uses the list [seen_vars] to avoid
   loops. [seen_vars] should be initialized to [ref []]. *)

let rec occurs_test_loop seen_vars v t =
   match t with
     Var v' ->
       begin
	 if List.memq v' (!seen_vars) then false else
	 begin
	   seen_vars := v' :: (!seen_vars);
           if v == v' then true else
           match v'.link with
             NoLink -> false
           | TLink t' -> occurs_test_loop seen_vars v t'
           | _ -> internal_error "unexpected link in occur_check"
         end
       end
   | FunApp(_,l) -> List.exists (occurs_test_loop seen_vars v) l

let matchafactstrict finst fgen =
  assert (!current_bound_vars == []);
  try
    match_facts fgen finst;
    (* If a variable v is instantiated in the match into
       a term that is not a variable and that contains v, then
       by repeated resolution, the term will be instantiated into
       an infinite number of different terms obtained by
       iterating the substitution. We should adjust the selection
       function to avoid this non-termination. *)
    if List.exists (fun v -> match v.link with
    | TLink (Var _) -> false
    | TLink t -> occurs_test_loop (ref []) v t
    | _ -> false) (!current_bound_vars) then
      begin
	cleanup();
	true
      end
    else
      begin
	cleanup();
	false
      end
  with NoMatch ->
    cleanup();
    false


(* Size *)

let rec term_size = function
    Var _ -> 0
  | FunApp(f, l) -> 1 + term_list_size l

and term_list_size = function
    [] -> 0
  | a::l -> term_size a + term_list_size l

let rec term_pair_list_size = function
    [] -> 0
  | (v,t)::l -> 1 + term_size t + term_pair_list_size l

let fact_size = function
    Pred(_, tl) -> 1 + term_list_size tl
  | Out(t,l) -> term_size t + term_pair_list_size l



(* [replace_f_var vl t] replaces names in t according to
   the association list vl. That is, vl is a reference to a list of pairs
   (f_i, v_i) where f_i is a (nullary) function symbol and
   v_i is a variable. Each f_i is replaced with v_i in t.
   If an f_i in general_vars occurs in t, a new entry is added
   to the association list vl, and f_i is replaced accordingly. *)

let rec replace_f_var vl = function
  | Var v2 -> Var v2
  | FunApp(f2,[]) ->
      begin
	try
	  Var (List.assq f2 (!vl))
	with Not_found ->
	  if f2.f_cat = General_var then
	    begin
	      let v = new_var f2.f_orig_name (snd f2.f_type) in
	      vl := (f2, v) :: (!vl);
	      Var v
	    end
	  else if f2.f_cat = General_mayfail_var then
	    begin
	      let v = new_unfailing_var f2.f_orig_name (snd f2.f_type) in
	      vl := (f2, v) :: (!vl);
	      Var v
	    end
	  else
	    FunApp(f2,[])
      end
  | FunApp(f2,l) -> FunApp(f2, List.map (replace_f_var vl) l)

(* [rev_assoc v2 vl] looks for v2 in the association list vl.
   That is, vl is a list of pairs (f_i, v_i) where f_i is a
   (nullary) function symbol and v_i is a variable.
   If v2 is a v_i, then it returns f_i[],
   otherwise it returns v2 unchanged. *)

let rec rev_assoc v2 = function
    [] -> Var v2
  | ((f,v)::l) -> if v2 == v then FunApp(f,[]) else rev_assoc v2 l

(* [follow_link var_case t] follows links stored in variables in t
   and returns the resulting term. Variables are translated
   by the function [var_case] *)

let rec follow_link var_case = function
    Var v ->
      begin
	match v.link with
	  TLink t -> follow_link var_case t
	| NoLink -> var_case v
	| _ -> Parsing_helper.internal_error "unexpected link in follow_link"
      end
  | FunApp(f,l) -> FunApp(f, List.map (follow_link var_case) l)

(* [replace name f t t'] replaces all occurrences of the name f (ie f[]) with t
   in t' *)

let rec replace_name f t = function
    Var v -> Var v
  | FunApp(f',[]) -> if f' == f then t else FunApp(f',[])
  | FunApp(f',l') -> FunApp(f', List.map (replace_name f t) l')

(* Return true when the term contains a variable *)

let rec has_vars = function
    Var _ -> true
  | FunApp(f, l) -> List.exists has_vars l

(* List of variables *)

let rec get_vars vlist = function
    Var v -> if not (List.memq v (!vlist)) then vlist := v :: (!vlist)
  | FunApp(_,l) ->
      List.iter (get_vars vlist) l

let get_vars_constra vlist = function
    Neq(t1,t2) -> get_vars vlist t1;
      get_vars vlist t2

let get_vars_fact vlist = function
    Pred(_,l) -> List.iter (get_vars vlist) l
  | Out(t,l) ->
      get_vars vlist t;
      List.iter(fun (_,t') -> get_vars vlist t') l

let rec get_vars_pat accu = function
    PatVar b -> b::accu
  | PatTuple(f,l) -> List.fold_left get_vars_pat accu l
  | PatEqual t -> accu
	
(* Copy of terms and constraints after matching *)

let rec copy_term3 = function
 | FunApp(f,l) -> FunApp(f, List.map copy_term3 l)
 | Var v -> match v.link with
     NoLink -> Var v
   | TLink l -> l
   | _ -> internal_error "unexpected link in copy_term3"

let copy_fact3 = function
    Pred(p,l) -> Pred(p, List.map copy_term3 l)
  | Out(t,l) -> Out(copy_term3 t, List.map (fun (x,t') -> (x, copy_term3 t')) l)

let rec copy_constra3 c = List.map (function
  | Neq(t1,t2) -> Neq(copy_term3 t1, copy_term3 t2)
	)c

(* [copy_term4] follows links [Tlink] recursively,
   but does not rename variables *)

let rec copy_term4 = function
 | FunApp(f,l) -> FunApp(f, List.map copy_term4 l)
 | Var v -> match v.link with
     NoLink -> Var v
   | TLink l -> copy_term4 l
   | _ -> internal_error "unexpected link in copy_term4"

(* Do not select Out facts, blocking facts, or pred_TUPLE(vars) *)

let is_var = function
    Var _ -> true
  | _ -> false

let unsel_set = ref ([] : fact list)
let add_unsel f =
  unsel_set := f :: (!unsel_set)

let is_unselectable = function
    Pred(p,pl) as f ->
      (p.p_prop land Param.pred_BLOCKING != 0) ||
      (p.p_prop land Param.pred_TUPLE != 0 &&
       p.p_prop land Param.pred_TUPLE_SELECT = 0 &&
       List.for_all is_var pl) ||
      (List.exists (function f' ->
	try
	  auto_cleanup (fun () ->
	    unify_facts f f');
	  true
	with Unify ->
	  false
	    ) (!unsel_set))
  | Out _ -> true

(* Helper functions for decomposition of tuples *)

let rec reorganize_list l =
  let rec get_first = function
      [] -> ([], [])
    | (a ::l)::l' ->
	let (firstl, rest) = get_first l' in
	(a :: firstl, l :: rest)
    | [] :: _ -> internal_error "unexpected case in reorganize_list"
  in
  match l with
    [] :: _ -> []
  | _ ->
      let (firstl, rest) = get_first l in
      firstl :: (reorganize_list rest)

let fun_app f = function
    FunApp(f',l) when f == f' -> l
  | _ -> raise Not_found

let reorganize_fun_app f l0 =
  reorganize_list (List.map (fun_app f) l0)

(*********************************************
      Definition of several functions
**********************************************)

(* Choice *)

let make_choice t1 t2 =
  let ty1 = get_term_type t1
  and ty2 = get_term_type t2 in
  if (Param.get_ignore_types()) || (ty1 == ty2) then
    FunApp(Param.choice_fun ty1, [t1;t2])
  else
    Parsing_helper.internal_error "[Terms.make_choice] This should be the same type"

(* Failure Constants *)

let get_fail_symb =
  Param.memo_type (fun ty ->
      let name = "fail-"^ty.tname in
      { f_orig_name = name;
        f_name = name;
        f_type = [], ty;
        f_cat = Failure;
        f_initial_cat = Failure;
        f_private = false;
        f_options = 0
    })

let get_fail_term ty = FunApp(get_fail_symb ty, [])

let fail_bool() = get_fail_term Param.bool_type
    (* fail_bool must be recomputed once Param.ignore_types is correctly set *)

(* Boolean Constants *)

let true_cst =
  { f_orig_name = "true";
    f_name = "true";
    f_type = [], Param.bool_type;
    f_cat = Tuple;
    f_initial_cat = Tuple;
    f_private = false;
    f_options = 0 }

let false_cst =
  { f_orig_name = "false";
    f_name = "false";
    f_type = [], Param.bool_type;
    f_cat = Tuple;
    f_initial_cat = Tuple;
    f_private = false;
    f_options = 0 }

let true_term = FunApp(true_cst, [])
let false_term = FunApp(false_cst, [])

(* is_true destructor: returns true when its argument is true,
   fails otherwise *)

let is_true_ref = ref None
let is_true_fun() =
  match !is_true_ref with
    Some f -> f
  | None ->
  let x = new_var_def Param.bool_type in

  let semantics = Red
    [
      [true_term], true_term, [];
      [x], fail_bool(), [(x,true_term)];
      [fail_bool()], fail_bool(), []
    ] in
  let f =
  {
    f_orig_name = "is_true";
    f_name = "is-true";
    f_type = [Param.bool_type], Param.bool_type;
    f_cat = semantics;
    f_initial_cat = semantics;
    f_private = false;
    f_options = 0
  }
  in
  is_true_ref := Some f;
  f

(* Boolean Functions *)

let equal_fun = Param.memo_type (fun ty ->
  let x = new_var_def ty
  and y = new_var_def ty
  and u = new_unfailing_var_def ty
  and fail = get_fail_term ty in

  let semantics = Red
    [
      [x;x], true_term, [];
      [x;y], false_term, [(x,y)];
      [fail;u], fail_bool(), [];
      [x;fail], fail_bool(), []
    ] in

  { f_orig_name = "=";
    f_name = "=";
    f_type = [ty;ty], Param.bool_type;
    f_cat = semantics;
    f_initial_cat = semantics;
    f_private = false;
    f_options = 0 })

let diff_fun = Param.memo_type (fun ty ->
  let x = new_var_def ty
  and y = new_var_def ty
  and u = new_unfailing_var_def ty
  and fail = get_fail_term ty in

  let semantics = Red
    [
      [x;x], false_term, [];
      [x;y], true_term, [(x,y)];
      [fail;u], fail_bool(), [];
      [x;fail], fail_bool(), []
    ] in

  { f_orig_name = "<>";
    f_name = "<>";
    f_type = [ty;ty], Param.bool_type;
    f_cat = semantics;
    f_initial_cat = semantics;
    f_private = false;
    f_options = 0 })


let and_ref = ref None
let and_fun() =
  match !and_ref with
    Some f ->f
  | None ->
  let u = new_unfailing_var_def Param.bool_type
  and x = new_var_def Param.bool_type in

  let semantics = Red
    [
    (* When the first conjunct is "false", the second conjunct is not evaluated,
       so the conjunction is "false" even if the second conjunct fails *)
      [true_term; u], u, [];
      [x;u], false_term, [(x,true_term)];
      [fail_bool(); u], fail_bool(), []
    ] in
  let f =
    { f_orig_name = "&&";
      f_name = "&&";
      f_type = [Param.bool_type; Param.bool_type], Param.bool_type;
      f_cat = semantics;
      f_initial_cat = semantics;
      f_private = false;
      f_options = 0 }
  in
  and_ref := Some f;
  f

let or_ref = ref None
let or_fun() =
  match !or_ref with
    Some f -> f
  | None ->
  let u = new_unfailing_var_def Param.bool_type
  and x = new_var_def Param.bool_type in

  let semantics = Red
    [
    (* When the first disjunct is "true", the second disjunct is not evaluated,
       so the disjunction is "true" even if the second disjunct fails *)
      [true_term; u], true_term, [];
      [x;u], u, [(x,true_term)];
      [fail_bool(); u], fail_bool(), []
    ] in
  let f =
    { f_orig_name = "||";
      f_name = "||";
      f_type = [Param.bool_type; Param.bool_type], Param.bool_type;
      f_cat = semantics;
      f_initial_cat = semantics;
      f_private = false;
      f_options = 0 }
  in
  or_ref := Some f;
  f

let not_ref = ref None
let not_fun() =
  match !not_ref with
    Some f -> f
  | None ->
  let x = new_var_def Param.bool_type in

  let semantics = Red
    [
      [true_term], false_term, [];
      [x], true_term, [(x,true_term)];
      [fail_bool()], fail_bool(), []
    ] in
  let f =
    { f_orig_name = "not";
      f_name = "not";
      f_type = [Param.bool_type], Param.bool_type;
      f_cat = semantics;
      f_initial_cat = semantics;
      f_private = false;
      f_options = 0 }
  in
  not_ref := Some f;
  f

(* [make_not a] returns the negation of the term [a] *)

let make_not a =
  let not_fun = not_fun() in
  match a with
    FunApp(f, [a']) when f == not_fun -> a'
  | _ -> FunApp(not_fun, [a])

(* [and_list l] returns the conjunction of the terms in [l] *)

let rec and_list = function
    [] -> true_term
  | [a] -> a
  | a::l -> FunApp(and_fun(), [a; and_list l])

(* [or_not_list l] returns the disjunction of the negation of the terms in [l] *)

let rec or_not_list = function
    [] -> false_term
  | [a] -> make_not a
  | a::l -> FunApp(or_fun(), [make_not a; or_not_list l])

(* The Let in else operators *)

let glet_constant_fun =
  Param.memo_type (fun ty ->
      { f_orig_name = "caught-fail";
        f_name = "caught-fail";
        f_type = [],ty;
        f_cat = Tuple;
        f_initial_cat = Tuple;
        f_private = true;
        f_options = 0
    })


let glet_constant_never_fail_fun =
  Param.memo_type (fun ty ->
      { f_orig_name = "never-fail";
        f_name = "never-fail";
        f_type = [],ty;
        f_cat = Tuple;
        f_initial_cat = Tuple;
        f_private = true;
        f_options = 0
    })

let glet_fun = Param.memo_type (fun ty ->
  let x = new_var_def ty
  and fail = get_fail_term ty
  and c_o = glet_constant_fun ty in

  let semantics = Red
    [
      [x], x, [];
      [fail], FunApp(c_o,[]), []
    ] in

  { f_orig_name = "catch-fail";
    f_name = "catch-fail";
    f_type = [ty], ty;
    f_cat = semantics;
    f_initial_cat = semantics;
    f_private = true;
    f_options = 0 })

(* The success operators *)

let success_fun = Param.memo_type (fun ty ->
  let x = new_var_def ty
  and fail = get_fail_term ty in

  let semantics = Red
    [
      [x], true_term, [];
      [fail], false_term, []
    ] in

  { f_orig_name = "success?";
    f_name = "success?";
    f_type = [ty], Param.bool_type;
    f_cat = semantics;
    f_initial_cat = semantics;
    f_private = false;
    f_options = 0 }
  )

let not_caught_fail_fun = Param.memo_type (fun ty ->
  let x = new_var_def ty
  and c_o = glet_constant_fun ty
  and fail = get_fail_term ty in

  let semantics = Red
    [
      [x], true_term, [(x,FunApp(c_o,[]))];
      [FunApp(c_o,[])], false_term, [];
      [fail], fail_bool(), []
    ] in

  { f_orig_name = "not-caught-fail";
    f_name = "not-caught-fail";
    f_type = [ty], Param.bool_type;
    f_cat = semantics;
    f_initial_cat = semantics;
    f_private = true;
    f_options = 0 }
  )

let gtest_fun = Param.memo_type (fun ty ->
  let u = new_unfailing_var_def ty
  and v = new_unfailing_var_def ty
  and x = new_var_def Param.bool_type
  and fail = get_fail_term ty in

  let semantics = Red
    [
      [true_term;u;v], u, [];
      [x;u;v], v, [(x, true_term)];
      [fail_bool();u;v], fail, []
    ]
  in
  { f_orig_name = "if-then-else";
    f_name = "if-then-else";
    f_type = [Param.bool_type;ty;ty], ty;
    f_cat = semantics;
    f_initial_cat = semantics;
    f_private = true;
    f_options = 0 })

(* The projection operator *)

let complete_semantics_constructors type_arg type_result =
  let var_fail_list = List.map new_unfailing_var_def type_arg
  and var_list = List.map new_var_def type_arg
  and fail_list = List.map get_fail_term type_arg
  and fail_result = get_fail_term type_result in

  let rec sub_complete var_list var_fail_list fail_list =
    match var_list, var_fail_list, fail_list with
    | [], [], [] -> []
    | x::var_l, _::var_fl, fail::fail_l ->
	let prev_list = sub_complete var_l var_fl fail_l in
	(fail::var_fl)::(List.map (fun l -> x::l) prev_list)
    | _,_,_ -> internal_error "The three lists should have the same size"
  in
  List.map (fun l -> l, fail_result,[]) (sub_complete var_list var_fail_list fail_list)

let red_rules_constructor f =
  let vars1 = var_gen (fst f.f_type) in
  (vars1, FunApp(f, vars1),[]) ::
    (complete_semantics_constructors (fst f.f_type) (snd f.f_type))

let red_rules_fun f =
  match f.f_cat with
    Eq red_rules -> (red_rules_constructor f) @ (List.map (fun (lhs,rhs) -> (lhs, rhs, [])) red_rules)
  | Red red_rules -> red_rules
  | Name _ -> [([],FunApp(f,[]),[])]
	(* This is ok because this function is called
	   either not with names (calls from Pitransl/Pitranslweak
	   and from TermsEq.close_term_destr_eq when it is used on
	   clauses that define LetFilter predicates)
	   or only with names from processes (calls from
	   TermsEq.close_term_destr_eq that come from Simplify).
	   We never have name function symbols here. *)
  | _ -> red_rules_constructor f

let get_function_name f =
  match f.f_cat with
    Tuple when f.f_name = "" ->
      let arity = List.length (fst f.f_type) in
      if (arity = 0) || (Param.get_ignore_types()) then
	(string_of_int arity) ^ "-tuple"
      else
	(tl_to_string "-" (fst f.f_type)) ^ "-tuple"
  | _ -> f.f_name

let projection_fun = Param.memo (fun (f_symb,i) ->
  if f_symb.f_cat <> Tuple
  then internal_error "[Terms.projection_fun] This should be a tuple";

  let type_list = fst f_symb.f_type in
  let type_result = snd f_symb.f_type in
  let var_list = var_gen type_list
  and gen_var_list = List.map (fun ty -> FunApp(new_gen_var ty false,[])) type_list
  and x = new_var_def type_result

  and ieme_type = List.nth type_list (i-1) in

  let fail = get_fail_term type_result
  and fail' = get_fail_term ieme_type in

  let semantics = Red
    [
      [FunApp(f_symb,var_list)], List.nth var_list (i-1), [];
      [x], fail', [x,FunApp(f_symb,gen_var_list)];
      [fail], fail', []
    ]
  in
  let name = Printf.sprintf "%d-proj-%s" i (get_function_name f_symb) in
  { f_orig_name = name;
    f_name = name;
    f_type = [type_result], ieme_type;
    f_cat = semantics;
    f_initial_cat = semantics;
    f_private = f_symb.f_private;
    f_options = 0 })

(* [get_all_projection_fun tuple_symb] returns the list of projection
   functions corresponding to the tuple function [tuple_symb] *)
let get_all_projection_fun tuple_symb =
  let rec sub_get_proj n l =
    match l with
    | [] -> []
    | _::q -> (projection_fun (tuple_symb,n))::(sub_get_proj (n+1) q)
  in
  sub_get_proj 1 (fst tuple_symb.f_type)

(* [clauses_for_function clauses_for_red_rules f] generates clauses
   for a function [f], given a function [clauses_for_red_rules] such
   that [clauses_for_red_rules f red_rules] generates clauses for
   function that has rewrite rules [red_rules].
   (For constructors, the rewrite rules f(...fail...) -> fail are
   omitted from [red_rules]. The function [clauses_for_red_rules] must
   take this point into account. In practice, this is easy because the
   clauses that come from f(...fail...) -> fail are useless.  This
   however needs to be justified in each case.) *)

let rec clauses_for_function clauses_for_red_rules f =
  if (not f.f_private) &&
    (* Don't generate clauses for type converter functions when we ignore types
       (These functions disappear.) *)
    (not ((f.f_options land Param.fun_TYPECONVERTER != 0) && (Param.get_ignore_types())))
  then
    match f.f_cat with
      Eq red_rules ->
	let vars1 = var_gen (fst f.f_type) in
	let red_rules = (vars1, FunApp(f, vars1),[]) :: (List.map (fun (lhs,rhs) -> (lhs, rhs, [])) red_rules) in
	clauses_for_red_rules f red_rules
    | Red red_rules ->
	clauses_for_red_rules f red_rules
    | Tuple ->
	(* For tuple constructor *)
	let vars1 = var_gen (fst f.f_type) in
	clauses_for_red_rules f [(vars1, FunApp(f, vars1),[])];
	(* For corresponding projections *)
      	List.iter (clauses_for_function clauses_for_red_rules) (get_all_projection_fun f)
    | _ -> ()

(* Names *)

let new_name_fun =
  Param.memo_type (fun t ->
      let cat = Name { prev_inputs = None; prev_inputs_meaning = [MAttSid] } in
      let name = "new-name" ^ (Param.get_type_suffix t) in
      { f_orig_name = name;
        f_name = name;
        f_type = [Param.sid_type], t;
        f_cat = cat;
        f_initial_cat = cat;
        f_private = false;
        f_options = 0 })

(*********************************************
               Occurrences
**********************************************)

let occ_count = ref 0

let reset_occurrence () =
  occ_count := 0

let new_occurrence () =
  incr occ_count;
  !occ_count

let rec put_lets p = function
    [] -> p
  | (v,t)::l -> put_lets (Let(PatVar v,t,p,Nil,new_occurrence())) l

(*********************************************
                       New names
**********************************************)

let create_name orig_name s ty is_private =
  let cat = Name { prev_inputs = None; prev_inputs_meaning = [] } in
  { f_orig_name = orig_name;
    f_name = s;
    f_type = ty;
    f_cat = cat;
    f_initial_cat = cat;
    f_private = is_private;
    f_options = 0 }
    
(**********************************************
  Rewrite rules for destructors with otherwise
***********************************************)

exception True_inequality
exception False_inequality


let generate_destructor_with_side_cond prev_args lht_list rht ext =

  (* Given an inequality [for all (may-fail variabless in uni_term_list), term_list <> uni_term_list],
     [remove_uni_fail_var] returns [(l1,l2)] representing an inequality [l1 <> l2] equivalent
     to the initial inequality, by removing the may-fail variables. *)

  let rec remove_uni_fail_var term_list uni_term_list = match term_list, uni_term_list with
    | [],[] -> [],[]
    | [],_ | _,[] -> internal_error "The two lists should have the same length"
    | t::q, Var(v)::uq when v.unfailing ->
        begin match v.link with
          | NoLink ->
              link v (TLink t);
              remove_uni_fail_var q uq
          | TLink t' ->
              let (list_left,list_right) = remove_uni_fail_var q uq in
              (t::list_left,t'::list_right)
          | _ -> internal_error "Unexpected link"
        end
    | t::q,ut::uq -> let (list_left,list_right) = remove_uni_fail_var q uq in
        (t::list_left,ut::list_right)
  in

  (* When [prev_args = (a1,...,an)] is the list of arguments of the previous
     rewrite rules, [generalize_prev_args] builds returns a list of pairs
     [(li,li')] representing the inequality [\wedge_i li <> li']
     equivalent to the inequality
     [\wedge_i forall (variables in ai), lht_list <> ai].
     The returned inequalities do not contain general may-fail variables
     (thanks to remove_uni_fail_var), but may contain may-fail variables.
     These variables will be removed in the next steps by case distinctions. *)

  let rec generalize_prev_args prev_args = match prev_args with
    | [] -> []
    | term_list::q ->
        (* Get the variables *)
        let vars = ref [] in
        List.iter (get_vars vars) term_list;

        (* Remove the may-fail variables *)
        let message_var_list = List.filter (fun v -> not (v.unfailing)) !vars in

        (* Generalize the variables *)
        let term_list' =
          auto_cleanup (fun () ->
            List.map (generalize_vars_in message_var_list) term_list
          )
        in

        (* Remove the universal may-fail variables *)
        let (lterms_left,lterms_right) = auto_cleanup (fun () ->
          remove_uni_fail_var lht_list term_list'
          )
        in

        (lterms_left,lterms_right)::(generalize_prev_args q)
  in

  let rec get_may_fail_vars varsl term = match term with
    | Var(v) ->
        begin match v.link with
          | NoLink -> if v.unfailing && not (List.memq v (!varsl)) then varsl := v :: (!varsl)
          | TLink(t) -> get_may_fail_vars varsl t
          | _ -> internal_error "Unexpected link"
        end
    | FunApp(_,l) -> List.iter (get_may_fail_vars varsl) l
  in

  let rec simplify_one_neq term_left term_right = match term_left,term_right with
    | Var(vl),Var(vr) when vl==vr -> raise False_inequality
    | FunApp(f,_), FunApp(f',_) when f.f_cat = Failure && f'.f_cat = Failure -> raise False_inequality
    | Var({link = TLink tl}),tr ->  simplify_one_neq tl tr
    | tl, Var({link = TLink tr}) -> simplify_one_neq tl tr
    | Var(v),FunApp(f,_) when v.unfailing = false && f.f_cat = Failure -> raise True_inequality
    | FunApp(f,_), Var(v) when v.unfailing = false && f.f_cat = Failure -> raise True_inequality
    | FunApp(f,_),FunApp(f',_) when f'.f_cat = Failure -> raise True_inequality
    | FunApp(f,_),FunApp(f',_) when f.f_cat = Failure -> raise True_inequality
    | _,_ -> term_left,term_right
  in

  let simplify_neq lterm_left lterm_right =
    List.fold_left2 (fun (neql,neqr) term_left term_right ->
      try
        let term_left',term_right' = simplify_one_neq term_left term_right in
        (term_left'::neql),(term_right'::neqr)
      with
        | False_inequality -> (neql,neqr)
    ) ([],[]) lterm_left lterm_right
  in

  let destructors = ref [] in

  let rec remove_may_fail_term_neq list_neq =
    (* Simplify Neq *)

    let list_neq' = List.fold_left (fun lneq (lterm_left,lterm_right) ->
      try
        let (lterm_left', lterm_right') = simplify_neq lterm_left lterm_right in

        if lterm_left' = []
        then raise False_inequality;

        (lterm_left', lterm_right')::lneq
      with
        True_inequality -> lneq
      ) [] list_neq
    in

    (* Get the may_fail_variables *)

    let vars = ref [] in
    List.iter (fun (lleft,lright) ->
      List.iter (get_may_fail_vars vars) lleft;
      List.iter (get_may_fail_vars vars) lright
    ) list_neq';

    let may_fail_var_list = !vars in

    if may_fail_var_list = []
    then
      (* If no more may-fail variables in inequalities then return the destructor *)
      auto_cleanup (fun () ->
        let rht' = copy_term2 rht
        and lht' = List.map copy_term2 lht_list
        and side_c = List.map (fun (left_l, right_l) ->
          let left_l' = List.map copy_term2 left_l
          and right_l' = List.map copy_term2 right_l in

          let type_list = List.map get_term_type left_l' in
          let tuple_symb = get_tuple_fun type_list in

          FunApp(tuple_symb,left_l'),FunApp(tuple_symb,right_l')
        ) list_neq' in

        (* Check the variables of the right hand terms *)

        let var_list_rht = ref [] in
        get_vars var_list_rht rht';

        if not (List.for_all (fun v -> List.exists (occurs_var v) lht') (!var_list_rht)) then
          Parsing_helper.input_error "All variables of the right-hand side of a \"reduc\" definition\nshould also occur in the left-hand side" ext;

        destructors := (lht',rht',side_c)::!destructors
      )
    else
      begin
        let mf_var = List.hd may_fail_var_list in

        (* Replace the may-fail variable by Fail *)
        auto_cleanup (fun () ->
          let fail = get_fail_term mf_var.btype in
          link mf_var (TLink fail);
          try
            remove_may_fail_term_neq list_neq'
          with
            | False_inequality -> ()
        );

        (* Replace the may-fail variable by a message variable *)
        auto_cleanup (fun () ->
          let x = new_var_def mf_var.btype in
          link mf_var (TLink x);
          try
	    remove_may_fail_term_neq list_neq'
	  with
	    | False_inequality -> ()
        )
      end
  in

  let list_side_c = generalize_prev_args prev_args in
  remove_may_fail_term_neq list_side_c;

  !destructors
