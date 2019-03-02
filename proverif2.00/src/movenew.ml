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

(* Move restrictions under inputs to make the analysis more precise *)

let rec put_new l p =
  match l with
    [] -> p
  | ((a,args,occ)::l') -> Restr(a,args,put_new l' p,occ)

let rec move_new accu = function
    Nil -> Nil

  | NamedProcess(s, tl, p) ->
    	(* let (l1,l2) = List.partition (fun (f,_,_) -> List.exists (Terms.occurs_f f) tl) accu in *)
        (* put_new l1 (NamedProcess(s, tl , move_new l2 p)) *)
      if List.exists (fun (f, _, _) -> (List.exists (Terms.occurs_f f) tl)) accu then
        NamedProcess(s, [], move_new accu p)
      else
        NamedProcess(s, tl, move_new accu p)
  | Par(p1,p2) -> put_new accu (Par(move_new [] p1, move_new [] p2))
  | Repl(p,occ) ->  put_new accu (Repl (move_new [] p,occ))
  | Restr(f, args, p,occ) -> move_new ((f,args, occ)::accu) p
  | Test(t,p1,p2,occ) ->
      if p2 <> Nil then
	put_new accu (Test(t, move_new [] p1, move_new [] p2,occ))
      else
	let (l1,l2) = List.partition (fun (f,_,_) -> Terms.occurs_f f t) accu in
        put_new l1 (Test(t,move_new l2 p1,Nil,occ))
  | Input(t,pat,p,occ) ->
      let (l1,l2) = List.partition (fun (f,_,_) -> Terms.occurs_f f t || Terms.occurs_f_pat f pat) accu in
      put_new l1 (Input(t,pat, move_new l2 p,occ))
  | Output(t1,t2,p,occ) ->
      let (l1,l2) = List.partition (fun (f,_,_) -> Terms.occurs_f f t1 || Terms.occurs_f f t2) accu in
      put_new l1 (Output(t1,t2,move_new l2 p,occ))
  | Let(pat,t,p,p',occ) ->
      if p' <> Nil then
        put_new accu (Let(pat, t, move_new [] p, move_new [] p',occ))
      else
        let (l1,l2) = List.partition (fun (f,_,_) -> Terms.occurs_f f t || Terms.occurs_f_pat f pat) accu in
        put_new l1 (Let(pat, t, move_new l2 p, Nil,occ))
  | LetFilter(vl,fact,p,q,occ) ->
      if q <> Nil then
	put_new accu (LetFilter(vl,fact,move_new [] p, move_new [] q,occ))
      else
	let (l1,l2) = List.partition (fun (f,_,_) -> Terms.occurs_f_fact f fact) accu in
	put_new l1 (LetFilter(vl, fact, move_new l2 p,Nil,occ))
  | Event(t1,env_args,p,occ) ->
      let (l1,l2) = List.partition (fun (f,_,_) -> Terms.occurs_f f t1) accu in
      put_new l1 (Event(t1, env_args, move_new l2 p, occ))
  | Insert(t1,p,occ) ->
      let (l1,l2) = List.partition (fun (f,_,_) -> Terms.occurs_f f t1) accu in
      put_new l1 (Insert(t1, move_new l2 p, occ))
  | Get(pat,t1,p,q,occ) ->
      if q <> Nil then
	put_new accu (Get(pat,t1,move_new [] p, move_new [] q,occ))
      else
	let (l1,l2) = List.partition (fun (f,_,_) -> Terms.occurs_f f t1 || Terms.occurs_f_pat f pat) accu in
	put_new l1 (Get(pat, t1, move_new l2 p, Nil, occ))
  | Phase(n,p,occ) ->
      Phase(n, move_new accu p,occ)
  | Barrier(n, tag, p,occ) ->
      Barrier(n, tag, move_new accu p,occ)
  | AnnBarrier _ ->
     Parsing_helper.internal_error "Annotated barriers should not appear here (5)"

let move_new p = move_new [] p
