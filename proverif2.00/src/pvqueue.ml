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
(*  All functions that traverse the queue are tail-recursive,
    and that is important to avoid a stack overflow with
    very large sets of clauses. *)

type 'a queue = { mutable next : 'a queue option;
                  elem : 'a }

type 'a q = { mutable qstart : 'a queue option;
              mutable qend : 'a queue option }

let new_queue() = { qstart = None; qend = None }

(* qstart and qend are None at the same time, 
   and this means that the queue is empty *)

let add queue r =
  match queue.qend with
    None -> let qelem = { next = None; elem = r } in
            queue.qstart <- Some qelem; queue.qend <- Some qelem
  | Some q -> q.next <- Some { next = None; elem = r };
              queue.qend <- q.next

let get queue =
  match queue.qstart with
    None -> None
  | Some q -> if q.next == None then queue.qend <- None;
              queue.qstart <- q.next;
              Some q.elem

let rec lengthq l q =
  match q with
    None -> l
  | Some q' -> lengthq (1+l) (q'.next)

let length queue =
  lengthq 0 queue.qstart

let exists queue f = 
  let rec existsrec q =
    match q with
      None -> false
    | Some q' -> (f q'.elem) || (existsrec q'.next)
  in
  existsrec queue.qstart

type 'a previous_elem =
    Start 
  | Elem of 'a queue
    
let filter queue f =
  let rec filterrec prev q =
    match q with
      None ->
	begin
	  match prev with
	    Start -> queue.qstart <- None; queue.qend <- None
	  | Elem pelem -> pelem.next <- None; queue.qend <- Some pelem
	end
    | Some q' -> 
	if f q'.elem then
	  begin
	    begin
	      match prev with
		Start -> queue.qstart <- Some q'
	      | Elem pelem -> pelem.next <- Some q'
	    end;
	    filterrec (Elem q') q'.next
	  end
	else
	  filterrec prev q'.next
  in
  filterrec Start queue.qstart

let iter queue f =
  let rec iterrec q =
    match q with
      None -> ()
    | Some q' -> 
	f q'.elem; 
	iterrec q'.next
  in
  iterrec queue.qstart
 
