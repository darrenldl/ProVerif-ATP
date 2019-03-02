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
open Stringmap

let get_event_status_internal event_status_table f =
  try 
    Hashtbl.find event_status_table f
  with Not_found ->
    Parsing_helper.internal_error ("event not found " ^ f.f_name)

       
let get_event_status pi_state f =
  match pi_state.pi_event_status_table with
  | Unset ->
     Parsing_helper.internal_error "event_status_table should be set before Pievent.get_event_status"
  | Set event_status_table ->
     get_event_status_internal event_status_table f
                                  

let set_event_status state =
  let event_status_table = Hashtbl.create 7 in

  let set_event_status_e set_end set_begin = function
      QSEvent(b, FunApp(f,_)) ->
       let fstatus = get_event_status_internal event_status_table f in
       if set_end then
         begin
	   if b then fstatus.end_status <- Inj else
	     if fstatus.end_status = No then fstatus.end_status <- NonInj
	 end;
       if set_begin then
         begin
	   if b then fstatus.begin_status <- Inj else
	     if fstatus.begin_status = No then fstatus.begin_status <- NonInj
	 end
      | _ -> ()
  in

  let rec set_event_status_r set_begin = function
    | Before(e, ll) ->
       List.iter (set_event_status_e true set_begin) e;
       List.iter (List.iter (function
	                QEvent e -> set_event_status_e false true e
	              | NestedQuery q -> set_event_status_r true q)) ll
  in
  
  let set_event_status1 = function
    | PutBegin(i, l) ->
       List.iter (fun f ->
	   let fstatus = get_event_status_internal event_status_table f in
	   if i then fstatus.begin_status <- Inj else
	     if fstatus.begin_status = No then fstatus.begin_status <- NonInj) l
    | RealQuery (q,_) ->
       set_event_status_r false q
    | QSecret _ ->
       ()
  in

  let set_event_status_q = function
    | QueryToTranslate _ ->
       Parsing_helper.internal_error "query should be translated before Pievent.set_event_status"
    | CorrespQuery(ql) ->
       List.iter set_event_status1 ql
    | CorrespQEnc(qql) ->
       List.iter (fun (_,q) -> set_event_status1 q) qql
    | ChoiceQEnc _ | ChoiceQuery | NonInterfQuery _ | WeakSecret _ ->
       ()
  in
  
  List.iter (fun d ->
      Hashtbl.add event_status_table d { end_status = No; begin_status = No }
    ) state.pi_events;
  begin
    match state.pi_process_query with
      Equivalence _ -> ()
    | SingleProcess(p, ql) ->
       List.iter set_event_status_q ql
    | SingleProcessSingleQuery(_, q) ->
       set_event_status_q q
  end;
  { state with pi_event_status_table = Set event_status_table }
