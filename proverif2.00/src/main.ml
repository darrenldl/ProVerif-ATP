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
open Parsing_helper
open Out_pos

type in_pos =
    Horn
  | HornType
  | SpassIn
  | Pi
  | PiType
  | Default

let gc = ref false

let in_kind = ref Default

let out_file = ref ""

let out_n = ref 0

let up_out = function
  | "spass" -> Spass
  | "tptp"  -> Tptp
  | "solve" -> Solve
  | _ -> Parsing_helper.user_error "-out should be followed by spass, tptp or solve"

let up_in = function
    "horn" -> Horn
  | "horntype" -> HornType
  | "spass" -> SpassIn
  | "pi" -> Pi
  | "pitype" -> PiType
  | _ -> Parsing_helper.user_error "-in should be followed by horn, horntype, spass, pi, or pitype"

exception Is_equivalent

let check_disequations l =
  if l <> [] then
    begin
      List.iter (fun (t1, t2) ->
	try
	  Terms.auto_cleanup (fun () ->
	    TermsEq.unify_modulo (fun () ->
	      Display.Text.print_string "Disequation: ";
	      Display.Text.display_term t1;
	      Display.Text.print_string " <> ";
	      Display.Text.display_term t2;
	      Display.Text.newline();
	      Parsing_helper.user_error "Invalid disequation: the terms unify"
		) t1 t2)
	with Terms.Unify -> ()
	    ) l;
      Display.Text.print_line "Note: all disequations are valid. (ProVerif otherwise ignores them.)"
    end
    
let set_need_vars_in_names pi_state =
  match pi_state.pi_need_vars_in_names with
    Computed _ -> pi_state
  | Function f ->
      let need_vars_in_names = f pi_state in
      { pi_state with
        pi_need_vars_in_names = Computed need_vars_in_names }

let transl_query pi_state =
  let aux = function
    | QueryToTranslate f -> f pi_state
    | x -> x
  in
  let process_query' =
    match pi_state.pi_process_query with
    | (Equivalence _) as pq -> pq
    | SingleProcess(p,ql) -> SingleProcess(p, List.map aux ql)
    | SingleProcessSingleQuery(p,q) -> SingleProcessSingleQuery(p, aux q)
  in
  { pi_state with
    pi_process_query = process_query' }

let check_delayed_names pi_state =
  let aux = function
    | QueryToTranslate _ ->
	Parsing_helper.internal_error "Queries should have been translated before check_delayed_names"
    | CorrespQuery(ql) ->
	CorrespQuery(List.map Reduction_helper.check_delayed_names ql)
    | CorrespQEnc(qql) ->
	CorrespQEnc(List.map (fun (qorig, qencoded) ->
	  (Reduction_helper.check_delayed_names qorig,
	   Reduction_helper.check_delayed_names qencoded)) qql)
    | ChoiceQEnc q -> ChoiceQEnc(Reduction_helper.check_delayed_names q)
    | x -> x
  in
  let process_query' = 
    match pi_state.pi_process_query with
    | (Equivalence _) as pq -> pq
    | SingleProcess(p,ql) -> SingleProcess(p, List.map aux ql)
    | SingleProcessSingleQuery(p,q) -> SingleProcessSingleQuery(p, aux q)
  in
  { pi_state with
    pi_process_query = process_query' }
    
let move_new pi_state =
  if !Param.move_new then
    let process_query' =
      match pi_state.pi_process_query with
      | Equivalence(p1, p2) -> Equivalence (Movenew.move_new p1, Movenew.move_new  p2)
      | SingleProcess(p, ql) -> SingleProcess(Movenew.move_new p, ql)
      | SingleProcessSingleQuery(p,q) -> SingleProcessSingleQuery(Movenew.move_new p, q)
    in
    { pi_state with
      pi_process_query = process_query' }
  else
    pi_state

(* [split pi_state next_f] calls [next_f] on each query in [pi_state].
   It guarantees that the state passed to [next_f] never has
   [pi_process_query = SingleProcess _]. This case is replaced with several calls
   using [SingleProcessSingleQuery]. *)
      
let split pi_state next_f =
  match pi_state.pi_process_query with
    SingleProcess(p,ql) ->
      List.iter (fun q ->
	next_f { pi_state with
                 pi_process_query = SingleProcessSingleQuery(p,q) }
	  ) ql
  | _ -> next_f pi_state
      
let is_non_interf horn_state =
  match horn_state.h_solver_kind with
    Solve_Noninterf _ -> true
  | _ -> false

let interference_analysis horn_state pi_state =
  if (pi_state.pi_equations != []) && (is_non_interf horn_state) then
    Parsing_helper.input_warning "using \"noninterf\" in the presence of equations may yield many\nfalse attacks. If you observe false attacks, try to code the desired\nproperty using \"choice\" instead." Parsing_helper.dummy_ext;
  let (_,query) = Param.get_process_query pi_state in
  let result = Rules.bad_derivable horn_state in
  if result = [] then
    begin
      Display.Text.print_string "RESULT ";
      Display.Text.display_query query;
      Display.Text.print_line " is true (bad not derivable).";
      if !Param.html_output then
	begin
	  Display.Html.print_string "<span class=\"result\">RESULT ";
	  Display.Html.display_query query;
	  Display.Html.print_line " is <span class=\"trueresult\">true (bad not derivable)</span>.</span>"
	end;
      raise Is_equivalent

    end
  else
    begin
      let l = List.map (fun rule ->
        Display.Text.print_string "goal reachable: ";
        Display.Text.display_rule rule;
	if !Param.html_output then
	  begin
	    Display.Html.print_string "goal reachable: ";
            Display.Html.display_rule rule
	  end;
	try
          let new_tree = History.build_history None rule in
	  let r =
	  (* For weak secrets, the reconstructed attack really falsifies the
	     equivalence; for other equivalences, it just reaches the program
	     point at which we find the first difference of execution, which
	     does not guarantee that the equivalence is false *)
	    if (!Param.reconstruct_trace) && (!Param.reconstruct_derivation) then
	      match query with
	      | WeakSecret _ -> 
		  Reduction.do_reduction None None new_tree
	      | NonInterfQuery _ ->
		  ignore (Reduction.do_reduction None None new_tree);
		  false
	      | ChoiceQuery | ChoiceQEnc _ ->
		  ignore (Reduction_bipro.do_reduction new_tree);
		  false
	      | _ ->
		  false
	    else
	      false
	  in
	  Terms.cleanup();
	  r
	with Not_found ->
	  (* When the derivation could not be reconstructed *)
	  Terms.cleanup();
	  false
	  ) result
      in
      Display.Text.print_string "RESULT ";
      Display.Text.display_query query;
      if List.exists (fun x -> x) l then
	Display.Text.print_line " is false."
      else
	Display.Text.print_line " cannot be proved (bad derivable).";
      if !Param.html_output then
	begin
	  Display.Html.print_string "<span class=\"result\">RESULT ";
	  Display.Html.display_query query;
	  if List.exists (fun x -> x) l then
	    Display.Html.print_line " is <span class=\"falseresult\">false</span>.</span>"
	  else
	    Display.Html.print_line " <span class=\"unknownresult\">cannot be proved (bad derivable)</span>.</span>"
	end
    end


let get_out_file() =
  if !out_file = "" then
    Parsing_helper.user_error "you should provide the output filename by the option -o <filename>";
  incr out_n;
  !out_file ^ (if !out_n = 1 then "" else string_of_int (!out_n))
  
let horn_solve (horn_state, queries) =
  match !Arg_params.out_kind with
    Solve ->
     TermsEq.record_eqs horn_state; 
     Rules.main_analysis horn_state queries
  | Spass ->
     Spassout.main (get_out_file()) horn_state.h_equations horn_state.h_clauses queries
  | Tptp ->
    Tptpout.main (get_out_file ()) horn_state.h_equations horn_state.h_clauses queries
      
let corresp_solve (horn_state, pi_state) =
  Param.current_state := pi_state;
  match !Arg_params.out_kind with
    Solve ->
      Piauth.solve_auth horn_state pi_state
  | Spass ->
      Spassout.main (get_out_file()) horn_state.h_equations horn_state.h_clauses
        (Encode_queries.query_to_facts pi_state)
  | Tptp ->
    Tptpout.main (get_out_file ()) horn_state.h_equations horn_state.h_clauses
        (Encode_queries.query_to_facts pi_state)

let equiv_solve (horn_state, pi_state) =
  Param.current_state := pi_state;
  match !Arg_params.out_kind with
    Solve ->
      interference_analysis horn_state pi_state
  | Spass ->
      Parsing_helper.user_error "the clauses generated by ProVerif for process equivalences cannot be\ntranslated to the Spass input format."
  | Tptp ->
      Parsing_helper.user_error "the clauses generated by ProVerif for process equivalences cannot be\ntranslated to the Spass input format."

(*********************************************
                 Interface
**********************************************)

let display_process pi_state =
  if (!Param.html_output) || (!Param.verbose_explain_clauses = Param.ExplainedClauses) || (!Param.explain_derivation) then
    match pi_state.pi_process_query with
      Equivalence(p1, p2) ->
	ignore (Display.Def.display_numbered_process p1 false false);
	ignore (Display.Def.display_numbered_process p2 false false)
    | SingleProcessSingleQuery(p, (ChoiceQuery | ChoiceQEnc _)) ->
	(* The process is in fact a biprocess *)
	ignore (Display.Def.display_numbered_process p true false)
    | SingleProcessSingleQuery(p, _) | SingleProcess(p,_) ->
	ignore (Display.Def.display_numbered_process p false false)

let is_corresp = function
  | CorrespQuery _ | CorrespQEnc _ -> true
  | _ -> false

let get_initial_query = function
    CorrespQEnc qql -> CorrespQuery(List.map fst qql)
  | ChoiceQEnc q -> CorrespQuery([q])
  | q -> q
           
let display_encoded_process pi_state =
  let (p,ql) =
    match pi_state.pi_process_query with
    | SingleProcessSingleQuery(p,q) -> (p,[q])
    | SingleProcess(p,ql) -> (p,ql)
    | Equivalence _ -> Parsing_helper.internal_error "Unexpected equivalence query"
  in
  let initial_queries = List.map get_initial_query ql in
  if List.exists2 (!=) ql initial_queries then
    (* The encoding is non-trivial, display the encoded process *)
    let bi_proc =
      match ql with
        (* Invariant: ChoiceQuery and ChoiceQEnc appear only with
           SingleProcessSingleQuery *)
	[ChoiceQEnc _ | ChoiceQuery] -> true
      | _ -> false
    in
    if !Param.html_output then
      begin
        Display.Html.print_string "<LI>Encoded process for ";
        Display.Html.display_list Display.Html.display_query "; " initial_queries;
        Display.Html.print_string "<br>\n"
      end
    else
      begin
        Display.Text.print_string "-- Encoded process for ";
        Display.Text.display_list Display.Text.display_query "; " initial_queries;
        Display.Text.newline();
      end;
    Some (Display.Def.display_numbered_process p bi_proc false)
  else
    (* No encoding was done *)
    None
      
let display_query_header process_shown pi_state =
  let (p,q) = Param.get_process_query pi_state in
  let initial_query = get_initial_query q in
  if (!Param.tulafale == 1) && (is_corresp initial_query) then
    Display.Text.print_line "-- Secrecy & events."
  else
    begin
      Display.Text.print_string "-- ";
      Display.Text.display_query initial_query;
      Display.Text.newline();
    end;
  if !Param.html_output then
    begin
      Display.Html.print_string "<LI><span class=\"query\">";
      Display.Html.display_query initial_query;
      Display.Html.print_string "</span><br>\n"
    end;
  if q != initial_query then
    (* The encoding is non-trivial, display it *)
    let bi_proc =
      match q with
	ChoiceQEnc _ | ChoiceQuery -> true
      | _ -> false
    in
    if !Param.html_output then
      begin
	Display.Html.display_query q;
	Display.Html.print_string " in "
      end
    else
      begin
	Display.Text.display_query q;
	Display.Text.print_string " in "
      end;
    match process_shown with
    | None ->
	ignore (Display.Def.display_numbered_process p bi_proc true)
    | Some n ->
	Display.Def.display_process_link n bi_proc true;
	Display.Def.print_line "."

let solve_simplified_process pi_state1 =
  let pi_state2 = Simplify.prepare_process pi_state1 in
  let (_,q) = Param.get_process_query pi_state2 in
  if !Param.html_output then
    begin
      Display.Html.print_string "<LI><span class=\"query\">";
      Display.Html.display_query q;
      Display.Html.print_string "</span><br>\n"
    end;
  Display.Text.print_string "-- ";
  Display.Text.display_query q;
  Display.Text.newline();
  display_process pi_state2;
  let horn_pi_state = Pitranslweak.transl pi_state2 in
  Display.Text.print_line "Solving the clauses...";
  equiv_solve horn_pi_state;
  incr Param.current_query_number

let simplify_and_solve_process pi_state1 =
  Display.Text.print_line "Looking for simplified processes ...";
  if (!Param.html_output) then
    Display.Html.print_line "Trying simplified processes.";
  let found_simplified_process = ref false in
  Simplify.simplify_state pi_state1 (fun pi_state2 ->
      if (not (!found_simplified_process)) && (!Param.html_output) then
        Display.Html.print_string "<UL>\n";
      found_simplified_process := true;
      solve_simplified_process pi_state2);
  if not (!found_simplified_process) then
    begin
      Display.Text.print_line "No simplified process found.";
      if (!Param.html_output) then
	Display.Html.print_line "No simplified process found.";
    end
  else if (!Param.html_output) then
    Display.Html.print_string "</UL>\n"

let rec interface_general_merg list_simpl_pi_state =
  let nb_biprocess = List.length list_simpl_pi_state in
  let conjug =
    if nb_biprocess = 1
    then ""
    else "es"
  in
  Printf.printf "\n----------------------------\n";
  Printf.printf "ProVerif has found %d simplified process%s equivalent to the initial process.\n" nb_biprocess conjug;
  Printf.printf "Possible actions:\n";
  Printf.printf "1- View them all\n";
  Printf.printf "2- Try solving equivalence for all of them\n";
  Printf.printf "   Note that this option stops when ProVerif finds an observationally equivalent biprocess\n";
  Printf.printf "3- Try solving equivalence for one specific process (enter 3-x with x the number of the process)\n";
  Printf.printf "4- Exit ProVerif\n";

  let result = read_line () in
  match result with
    | "1" ->
      let acc = ref 1 in
      List.iter (fun pi_state ->
        Printf.printf "\n---------------------------\n";
        Printf.printf "-- Simplified process %d --\n" !acc;
        Printf.printf "---------------------------\n";

	let (p,_) = Param.get_process_query pi_state in
	Display.Text.display_process_occ "" p;
	Display.Text.newline();
	acc := !acc + 1
      ) list_simpl_pi_state;
      interface_general_merg list_simpl_pi_state
    | "2" ->
       begin try
         List.iter solve_simplified_process list_simpl_pi_state;
       with Is_equivalent -> ()
       end
    | r when (String.length r > 2) && (String.sub r 0 2 = "3-") ->
       let size = List.length list_simpl_pi_state in
       let n =
         try
           int_of_string (String.sub r 2 ((String.length r) - 2))
         with _ -> 0 in

       if n > 0 && n <= size
       then
         begin
           try
             solve_simplified_process (List.nth list_simpl_pi_state (n-1))
           with Is_equivalent -> ()
         end;

       interface_general_merg list_simpl_pi_state

    | "4" -> exit 0
    | _ -> interface_general_merg list_simpl_pi_state

let interface_for_merging_process pi_state =
  Display.Text.print_line "Check the process...";
  let (p,_) = Param.get_process_query pi_state in
  Simplify.verify_process [] p;
  Display.Text.print_line "Calculate the simplified processes...";
  let simpl_state_list = ref [] in
  Simplify.simplify_state pi_state
    (fun pi_state' -> simpl_state_list := pi_state'::!simpl_state_list);
  if !simpl_state_list <> [] then
    begin
      if !Param.html_output then
        Display.Html.print_string "<UL>\n";
      interface_general_merg !simpl_state_list;
      if !Param.html_output then
        Display.Html.print_string "</UL>\n"
    end
  else
    Display.Text.print_line "No simplified process found"

let compile_barriers pi_state next_f =
  if !Param.has_barrier then
    begin
      (* Expand "sync" barriers if they are present *)
      if (!Param.key_compromise != 0) then
  	Parsing_helper.user_error "Key compromise is incompatible with sync";
      if (pi_state.pi_max_used_phase > 0) then
  	Parsing_helper.user_error "Phase is incompatible with sync";
      
      Proswapper.compile_barriers (fun pi_state2 ->
  	  Display.Text.print_line "-- After compilation of barriers";
  	  if !Param.html_output then
  	    Display.Html.print_string "<LI><span class=\"query\">After compilation of barriers</span><br>\n";

  	display_process pi_state2;
	next_f pi_state2) pi_state
    end
  else
    next_f pi_state
      
let prove_equivalence_with_choice pi_state =
  (* This query header will be an item in the HTML list.
     In case the initial protocol uses choice, 
     it will be the only item. *)
  display_query_header None pi_state;
  if (!Param.key_compromise != 0) then
    Parsing_helper.user_error "Key compromise is incompatible with choice";

  let pi_state1 = set_need_vars_in_names pi_state in

  (* Open a new list for the various expansions of barriers
     with swapping *)
  if (!Param.html_output) && (!Param.has_barrier) then
    Display.Html.print_string "<UL>\n";
  begin
    try 
      compile_barriers pi_state1 (fun pi_state2 ->
          equiv_solve (Pitranslweak.transl pi_state2);
          incr Param.current_query_number;
	  
          if !Param.typed_frontend && not (!Param.has_barrier) then
	    begin
	      (* The untyped front-end do not support modifying processes *)
  	      (* Do not propose simplification of the process in case barriers are used.
  	     That would lead to too many processes. (We might change that in the future.) *)
  	      if !Param.simplify_process = 2 then
	        interface_for_merging_process pi_state1
  	      else if !Param.simplify_process = 1 then
	        simplify_and_solve_process pi_state1
	    end)
    with Is_equivalent -> ()
  end;
  if (!Param.html_output) && (!Param.has_barrier) then
    Display.Html.print_string "</UL>\n"


      
let prove_equivalence_two_processes pi_state =
  if !Param.has_choice then
    Parsing_helper.user_error "When showing equivalence of two processes, the processes cannot contain choice";
  if !Param.has_barrier then
    Parsing_helper.user_error "When showing equivalence of two processes, the processes cannot contain sync";
  if (!Param.key_compromise != 0) then
    Parsing_helper.user_error "Key compromise is incompatible with equivalence";

  if (!Param.html_output) then
    Display.Html.print_string "<span class=\"query\">Observational equivalence between two processes</span><br>\n"
  else if (!Param.verbose_explain_clauses = Param.ExplainedClauses) || (!Param.explain_derivation) then
    Display.Text.print_string "Observational equivalence between two processes\n";

  try
    let biprocess_found = ref false in
    (* Simplification sets need_vars_in_names empty.
       No need to set it explicitly *)
    Simplify.simplify_state pi_state (fun pi_state1 ->
      biprocess_found := true;
      let pi_state2 = Simplify.prepare_process pi_state1 in
      if !Param.html_output then
  	Display.Html.print_string "<LI><span class=\"query\">Observational equivalence</span><br>\n";
		
      display_process pi_state2;
		
      equiv_solve (Pitranslweak.transl pi_state2);
      incr Param.current_query_number
  	);
    if not (!biprocess_found) then
      begin
  	Display.Text.print_line "RESULT no biprocess can be computed";
  	if !Param.html_output
  	then Display.Html.print_string "<LI><span class=\"result\">RESULT no biprocess can be computed</span><br>"
      end
  with Is_equivalent -> ()

let is_some = function
    Some _ -> true
  | None -> false
                          
let prove_monoprocess_queries pi_state =      
  let pi_state1 = set_need_vars_in_names pi_state in
  let opt_process_num = display_encoded_process pi_state1 in
  if (!Param.html_output) && (is_some opt_process_num) then
    Display.Html.print_string "<UL>\n";
  
  (* [compile_barriers] always has a single possible output
     (there is no swapping for correspondences) *)
  compile_barriers pi_state1 (fun pi_state2 ->
    split pi_state2 (fun pi_state3 ->
      let pi_state4 = Pievent.set_event_status pi_state3 in
      let (horn_state, pi_state5) = Pitransl.transl pi_state4 in
      let pi_state6 = check_delayed_names pi_state5 in
      display_query_header opt_process_num pi_state6;
      let (_,q) = Param.get_process_query pi_state6 in
      begin
	match q with
	| CorrespQuery _ | CorrespQEnc _ ->
            (* Secrecy and authenticity *)
  	    corresp_solve (horn_state, pi_state6)
        | NonInterfQuery _ | WeakSecret _ ->
	    begin
              (* Non-interference and weak secrets *)
  	      try
  	        equiv_solve (horn_state, pi_state6)
  	      with Is_equivalent -> ()
	    end
	| _ ->
	    Parsing_helper.internal_error "Queries should have been translated and choice queries should have been already treated"
      end;
      incr Param.current_query_number
  	);
    );
  if (!Param.html_output) && (is_some opt_process_num) then
      Display.Html.print_string "</UL>\n"


let prove_queries pi_state =
  match pi_state.pi_process_query with
  | Equivalence _ ->
      prove_equivalence_two_processes pi_state
  | SingleProcessSingleQuery(_, (ChoiceQuery | ChoiceQEnc _)) ->
      (* Invariant: ChoiceQuery and ChoiceQEnc appear only with
         SingleProcessSingleQuery *)
      prove_equivalence_with_choice pi_state
  | _ ->
      prove_monoprocess_queries pi_state      
    
(*********************************************
               Analyser
**********************************************)

let first_file = ref true

let anal_file s0 =
  if not (!first_file) then
    Parsing_helper.user_error "You can analyze a single ProVerif file for each run of ProVerif.\nPlease rerun ProVerif with your second file.";
  first_file := false;
  let s =
    (* Preprocess .pcv files with m4 *)
    let s_up = String.uppercase_ascii s0 in
    if Terms.ends_with s_up ".PCV" then
      let s' = Filename.temp_file "pv" ".pv" in
      let res = Unix.system("m4 -DProVerif " ^ s0 ^ " > " ^ s') in
      match res with
        Unix.WEXITED 0 -> s'
      | _ -> Parsing_helper.user_error ("Preprocessing of " ^ s0 ^ " by m4 failed.")
    else
      s0
  in
  let in_front_end =
    match !in_kind with
    | Default -> (* Set the front-end depending on the extension of the file *)
       let s_up = String.uppercase_ascii s in
       if Terms.ends_with s_up ".PV" then PiType else
       if Terms.ends_with s_up ".PI" then Pi else
       if Terms.ends_with s_up ".HORNTYPE" then HornType else
       Horn (* Horn is the default when no extension is recognized for compatibility reasons *)
    |	x -> x
  in

  if (!Param.html_output) then
    begin
      Display.LangHtml.openfile ((!Param.html_dir) ^ "/index.html") "ProVerif: main result page";
      Display.Html.print_string "<H1>ProVerif results</H1>\n"
    end;
  begin
    match in_front_end with
      Default ->
	Parsing_helper.internal_error "The Default case should have been removed previously"
    | Horn ->
	(* If the input consists of Horn clauses, no explanation can be given *)
	Param.verbose_explain_clauses := Param.Clauses;
	Param.explain_derivation := false;
	Param.abbreviate_clauses := false;
	horn_solve (Syntax.parse_file s)
    | HornType ->
	(* If the input consists of Horn clauses, no explanation can be given *)
	Param.verbose_explain_clauses := Param.Clauses;
	Param.explain_derivation := false;
	Param.abbreviate_clauses := false;
	Param.typed_frontend := true;
	(* Param.ignore_types := false; *)
	horn_solve (Tsyntax.parse_file s)
    | SpassIn ->
	Parsing_helper.user_error "spass input not yet implemented"
    | PiType ->
        Param.typed_frontend := true;
        let pi_state0 = Pitsyntax.parse_file s in
        let pi_state1 = move_new pi_state0 in
        let pi_state2 = Simplify.prepare_process pi_state1 in
        TermsEq.record_eqs_with_destr pi_state2;

        (* Check if destructors are deterministic *)
        Destructor.check_deterministic pi_state2.pi_destructors_check_deterministic;

	(* Check that the disequations are valid *)
	check_disequations pi_state2.pi_disequations;
	
	(* Display the process(es) *)
	if not (Param.is_equivalence_two_processes pi_state2) then
	  (* Start from process 0 in display *)
	  decr Param.process_number;
	display_process pi_state2;
	
	let pi_state3 = transl_query pi_state2 in
        if (!Param.html_output) then
          Display.Html.print_string "<UL>\n";
	Encode_queries.encode_secret_public_vars prove_queries pi_state3;
		(* The transformations that the encoding can make on the process are strongly limited:
		   They must not change the type of the arguments of names. 
		   That seems plausible, but remains to be tested in more detail.
		   If the arguments of names change, I need to reset them by setting
		   their type to Param.tmp_type. Simplify.prepare_process does that. 
		   For deeper transformation, I may need to reset need_vars_in_names. *)
        if (!Param.html_output) then
          Display.Html.print_string "</UL>\n"
    | Pi ->
	let pi_state0 = Pisyntax.parse_file s in
	let pi_state1 = move_new pi_state0 in
	TermsEq.record_eqs_with_destr pi_state1;

	(* Check if destructors are deterministic *)
	Destructor.check_deterministic pi_state1.pi_destructors_check_deterministic;

	(* Display the original process *)
	decr Param.process_number;
	display_process pi_state1;

	let pi_state2 = transl_query pi_state1 in
        if (!Param.html_output) then
          Display.Html.print_string "<UL>\n";
	prove_queries pi_state2;
        if (!Param.html_output) then
          Display.Html.print_string "</UL>\n"
	  
  end;
  if (!Param.html_output) then
    Display.LangHtml.close();
  (* Remove the preprocessed temporary file when everything went well *)
  if s0 <> s then
    Unix.unlink s
    


let _ =
  Printexc.record_backtrace true;
  try
    Arg.parse
    [ "-test", Arg.Unit (fun () ->
        if !Param.tulafale == 0 then
          Param.verbose_explain_clauses := Param.ExplainedClauses),
        "\t\tdisplay a bit more information for debugging";
      "-in", Arg.String(fun s -> in_kind := up_in s),
        "<format> \t\tchoose the input format (horn, horntype, spass, pi, pitype)";
      "-out", Arg.String(fun s -> Arg_params.out_kind := up_out s),
        "<format> \tchoose the output format (solve, spass, tptp)";
      "-tag-out", Arg.Unit (fun () -> Arg_params.tag_in_out := true),
      "\t\ttag output messages";
      "-log-pv", Arg.Unit (fun () -> Arg_params.log_pv := true),
      "\t\tsave the ProVerif AST actually used after potential processing as infile.export";
      "-log-pv-only", Arg.Unit (fun () -> Arg_params.log_pv := true; Arg_params.exit_after_log_pv := true),
      "\t\tsave the ProVerif AST going to be used after potential processing as infile.export then exit";
      "-o", Arg.String(fun s -> out_file := s),
        "<filename> \tchoose the output file name (for spass output)";
      "-lib", Arg.String (fun s -> Param.lib_name := s),
        "<filename> \tchoose the library file (for pitype front-end only)";
      "-TulaFale", Arg.Int(fun n ->
	Param.tulafale := n;
	if n = 1 then
	  begin
	    Param.reconstruct_trace := false;
	    Param.verbose_explain_clauses := Param.Clauses;
	    Param.explain_derivation := false;
	    Param.abbreviate_derivation := false;
	    Param.redundant_hyp_elim := true;
	    Param.redundant_hyp_elim_begin_only := true
	  end
	    ),
        "<version> \tindicate the version of TulaFale when ProVerif is used inside TulaFale";
      "-graph", Arg.String (fun s ->
	Param.graph_output := true;
        Param.trace_display_graphicx := Param.GraphDisplay;
	Param.html_dir := s),
      "\t\t\tcreate the trace graph from the dot file in the directory specified";
      "-commandLineGraph", Arg.String (fun s ->
        Param.command_line_graph_set := true;
        Param.command_line_graph := s;),
      "\t\t\tDefine the command for the creation of the graph trace from the dot file";
      "-gc", Arg.Set gc,
        "\t\t\tdisplay gc statistics";
      "-color", Arg.Set Param.ansi_color,
      "\t\t\tuse ANSI color codes";
      "-html", Arg.String (fun s ->
	Param.html_output := true;
	Param.html_dir := s;
	if !Param.tulafale == 0 then
          Param.verbose_explain_clauses := Param.ExplainedClauses),
        "\t\t\tHTML display"
    ]
    anal_file ("Proverif " ^ Version.version ^ ". Cryptographic protocol verifier, by Bruno Blanchet, Vincent Cheval, and Marc Sylvestre");
    if !gc then Gc.print_stat stdout
  with
  | InputError(mess, ext) ->
      Parsing_helper.display_input_error mess ext
  | e ->
    begin
      Printexc.print_backtrace stdout;
      Parsing_helper.internal_error (Printexc.to_string e)
    end
