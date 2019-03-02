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

let debug_print s = ()
   (* print_endline s *)

let max_proc_nb = 1024

let cur_proc_nb = ref 1

let get_proc_nb () = !cur_proc_nb

let up_proc_nb int = cur_proc_nb := int

let no_more_proc () = get_proc_nb () >= max_proc_nb

(* [get_proc state n] Return the n-th process in state.subprocess *)
let get_proc state n =
  let (proc, _, _, _, _) = List.nth state.subprocess n in
  proc

(* Ask for a recipe for the term t. Add (recipe, t) to !cur_state.public if the recipe is found.
   Return the new state and the expansion of the recipe if the evaluation doesn't fail.
   otherwise raise WrongChoice *)
let rec get_recipe_of_term question_text t =
    let state = Menu_helper.get_state () in
    try
      auto_cleanup (fun () ->
          let recipe = Menu_helper.get_recipe "" question_text in
          let expand = Evaluation_helper.term_evaluation_fail (Menu_helper.expand_recipe state.pub_vars state.public recipe) in
          if Reduction_helper.equal_terms_modulo t expand then
	    let state' = Evaluation_helper.add_public_with_recipe state (recipe, expand) in
	    let (new_pub, pub_vars) = Menu_helper.get_new_vars state state'.public in
            { state' with
              pub_vars = pub_vars;
              comment = RAddpub new_pub;
              previous_state = Some state}
        else
          Parsing_helper.user_error ("The recipe you have given evaluates to " ^
		      (Display_interact.GtkInteract.display_term expand) ^
		      " which is different from " ^
		      (Display_interact.GtkInteract.display_term t))
	    )
    with
    | Unify -> Parsing_helper.user_error "The evaluation of the recipe fails"
    | Menu_helper.WarningsAsError -> get_recipe_of_term question_text t

(* Functions doing reduction steps *)

let do_repl state n p =
  debug_print "Doing Repl";
  {
    state with
      subprocess = Reduction_helper.add_at n (Menu_helper.sub_of_proc p) state.subprocess;
      previous_state = (Some state);
      comment = (RRepl (n, 2 ))
  }

let get_previous_state already_public state = state
(*  if already_public then
    state
  else
    match state.previous_state with
      Some state' -> state'
    | None -> Parsing_helper.internal_error "get_previous_state" *)

(* [do_public_input state n tin pat p already_public] Do a public input. *)
(* If [already_public] is true, then this function is used when the canal is public. *)
(* Otherwise, it is used after giving the recipe for the private channel *)
let rec do_public_input state n tin pat p already_public =
  let get_recipe_and_expand state =
    try
      auto_cleanup (fun () ->
        let c = Menu_helper.get_recipe "" ("Give recipe to input on channel" ^ "\n" ^ (Display_interact.GtkInteract.display_term tin) ^ ":\n")  in
        let exp = Menu_helper.expand_recipe state.pub_vars state.public c in
        let t' = Evaluation_helper.term_evaluation_fail exp in
        (c, t'))
    with Unify ->
      Parsing_helper.user_error "The evaluation of the recipe fails"
  in
  let (recipe, expand) =
    get_recipe_and_expand state
  in
  try
    auto_cleanup (fun () ->
      Evaluation_helper.match_pattern pat expand;
      let p' = auto_cleanup (fun () -> Reduction_helper.copy_process p) in
      { state with
          subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc p') state.subprocess;
          comment = RInput(n, tin, pat, recipe, expand);
          previous_state = Some (get_previous_state already_public state)
        })
  with
| Unify ->
      if not (Terms.equal_types (Terms.get_pat_type pat) (Terms.get_term_type expand)) then
	ignore (GToolbox.question_box "Input failed" ["OK"] "The input failed because the received message is not of the expected type." )
      else
	ignore (GToolbox.question_box "Input failed" ["OK"] "The input failed because the pattern-matching failed.");
      { state with
          subprocess = Reduction_helper.remove_at n state.subprocess;
          comment = RInput2(n, tin, pat, recipe, expand);
         previous_state = Some (get_previous_state already_public state)
       }

(* [do_fail_input] performs an input in which the evaluation
   of the channel fails *)
let do_fail_input state n tc pat =
  { state with
      subprocess =   Reduction_helper.remove_at n state.subprocess;
      comment = RInput3(n, tc, pat);
      previous_state = Some state
      }

(* [do_public_output state n tc t p occ already_public] Do a public output,
   or an output in which the channel or the message fails. *)
(* If [already_public] is true, then this function is used when the canal is public. *)
(* Otherwise, it is used after giving the recipe for the private channel *)
let do_public_output state n tc t p occ already_public =
  debug_print "Doing Out";
  try
    auto_cleanup (fun () ->
      let tc' = Evaluation_helper.term_evaluation_fail tc in
      let t' = Evaluation_helper.term_evaluation_fail t in
      assert (Evaluation_helper.is_in_public state.public tc' != None);
      let p' = auto_cleanup (fun () -> Reduction_helper.copy_process p) in
      let (n_b, state') = Evaluation_helper.add_public state t' in
      let (_, pub_vars) = Menu_helper.get_new_vars state state'.public in
      { state' with
          subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc p') state.subprocess;
          comment = ROutput1(n, tc, n_b, t);
          pub_vars = pub_vars;
          previous_state = Some (get_previous_state already_public state) }
      )
  with Unify ->
    { state with
        subprocess = Reduction_helper.remove_at n state.subprocess;
        comment = ROutput2(n, tc, t);
        previous_state = Some (get_previous_state already_public state) }

let do_insert state n t p =
  let rec insert_in acc t = function
      [] -> List.rev (t::acc)
    | (FunApp(f, fl) as t')::tl as tables ->
       begin
         match t with
         | FunApp(f',_) ->
            if f'.f_name < f.f_name then
              List.rev_append acc (t::tables)
            else
              if f'.f_name > f.f_name then
                insert_in (FunApp(f, fl)::acc) t tl
              else
                if Terms.equal_terms t t' then
                  List.rev_append acc tables
                else
                  insert_in (FunApp(f, fl)::acc) t tl
         | _ -> assert false
       end
    | _ -> assert false
  in
  try
    begin
      auto_cleanup
        (fun () ->
	  let t' = Evaluation_helper.term_evaluation_fail t in
	  { state with
            subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc p) state.subprocess;
	    tables = insert_in [] t' state.tables;
	    comment = RInsert1(n, t, false);
	    previous_state = Some state }
        )
    end
  with Unify ->
    { state with
      subprocess = Reduction_helper.remove_at n state.subprocess;
      comment = RInsert2(n, t);
      previous_state = Some state }

let do_nil state n =
      { state with
        subprocess = Reduction_helper.remove_at n state.subprocess;
        comment = RNil(n);
        previous_state = Some state}

let do_par state p q n =
  debug_print "Doing Par";
  { state with
    subprocess = Reduction_helper.add_at n (Menu_helper.sub_of_proc p) (Reduction_helper.replace_at n (Menu_helper.sub_of_proc q)
                                             state.subprocess);
    comment = RPar(n);
    previous_state = Some state }

let do_restr state na env args p n =
  debug_print "Doing Restr";
  let na' = Terms.create_name na.f_orig_name (Terms.fresh_id na.f_name) ([], snd na.f_type) true in
  let n' = FunApp(na', []) in
  let p' = Reduction_helper.process_subst p na n' in
  { state with
    subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc p') state.subprocess;
    comment = RRestr(n, na, n');
    previous_state = Some state }

let do_event state t n p =
  try
    auto_cleanup
      (fun () ->
          let t = Evaluation_helper.term_evaluation_fail t in
          { state with
            subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc p) state.subprocess;
            comment = REvent1(n, t, false);
            previous_state = Some state;
            events = t::state.events
      })
  with Unify ->
    { state with
      subprocess = Reduction_helper.remove_at n state.subprocess;
      comment = REvent2(n, t);
      previous_state = Some state}

let do_let state pat t p q n =
  debug_print "Doing Let";
  try
    auto_cleanup (fun () ->
      let t' = Evaluation_helper.term_evaluation_fail t in
      Evaluation_helper.match_pattern pat t';
      let p' = auto_cleanup (fun () -> Reduction_helper.copy_process p) in
      { state with
        subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc p') state.subprocess;
        comment = RLet1(n, pat, t);
        previous_state = Some state}
    )
  with Unify ->
    { state with
      subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc q) state.subprocess;
      comment = RLet2(n, pat, t);
      previous_state = Some state}

let do_test state t p q n =
        debug_print "Doing Test";
        try
          auto_cleanup (fun () ->
            let t' = Evaluation_helper.term_evaluation_fail t in
            if Reduction_helper.equal_terms_modulo t' Terms.true_term then
              { state with
                subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc p) state.subprocess;
                comment = RTest1(n, t);
                previous_state = Some state;
              }
            else
              { state with
                subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc q) state.subprocess;
                comment = RTest2(n, t);
                previous_state = Some state;
              }
          )
        with Unify ->
            { state with
              subprocess = Reduction_helper.remove_at n state.subprocess;
              comment = RTest3(n, t);
              previous_state = Some state;
            }

let do_get state pat mess_term t n p =
  Terms.auto_cleanup(fun () ->
  Evaluation_helper.match_pattern pat mess_term;
  let p' = auto_cleanup (fun () -> Reduction_helper.copy_process p) in
  { state with
    subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc p') state.subprocess;
    comment = RGet(n, pat, t, mess_term);
    previous_state = Some state
  })

let do_rio t pat p q n_input n_output tin state =
  debug_print "do rio";
  Menu_helper.set_io_c Other;
  try
    Terms.auto_cleanup (fun () ->
      (* The evaluation of the message [t] always succeeds
	 because when it fails, the output is automatically removed *)
      let t' = Evaluation_helper.term_evaluation_fail t in
      Evaluation_helper.match_pattern pat t';
      let q'' = auto_cleanup (fun () -> Reduction_helper.copy_process q) in
      { state with
        subprocess = Reduction_helper.replace_at (n_input) (Menu_helper.sub_of_proc q'') (Reduction_helper.replace_at n_output (Menu_helper.sub_of_proc p) state.subprocess);
        comment = RIO(n_input, tin, pat, n_output, tin, None, t', false);
        previous_state = Some state })
  with Unify ->
        debug_print "doing RIO2";
        { state with
          subprocess = Reduction_helper.remove_at (n_input) (Reduction_helper.replace_at n_output (Menu_helper.sub_of_proc p) state.subprocess);
          comment = RIO2(n_input, tin, pat, n_output, tin, None, t, false);
          previous_state = Some state }

let do_phase state n =
  debug_print ("Doing Phase " ^(string_of_int n));
  if n <= state.current_phase then
    Parsing_helper.user_error "Phases should be in increasing order.";
  { state with
    subprocess = Evaluation_helper.extract_phase n state.subprocess;
    current_phase = n;
    comment = RPhase(n);
    previous_state = Some state
  }

(* Do the reduction of the n-th process of state.subprocess which *)
(* is proc. This function doesn't treat the case LetFilter yet. NamedProcess reductions are done *)
(* automatically *)
let rec do_auto_reduction state n proc =
  let n_state =
    match proc with
    | Repl(p,occ) -> do_repl state n p
    | Insert(t,p,_) -> do_insert state n t p
    | Nil -> do_nil state n;
    | Par(p, q) -> do_par state p q n
    | Restr(na, (args, env), p, occ) -> do_restr state na env args p n
    | Let(pat, t, p, q, occ) -> do_let state pat t p q n
    | Test(t, p, q, occ) -> do_test state t p q n
    | Output(tc,t,p,occ) -> do_public_output state n tc t p occ true
    | Input(tc,pat,p,occ) -> do_fail_input state n tc pat
    | Event(t, _, p, _) ->
       do_event state t n p
    | _ -> raise Menu_helper.WrongChoice
  in
  Menu_helper.delete_NamedProcess n_state

(* [show_terms termsl] Display the terms in  termsl in a for of a store. It allows the user to click *)
(* on one term, and update [choice_term] with this term. *)
let show_terms termsl frz dfrz =
  let window = GWindow.dialog ~modal:true ~title:"Double-click on a term" ~width:300 ~height:300 ~border_width:0 () in
  window#misc#modify_bg [(`NORMAL, `WHITE)];
  let destroy_win () =
    window#destroy();
    GMain.Main.quit()
  in
  frz();
  let choice_term = ref None in
  let cols = new GTree.column_list in
  let col = cols#add Gobject.Data.string in
  let create_model labl =
    let store = GTree.list_store cols in
    let fill l =
      let iter = store#append () in
      store#set ~row:iter ~column:col l
    in
    List.iter fill labl;
    store
  in
  (* Function called when a double click is made on a row *)
  let on_row_activated (view:GTree.view) path column =
    let row_nb = int_of_string (GTree.Path.to_string path) in
    choice_term := Some (List.nth termsl row_nb);
    window#destroy()
  in
  let create_view ~model ~packing =
    let view = GTree.view ~headers_visible:false  ~packing ~model  () in
    view#selection#set_mode `SINGLE;
    let col_v =  GTree.view_column ~renderer:(GTree.cell_renderer_text [], ["markup", col]) () in
    let _ = view#append_column col_v in
    let _ = view#connect#row_activated ~callback:(on_row_activated view) in
    view#coerce
  in
  let labl = List.map Display_interact.GtkInteract.display_term termsl in
  let _ =  window#connect#destroy ~callback:destroy_win in
  let scrolled_window = GBin.scrolled_window ~border_width:10
    ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~packing:window#vbox#add () in
  let main_vbox = GPack.vbox ~packing:scrolled_window#add_with_viewport () in
  let model = create_model labl in
  let _ = create_view ~model ~packing:main_vbox#pack in
  let cancel_b = GButton.button ~stock:`CANCEL  ~packing:window#action_area#add () in
  let _ = cancel_b#connect#clicked ~callback:destroy_win in
  window#show ();
  GMain.Main.main();
  !choice_term

(* Make a manual reduction of the nth process in state.subprocess (proc), reduct renaming NamedProcess *)
let do_manual_reduction state n proc frz dfrz =
  (* Function for RIO cases *)
  let quest_io io tin set_tio func =
    let ans =  GToolbox.question_box ("Private " ^ io) ["1) Channel is public"; "2) Private communication"; "Cancel"] ("Either: \n 1) The channel " ^ Display_interact.GtkInteract.display_term tin ^ " is in fact public. Give a recipe to prove that. \n 2) Make a communication on the private channel " ^ Display_interact.GtkInteract.display_term tin ^ ".\n      You will then choose the process to communicate with.") in
    begin
      match ans with
      | 1 ->
         let n_state = get_recipe_of_term ("Give a recipe for the channel:\n" ^ Display_interact.GtkInteract.display_term tin) tin in
         func n_state
      | 2 ->
         let data = Menu_helper.get_data () in
	 if List.exists (fun (_,x) -> Menu_helper.equal_io_oi x set_tio) data.titles then
           let _ = Menu_helper.set_io_c (set_tio) in
           state
	 else
           let _ =   GToolbox.question_box "Error" ["OK"] "No Reduction possible on this private channel" in
           state
      | _ ->  state
    end
  in
  let n_state = match Menu_helper.get_io_c () with
    | Other ->
       begin
         match proc with
         | Repl(p,occ) -> do_repl state n p
         | Phase(n, p, _) -> do_phase state n
         | Input(tin, pat, p, _) ->
             begin
	       try
		 let tin' = Evaluation_helper.term_evaluation_fail tin in
		 match Evaluation_helper.is_in_public state.public tin' with
		 | Some _ ->  do_public_input state n tin pat p true
		 | _ ->
                     let fun_1 n_state = do_public_input n_state n tin pat p false in
                     quest_io "Input" tin (I_O (tin, n, pat, p)) fun_1
	       with Unify ->
		 do_fail_input state n tin pat
            end
         | Output(tc, t, p, occ) ->
            let fun_1 state = do_public_output state n tc t p occ false in
            quest_io "Output" tc (O_I (tc, (n), t, p)) fun_1
         | Insert(t,p,_) ->
            do_insert state n t p
         | Get(pat, t, p, q, occ) ->
            (* 3 cases are possible: *)
            (* - There could be no term in [state.tables] that satisfying the pattern, *)
            (* in which case, q is executed. *)
            (* - There could be only one term that matches the pattern with a substitution \sigma, *)
            (* in which case p\sigma is executed *)
            (* - There could be several terms that matches the pattern. In this case, the possible terms are *)
            (* displayed using [show_terms], and the reduction is made. *)
            (* [match_terms_lst] contains all the terms in state.table that match the pattern with a substitution \sigma *)
            (* such that t\sigma is true will be on match_terms_lst *)
            let match_terms_lst =
              List.filter (fun term ->
                  try
                    Terms.auto_cleanup(fun () ->
                        Evaluation_helper.match_pattern pat term;
                        let t' = Evaluation_helper.term_evaluation_fail t in
	                Reduction_helper.equal_terms_modulo t' true_term)
                  with Unify -> false) state.tables in
            begin
              match match_terms_lst with
              | [] -> (* The else branch is taken: q is executed *)
                 debug_print "Doing Get1";
                 { state with
                   subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc q) state.subprocess;
                   comment = RGet2(n, pat, t);
                   previous_state = Some state
                 }
              | mess_term::[] -> (* Only one choice, p\sigma is executed *)
                 do_get state pat mess_term t n p;
              | termsl ->
                 let t' = show_terms termsl frz dfrz in
                 match t' with
                   None -> state
                 | Some mess_term -> do_get state pat mess_term t n p
            end
         | _ -> state
       end
    | I_O(tin, n_input, pat, q) -> (* Input on the private channel tin has been made *)
       begin
         match proc with
         | Output(_, t, p, _) ->
            do_rio t pat p q n_input (n) tin state
         | _ -> failwith "RIO"
       end
    | O_I(tc, n_output, t, p) -> (* Output on a the private channel tc has been made *)
       begin
         match proc with
         | Input(_, pat, q, _) ->
            do_rio t pat p q n n_output tc state
         | _ -> failwith "RIO"
       end
  in
  Menu_helper.delete_NamedProcess n_state

(* [do_one_reduction_step state n] Do one reduction step for the nth subprocess of n *)
let rec do_one_reduction_step state n frz dfrz =
  Menu_helper.reset_forward_lst ();
  let proc = get_proc state n in
  let aux state n proc =
    if Menu_helper.is_auto_reductible state proc then
      do_auto_reduction state n proc
    else
      do_manual_reduction state n proc frz dfrz
  in
  match proc with
  | Repl(_, _) | Par(_, _) ->
     if no_more_proc () then
       let _ = GToolbox.message_box ~title:"Error" "Too much processes to do this reduction" in
         state
     else
       aux state n proc
  | _ -> aux state n proc

(* [do_all_auto_reduction state] Do all auto-reductions on state *)
let do_all_auto_reduction state =
  Menu_helper.reset_forward_lst ();
  let proc_nb = ref (List.length state.subprocess) in
  let rec aux state  = function
    | n when n = !proc_nb -> state
    | n ->
       let proc = get_proc state n in
       if Menu_helper.is_auto_reductible state proc then
	 let state' = do_auto_reduction state n proc in
	 proc_nb := List.length state'.subprocess;
         aux state' n
       else
         aux state (n + 1)
  in
  aux state 0
