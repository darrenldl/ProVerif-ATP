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
open GMain
open GdkKeysyms
open Types
open Pitypes
open Terms

exception WrongChoice

let debug_print s = () 
  (* print_endline s *)

(* [initialize_state ()] Initialize or reset [cur_state] *)
let initialize_state () =
  { goal = NoGoal;
    subprocess = [];
    public = [];
    pub_vars = [];
    tables = [];
    prepared_attacker_rule = [];
    io_rule = [];
    previous_state = None;
    hyp_not_matched = [];
    assumed_false = [];
    current_phase = 0;
    comment = RInit;
    events = [];
    barriers = []}

(* [cur_state] A reference on the curent state given first by the parsing of the selected file. *)
(* This reference changes after every reduction step *)
let cur_state = ref (initialize_state ())

(* [get_state ()] Return the current state *)
let get_state () = !cur_state

(* [sub_of_proc proc] Return the subprocess corresponding to [proc] *)
let sub_of_proc proc = (proc, [], [], [], Nothing)

(* [proc_of_sub proc] Return the process corresponding to [sub] *)
let proc_of_sub sub =
  let (p, _, _, _, _) = sub in
  p

(* [get_proc state n] Return the n-th process in state.subprocess *)
let get_proc state n =
  let (proc, _, _, _, _) = List.nth state.subprocess n in
  proc

(* [get_proc_list state] Return the list of process obtain from state.subprocess *)
let get_proc_list state =
  let rec aux acc = function
      [] -> List.rev acc
    | (proc, _, _, _, _)::tl -> aux (proc::acc) tl
  in
  aux [] state.subprocess

(* [only_one_proc state] Return true if state.suprocess contains only one process, false otherwise. *)
let only_one_proc state = match state.subprocess with
  | p::[] -> true
  | _ -> false

(* [is_auto_reductible state p] Return true if the p is auto reductible, according to state, *)
(* false otherwise *)
let is_auto_reductible state p =
  match p with
  | Nil | Par(_, _) | Restr(_, _, _, _) | Let(_, _, _, _, _)
  | NamedProcess(_ , _, _) | Event( _, _, _, _) | Test(_, _, _, _) -> true
  | Output(tc, t, _, _)  ->
    begin
      try
        let tc' = Evaluation_helper.term_evaluation_fail tc in
        let _ = Evaluation_helper.term_evaluation_fail t in
        match Evaluation_helper.is_in_public state.public tc' with
        | None -> false
        | Some _ -> true
      with Unify ->
        true
    end
  | Input(tc, _, _, _) ->
     begin
      try
        let _ = Evaluation_helper.term_evaluation_fail tc in
	false
      with Unify ->
        true
     end
  | Insert (t, _, _)->
      begin
	try
	  let _ = Evaluation_helper.term_evaluation_fail t in
	  only_one_proc state
	with Unify ->
	  true
      end
  | _ -> false

(* List of forwards steps done previously *)
let forwards_lst = ref []

(* True if a forward step is possible ([exists_forward ()] *)
(* can be false, if one step has been made, and one backward) *)

let exists_forward () = !forwards_lst <> []

let reset_forward_lst () =
  forwards_lst := []

let add_to_forwards_lst state =
  forwards_lst := state::(!forwards_lst)


(* [string_of_proc_first_line state proc] Return the string witch will be displayed in the first *)
(* column of the store to represent [proc], in respect to [state] *)
let string_of_proc_first_line state proc =
  match proc with
  | Nil -> "Nil"
  | Par(_, _) ->  "Par"
  | Repl(_, _)-> "Replication"
  | Restr(_, _, _ , _) -> "Restriction"
  | Test(_, _, _, _) -> "Test"
  | Input(tin, _, _, _) ->
    begin
      try
        let tin' = Evaluation_helper.term_evaluation_fail tin in
        match Evaluation_helper.is_in_public state.public tin' with
        | None -> "Input (private)"
        | Some _ -> "Input (public)"
      with Unify ->
        "Input (channel fails)"
    end
  | Output(tc, _, _, _) ->
    begin
      try
        let tc' = Evaluation_helper.term_evaluation_fail tc in
        match Evaluation_helper.is_in_public state.public tc' with
        | None -> "Output (private)"
        | Some _ -> "Output (public)"
      with Unify ->
        "Output (channel fails)"
    end
  | Let(_, _, _, _, _) -> "Let"
  | LetFilter(_, _, _, _, _) -> "let...suchthat"
  | Event(_, _, _, _) -> "Event"
  | Insert(_, _, _)-> "Insert"
  | Get(_, _, _, _, _) -> "Get"
  | Phase(_, _, _) -> "Phase"
  | NamedProcess(s, _, _) -> "Process" ^ s
  | _ -> "Other"


let equal_io_oi x y =
  match x, y with
  | (I_O (cin, _, _, _), O_I (cout, _, t, _))
  | (O_I (cout, _, t, _), I_O (cin, _, _, _)) ->
      begin
	try
          let cin' = Evaluation_helper.term_evaluation_fail cin in
          let cout' = Evaluation_helper.term_evaluation_fail cout in
          let _ = Evaluation_helper.term_evaluation_fail t in
	  Reduction_helper.equal_terms_modulo cin' cout'
	with Unify ->
	  false
      end
  | _ -> false

let string_of_events t = Display_interact.GtkInteract.display_term t

(* [get_data_from_state ()] Return the data associated to the current state. *)
let get_data_from_state () =
  let string_lst_of_barriers barriers = [] (* TO DO *)
  in
  let state = get_state () in
  let exists_auto = ref false in
  let plst = get_proc_list state in
  let rec aux n tlst plst = function
    | [] -> (List.rev tlst, List.rev plst)
    | p::tl ->
       begin
         if is_auto_reductible state p then
           exists_auto := true;
         let pt = string_of_proc_first_line state p in
         let sp = List.rev (Display_interact.GtkInteract.display_process p) in
         let is_io_p = match p with
             Input (tin, pat, p, _) -> I_O (tin, n, pat, p)
           | Output (tou, t, q, _) -> O_I (tou, n, t, q)
           | _ -> Other in
         aux (n + 1) ((pt,is_io_p)::tlst) (sp::plst) tl
       end
  in
  let last_id = ref None in
  let add_space_if_needed tables =
    let rec aux acc = function
      [] -> List.rev acc
    | hd::tl ->
       begin
         match hd with
           FunApp(f, _) as t ->
            let t' = Display_interact.GtkInteract.display_term t in
            begin
              match !last_id with
                None ->
               last_id := Some f.f_name;
               aux (t'::acc) tl
              | Some(f') ->
                 if not (f.f_name = f') then
                   begin
                     last_id := Some f.f_name;
                     aux (t'::""::acc) tl
                   end
                 else
                   aux (t'::acc) tl
            end
         | _ -> failwith "add_space_if_needed"
       end
    in
    aux [] tables
  in
  let tables_lst = add_space_if_needed state.tables in
  let public_lst = Display_interact.GtkInteract.display_public state.public state.pub_vars in
  let barriers_lst = string_lst_of_barriers () in
  let (titles, proc_llst) = aux (-3) [] [] plst in (* -3 since there is columns titles, events and tables *)
  let events_lst = List.rev_map string_of_events state.events in
  {tables_lst; public_lst; titles =("Tables", Other)::("Events", Other)::("Public", Other)::titles; proc_llst; no_auto = not !exists_auto; events_lst; barriers_lst}

(* [cur_data] Reference on the current data associated to [!cur_state] *)
let cur_data = ref (get_data_from_state ())

(* [get_data ()] Return the current data associated to the current state *)
let get_data () = !cur_data

(* [is_first_step ()] Return true if the current state is the initial state, false otherwise *)
let is_first_step () =
  let rec aux state = match state.previous_state, state.comment with
      None, _ -> true
    | Some (s), RNamedProcess(_) -> aux s
    | _ -> false
  in
  aux (!cur_state)


(* [exists_auto ()] Return true if there exists a auto-reductible process *)
(* in one of the subprocess of the current state, false otherwise *)
let exists_auto () = not (!cur_data.no_auto)

(* [update_cur_state state] Update the current state with [state], and the *)
(* current data associated to it *)
let update_cur_state state =
  cur_state := state;
  cur_data := get_data_from_state ()

(* [dialog_box title string ()] Create a dialog box with title *)
(* [title], displaying [string]. *)
(* Return the string entered by the user, *)
(* raise WrongChoice if no string is entered. *)
let dialog_box title string () =
  let db = GToolbox.input_string ~title ~text:"" string in
  match db  with
    Some s -> s
  | None -> raise WrongChoice

(* [reset_env ()] Reset the global environment, clear tables, restore some parameters. *)
(* Used to load a new file *)
let reset_env () =
  cur_state := initialize_state ()

(* [input_error_box b mess ext] Create a message box with title "Error in your Recipe", and one *)
(* button. The message displayed is comming from an InputError(mess, ext) exception. If [b] *)
(* is true, the the message display the line number and the character number of the error. *)
(* Otherwise, its only display the character number *)
let input_error_box b mess ext =
  let mess' = Parsing_helper.get_mess_from b "Error: " mess ext in
  let _ =  GToolbox.question_box "Error" ["OK"] mess' in
  ()

(* [get_binder_name b] Return the string associated to the binder [b] *)
let get_binder_name b =
  if b.vname = 0 then b.sname else  b.sname ^ "_" ^ (string_of_int b.vname)

(* [add_var_env env b] Add the binder [b] to [env] *)
let add_var_env env b =
  let s = get_binder_name b in
  Stringmap.StringMap.add s (EVar b) env

let args_to_string tl =
  let l = List.length tl in
  if l=0 then
    "0 argument"
  else if l=1 then
    "1 argument of type " ^ (Terms.tl_to_string ", " tl)
  else
    (string_of_int l) ^ " arguments of types " ^ (Terms.tl_to_string ", " tl)

let type_compatible ty1 ty2 =
  ty1 == ty2 || (Param.get_ignore_types() && (ty1 == Param.any_type || ty2 == Param.any_type))

let rec compatible_lists l1 l2 =
  match l1,l2 with
    [],[] -> true
  | a1::q1,a2::q2 -> (type_compatible a1 a2) && (compatible_lists q1 q2)
  | _,_ -> false

let type_error mess ext =
  if Param.get_ignore_types() then
    Parsing_helper.input_warning (mess ^ (Parsing_helper.add_point_if_necessary mess) ^
				  "\nThis is acceptable because types are ignored.") ext
  else
    Parsing_helper.input_error mess ext

let rec split_string s =
  try
    let pos_first_dash = String.index s '-' in
    let s1 = String.sub s 0 pos_first_dash in
    let s2 = String.sub s (pos_first_dash+1) (String.length s -pos_first_dash-1) in
    s1 :: split_string s2
  with Not_found ->
    [s]

let rec id_list_to_types = function
    [] -> raise Not_found
  | ["tuple"] -> []
  | [_] -> raise Not_found
  | a::r ->
      let ty = List.find (fun t -> t.tname = a) (!Param.current_state).pi_types in
      let ty_r = id_list_to_types r in
      ty::ty_r

let rec check_eq_term env (term,ext) =
  match term with
  | Pitptree.PFail -> None
  | (Pitptree.PIdent (s,ext)) ->
    let t =
      try
	match Stringmap.StringMap.find s env with
	| EVar v -> Var v
	| EFun f ->
	    if fst f.f_type <> [] then
	      Parsing_helper.input_error ("function " ^ s ^ " expects " ^
					  (string_of_int (List.length (fst f.f_type))) ^
					  " arguments but is used without arguments") ext;
            if f.f_private then
              Parsing_helper.input_error ("identifier " ^ f.f_name ^ " is private") ext;
            FunApp(f, [])
        | EName r ->
            if r.f_private then
              Parsing_helper.input_error ("identifier " ^ r.f_name ^ " is private") ext;
            FunApp(r, [])
	| _ -> Parsing_helper.input_error ("identifier " ^ s ^ " should be a function, a variable, or a name") ext
      with Not_found ->
	Parsing_helper.input_error ("identifier " ^ s ^ " not defined") ext
    in
    Some (t, Terms.get_term_type t)
  | (Pitptree.PFunApp ((f,ext), tlist)) ->
     begin
       let tol = List.map (check_eq_term env) tlist in
       match f, tol with
	 "=", [to1;to2] ->
	   begin
             match to1, to2 with
             | Some (t1, ty1), Some (t2, ty2) ->
		 if not (type_compatible ty1 ty2) then
		   type_error ("function " ^ f ^ " expects two arguments of same type but is here given " ^ args_to_string [ty1;ty2]) ext;
		 Some(FunApp(Terms.equal_fun ty1, [t1; t2]), Param.bool_type)
             | _ ->
		 Some(get_fail_term Param.bool_type, Param.bool_type)
	   end
       | "<>", [to1;to2] ->
	   begin
	     match to1, to2 with
	     | Some (t1, ty1), Some (t2, ty2) ->
		 if not (type_compatible ty1 ty2) then
		   type_error ("function " ^ f ^ " expects two arguments of same type but is here given " ^
    		          args_to_string [ty1;ty2]) ext;
		 Some(FunApp(Terms.diff_fun ty1, [t1; t2]), Param.bool_type)
             | _ ->
		 Some(get_fail_term Param.bool_type, Param.bool_type)
	   end
       | ("=" | "<>"), _ ->
	   Parsing_helper.input_error (f ^ " expects two arguments") ext
       | "choice", _ ->
	   Parsing_helper.input_error "choice is not allowed in recipes" ext;
       | _ ->
	   try
	     match Stringmap.StringMap.find f env with
               EFun r ->
		 let (tl', tyl) =
		   List.split (List.map2 (fun ty t ->
		     match t with
		     | None -> (get_fail_term ty, ty)
		     | Some (t, ty') -> (t, ty')
			   ) (fst r.f_type) tol)
		 in
		 if (List.length (fst r.f_type)) != List.length tyl then
      		   Parsing_helper.input_error ("function " ^ f ^ " expects " ^
        				       args_to_string (fst r.f_type) ^
        				       " but is here given " ^
        				       args_to_string tyl) ext;
      		 if not (compatible_lists (fst r.f_type) tyl) then
      		   type_error ("function " ^ f ^ " expects " ^
        		       args_to_string (fst r.f_type) ^
        		       " but is here given " ^
        		       args_to_string tyl) ext;
		 if r.f_private then
		   Parsing_helper.input_error ("identifier " ^ r.f_name ^ " is private") ext;
		 if (r.f_options land Param.fun_TYPECONVERTER != 0) && (Param.get_ignore_types()) then
		   match tl' with
		     [t] -> Some (t, snd r.f_type)
		   | _ -> Parsing_helper.input_error ("type converter functions should always be unary") ext
		 else
		   Some (FunApp(r, tl'), snd r.f_type)
	     | x -> Parsing_helper.input_error (f ^ " should be a function") ext
	   with Not_found ->
	     Parsing_helper.input_error (f ^ " not defined") ext
     end
  | (Pitptree.PTuple tlist) ->
    let tl' = List.map (check_eq_term env) tlist in
    let (tl, tyl) =
      List.split (List.map (function
	| None ->
	    let ty = Param.bitstring_type in
	    (get_fail_term ty, ty)
	| Some (t',ty) ->
	    (t', ty)) tl')
    in
    Some (FunApp (Terms.get_tuple_fun tyl, tl), Param.bitstring_type)
  | (Pitptree.PProj((f, ext), t)) ->
      let t' = check_eq_term env t in
      (* f is of the form "<integer>-proj-<identifier>"
	 <integer> is the position of the element extracted by the projection
	 <identifier> is the corresponding tuple function *)
      let f_split = split_string f in
      match f_split with
	n_str :: "proj" :: id_list ->
	  begin
	    let n = int_of_string n_str in
	    let tuple_fun =
	      match id_list with
		[fun_name] ->
		  begin
		    try
		      match Stringmap.StringMap.find fun_name env with
			EFun r when r.f_cat == Tuple ->
			  r
		      | _ ->
			  Parsing_helper.input_error ("Projection " ^ f ^ " should refer to a [data] function") ext
		    with Not_found ->
		      Parsing_helper.input_error ("Function " ^ fun_name ^ " not defined. Projection " ^ f ^ " should refer to a [data] function") ext
		  end
	      | _ ->
		  if Param.get_ignore_types() then
		    (* The default tuple functions are written <n'>-tuple *)
		    match id_list with
		      [n_str'; "tuple"] ->
			begin
			  try
			    let n' = int_of_string n_str' in
			    let tl = Terms.copy_n n' Param.any_type in
			    Terms.get_tuple_fun tl
			  with _ ->
			    Parsing_helper.input_error "After -proj-, we accept either an existing [data] function or a default tuple function written <n>-tuple" ext
			end
		    | _ ->
			Parsing_helper.input_error "After -proj-, we accept either an existing [data] function or a default tuple function written <n>-tuple" ext
		  else
		    (* The default tuple functions are written <typelist>-tuple *)
		    try
		      let tl = id_list_to_types id_list in
		      Terms.get_tuple_fun tl
		    with Not_found ->
		      Parsing_helper.input_error "After -proj-, we accept either an existing [data] function or a default tuple function written <type-list>-tuple" ext
	    in
	    if (n < 1) || (n > List.length (fst tuple_fun.f_type)) then
	      Parsing_helper.input_error ("Component does not exist in projection " ^ f) ext;
	    let proj_fun = Terms.projection_fun (tuple_fun, n) in
	    match t' with
	      Some(t'', ty) ->
		if not (type_compatible ty (snd tuple_fun.f_type)) then
		  type_error ("function " ^ f ^ " expects " ^
        		      args_to_string (fst proj_fun.f_type) ^
        		      " but is here given " ^
        		      args_to_string [ty]) ext;
		Some (FunApp(proj_fun, [t'']), snd proj_fun.f_type)
	    | None ->
		let t'' = Terms.get_fail_term (snd tuple_fun.f_type) in
		Some (FunApp(proj_fun, [t'']), snd proj_fun.f_type)
	  end
      | _ -> Parsing_helper.internal_error "Bad projection name"

exception WarningsAsError

(* [parse_term string] Return the term corresponding to the parsing of [string]. *)
(* Call input_error if the parsing went wrong *)
let parse_term s =
  let state = get_state () in
  let lexbuf = Lexing.from_string s in
  let ptree =
    try
      Pitparser.term Pitlexer.token lexbuf
    with
      Parsing.Parse_error -> Parsing_helper.input_error ("Syntax error") (Parsing_helper.extent lexbuf)
  in
  let global_env =
    match (!Param.current_state).pi_global_env with
    | Set global_env -> global_env
    | Unset ->
	Parsing_helper.internal_error "global_env should be set"
  in
  let pub_vars = state.pub_vars in
  let env = List.fold_left (fun accu var ->
    match var with
      Var x -> add_var_env accu x
    | FunApp(n,[]) ->
	begin
	  match n.f_cat with
	    Name _ -> Stringmap.StringMap.add n.f_name (EName n) accu
	  | _ -> accu
	end
    | _ -> accu) global_env pub_vars
  in
  let term =
    match check_eq_term env ptree with
    | None -> get_fail_term Param.bitstring_type
    | Some(t, _) -> t
  in
  let warnings = Parsing_helper.get_warning_list() in
  if warnings != [] then
    begin
      let messages = String.concat "" (List.map (fun (mess, ext) ->
	(Parsing_helper.get_mess_from false "Warning: " mess ext) ^ "\n") warnings) in
      let messages = messages ^ "Do you want to continue?" in
      match (GToolbox.question_box "Warnings" ["Yes"; "No"] messages ) with
	0 | 1 -> ()
      | _ -> raise WarningsAsError
    end;
  term

(* [delete_NamedProcess state] Return the state obtained after *)
(* applying recursively all the NamedProcess  *)
(* reductions steps to the subprocesses of state that are named *)
let delete_NamedProcess state =
  let proc_nb = List.length state.subprocess  in
  let rec aux state n =
    if n = proc_nb then state
    else
      let proc = get_proc state n in
          match proc with
          | NamedProcess (name, l, p') ->
                 let n_sub = sub_of_proc p' in
                 let n_state =
                   {state with
                     subprocess = Reduction_helper.replace_at n n_sub state.subprocess;
                     comment = RNamedProcess (n, name, l);
                     previous_state = Some state
                   } in
                   aux n_state n;
          | _ -> aux state (n + 1)
  in
  aux state 0

(* Callback function to make a forward step. Update the list of *)
(* forward steps *)
let one_step_forward () =
  match !forwards_lst with
    [] -> !cur_state
  | hd::tl ->
     forwards_lst := List.tl !forwards_lst;
     delete_NamedProcess hd

(* Used for RIO reductions *)
let io_c = ref Pitypes.Other

let set_io_c c = io_c := c

let get_io_c () = !io_c

let ans = ref None

(* [get_recipe public_aux pref text] Display a window with title "Give Recipe, with public elements on the left", and a dialog bog on a right *)
(* [pref] is used to display error messages if the user makes a mistake. *)
(* [text] is the message displayed in the dialog box. *)
(* The user enter a string. This string is parsed to a term. *)
(* If parsing failed, a new dialog window is opened, and the *)
(* parsing error message is shown. The user can enter a new string. *)
(* Otherwise, at the end of the call to [get_recipe_aux], *)
(* the reference [ans] contains [Some(t)] where [t] is the parsed *)
(* term corresponding to the input string (otherwise if the user *)
(* leaves, the ref contains [None]. *)
let rec get_recipe_aux pref text =
 let rec do_ok m_win entry pref text () =
    try
      let str = entry#text in
      ans:= Some (parse_term str);
      m_win#destroy ()
    with
      Parsing_helper.InputError(mess, extent) ->
       let str = entry#text in
       let mess' = Parsing_helper.get_mess_from false "Error: " mess extent in
       let _ = m_win#destroy() in
       if str = "" then
         get_recipe_aux  "" text
       else
         get_recipe_aux ("entry: "  ^ str ^ "\n" ^ mess') text
    | WarningsAsError ->
       let _ = m_win#destroy() in
       get_recipe_aux "" text
  in
  (* Return the scrolled window containing a view with the public *)
  (*  elements of state *)
  let create_public state =
    let s_win = GBin.scrolled_window () in
    let c_lst = new GTree.column_list in
    let col_public = c_lst#add Gobject.Data.string in
    let store = GTree.list_store c_lst in
    let rec fill p =
      let iter = store#append () in
      store#set ~row:iter ~column:col_public p
    in
    List.iter fill (Display_interact.GtkInteract.display_public state.public state.pub_vars);
    let c_p = GTree.view_column ~title:"Public elements" ~renderer:(GTree.cell_renderer_text [], ["text", col_public]) () in
    c_p#set_resizable true;
    let v = GTree.view ~enable_search:false ~width:640  ~packing:(s_win#add) ~model:store () in
    v#selection#set_mode `NONE;
    let _ = v#append_column c_p in
    s_win#coerce
  in
  ans := None;
  let state = get_state () in
  (* Main window *)
  let m_win = GWindow.dialog ~title:"Give recipe"
                 ~width:640 ~height:400 ~allow_shrink:true ~border_width:5 () in
  let _ = m_win#connect#destroy ~callback:(fun () ->
    begin
      m_win#destroy();
      GMain.Main.quit()
    end) in
  let s_win = create_public state in
  let _ = m_win#vbox#pack ~expand:true s_win in
  (* Label with user text, packed after the view *)
  let _ = GMisc.label
    ~text:(pref ^ "\n" ^ text) ~xalign:0.01
    ~packing:(m_win#vbox#pack (* ~expand:false *)) ()
  in
  (* Create entry, and link key_press events *)
  let entry = GEdit.entry  ~text:"" ~packing:(m_win#vbox#pack ~padding:3) () in
  let _ = entry#event#connect#key_press ~callback:(
    begin fun ev ->
      if GdkEvent.Key.keyval ev = GdkKeysyms._Return then
        do_ok m_win entry pref text ();
      if GdkEvent.Key.keyval ev = GdkKeysyms._Escape then
        m_win#destroy ();
      false
    end;) in
  (* Put the cursor on entry *)
  entry#misc#grab_focus ();
  (* Create ok and cancel button, with associated callbacks. *)
  (* Pack them in the action area of the main dialog window *)
  let ok_b = GButton.button ~stock:`OK ~packing:(m_win#action_area#pack ~padding:3) () in
  let c_b = GButton.button ~stock:`CANCEL ~packing:(m_win#action_area#pack ~padding:3) () in
  let _ = ok_b#connect#clicked ~callback:(do_ok m_win entry pref text) in
  let _ = c_b#connect#clicked ~callback:m_win#destroy in
  m_win#show ();
  ok_b#grab_default ();
  GMain.Main.main()

let get_recipe pref text =
  get_recipe_aux pref text;
  match !ans with
  | None -> raise WrongChoice
  | Some s -> s

(* [get_new_vars state public'] returns a pair:
   - list of elements of [public'] added at the head of [state.public]
   with an additional term used to designate them in recipes.
   - list of these additional terms added at the head of [state.pub_vars],
   so that this list is the new value of [state.pub_vars], corresponding
   to [public'].
   The fresh variables are generated in increasing order from the
   the queue of [public'] to its head, so that they appear in increasing
   order when the terms are displayed. *)
    
let get_new_vars state public' =
  (* [get_new_pub [] public public'] returns the elements
     of [public'] that have been added at the head of [public],
     in reverse order. *)
  let rec get_new_pub new_pub public public' =
    if public == public' then
      new_pub
    else
      match public' with
	a::l -> get_new_pub (a::new_pub) public l
      | _ -> assert false
  in
  let new_pub = get_new_pub [] state.public public' in
  (* [add_vars [] state.pub_vars new_pub] returns a pair
     - elements of [new_pub] with an additional term used to designate
     them in recipes, in reverse order.
     - those additional terms added to [state.pub_vars]. *)
  let rec add_vars new_pub_v new_v = function
      (p',mess)::l ->
	let q =
	  (* [q] is the term that user can use to designate 
	     the message in recipes.
	     It is a fresh variable if the recipe is not 
	     a variable or a constant. *)
          match p' with
            Var _ | FunApp(_, []) ->
	      p'
          | FunApp(f, _) ->
              Var (new_var "~M" (snd f.f_type))
	in
        add_vars ((q, p', mess)::new_pub_v) (q::new_v) l
    | [] -> (new_pub_v, new_v)
  in
  add_vars [] state.pub_vars new_pub


(* [expand_recipe pub_vars public recipe] expand the [recipe] according to variables linked to equations in public, *)
(* and returns the obtained term *)
let expand_recipe pub_vars public recipe  =
  Terms.auto_cleanup (fun () ->
    List.iter2 (fun v (_,t') ->
      match v with
	Var x -> link x (TLink t')
      | _ -> ()) pub_vars public;
    copy_term3 recipe)
