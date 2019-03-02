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
open Ptree

let lib_name = ref ""

let def_var_name = "v"

(* constants for predicate properties *)

let pred_ANY = 1
let pred_TUPLE = 2
let pred_BLOCKING = 4
let pred_ANY_STRICT = 8
let pred_ELEM = 16
let pred_ATTACKER = 32
let pred_ELIMVAR = 64
let pred_SIMPEQ = 128
let pred_TUPLE_SELECT = 256

(* constants for function properties *)

let fun_TYPECONVERTER = 2

(* various parameters that can be set by the user *)

let max_depth = ref (-1)
let max_hyp = ref (-1)

let ansi_color = ref false

let active_attacker = ref true

let key_compromise = ref 0

let typed_frontend = ref false
type ignore_t =
    NotSet
  | Ignore
  | NotIgnore
let ignore_types = ref NotSet

let get_ignore_types () =
  match !ignore_types with
    NotSet -> Parsing_helper.internal_error "ignore_types read before set"
  | Ignore -> true
  | NotIgnore -> false

let set_ignore_types b =
  begin
  match !ignore_types with
    NotSet -> ()
  | _ -> print_string "Warning: ignore_types set twice\n"
  end;
  ignore_types := if b then Ignore else NotIgnore

let default_set_ignore_types() =
  match !ignore_types with
    NotSet -> ignore_types := Ignore
  | _ -> ()

let html_output = ref false
let html_dir = ref ""
let current_query_number = ref 1
(* let current_process_number = ref 1 *) (* not use anywhere *)
let derivation_number = ref 0
let inside_query_number = ref 0
let process_number = ref 0

let expand_if_terms_to_terms = ref false
let expand_simplify_if_cst = ref true
let simplify_process = ref 1
let reject_choice_true_false = ref true
let reject_no_simplif = ref true

let verbose_rules = ref false
type explain_clauses = NoClauses | Clauses | ExplainedClauses
let verbose_explain_clauses = ref NoClauses
let verbose_redundant = ref false
let verbose_completed = ref false
let verbose_eq = ref true
let verbose_destr = ref false
let verbose_term = ref true
let abbreviate_clauses = ref true
let remove_subsumed_clauses_before_display = ref true

let reconstruct_derivation = ref true
let simplify_derivation = ref true
type simplification_level_t = AttackerOnly | AttackerSameTree | AllFacts
let simplify_derivation_level = ref AttackerSameTree
let unify_derivation = ref true

let display_derivation = ref true
let abbreviate_derivation = ref true
let explain_derivation = ref true
let reconstruct_trace = ref true
let trace_backtracking = ref true

(* For trace reconstruction, to disable display of initial state when
   backtracking is forbidden and the trace is displayed as it is build. *)
let display_init_state = ref true

(* let testeq = ref (None : (Types.predicate * Types.funsymb list) option) *)

type sel_type = NounifsetMaxsize | Nounifset | Term | TermMaxsize
let select_fun = ref TermMaxsize

let should_stop_term = ref true

type red_type = NoRed | SimpleRed | BestRed
let redundancy_test = ref SimpleRed

let move_new = ref false

let redundant_hyp_elim = ref true
let redundant_hyp_elim_begin_only = ref true

let check_pred_calls = ref true

let eq_in_names = ref false

let simpeq_remove = ref true
let simpeq_final = ref true

type eqtreatment = ConvLin | NonProved
let eqtreatment = ref ConvLin

let symb_order = ref None

type trace_display = NoDisplay | ShortDisplay | LongDisplay
let trace_display = ref ShortDisplay

(*for interactive mode *)
let allow_tilde = ref false
(* Reference to know if win_trace is open in interactive mode *)
let trace_win_open = ref false
let interactive_dot_command = ref "dot"
    
(* for trace graph *)
type trace_display_graphicx = TextDisplay | GraphDisplay
let trace_display_graphicx = ref TextDisplay


let command_line_graph = ref "dot -Tpdf %1.dot -o %1.pdf"
let command_line_graph_set = ref false

let graph_output = ref false

let tulafale = ref 0

(* For swapping at barriers *)

let interactive_swapping = ref false
let set_swapping = ref None

let boolean_param flag p ext v =
  match v with
    S ("no",_) | S ("false",_) -> flag := false
  | S ("yes",_) | S ("true",_) -> flag := true
  | _ -> Parsing_helper.input_error ("Unexpected value for parameter " ^ p ^ "=" ^
		       (match v with S (s,_) -> s | I n -> string_of_int n)) ext

let common_parameters p ext v =
  match (p,v) with
    "verboseRules", _ -> boolean_param verbose_rules p ext v
  | "verboseRedundant", _ -> boolean_param verbose_redundant p ext v
  | "verboseCompleted", _ -> boolean_param verbose_completed p ext v
  | "verboseEq", _ -> boolean_param verbose_eq p ext v
  | "verboseTerm", _ -> boolean_param verbose_term p ext v
  | "abbreviateClauses", _ -> boolean_param abbreviate_clauses p ext v
  | "maxDepth", S ("none",_) -> max_depth := -1
  | "maxDepth", I s -> max_depth := s
  | "maxHyp", I s -> max_hyp := s
  | "maxHyp", S ("none",_) -> max_hyp := -1
  | "selFun", S ("Nounifset",_) -> select_fun := Nounifset
  | "selFun", S ("NounifsetMaxsize",_) -> select_fun := NounifsetMaxsize
  | "selFun", S ("Term",_) -> select_fun := Term
  | "selFun", S ("TermMaxsize",_) -> select_fun := TermMaxsize
  | "stopTerm", _ -> boolean_param should_stop_term p ext v
  | "redundancyElim", S("no",_) -> redundancy_test := NoRed
  | "redundancyElim", S("simple",_) -> redundancy_test := SimpleRed
  | "redundancyElim", S("best",_) -> redundancy_test := BestRed
  | "redundantHypElim", S("beginOnly",_) ->
      redundant_hyp_elim := true;
      redundant_hyp_elim_begin_only := true
  | "redundantHypElim", S (("true"|"yes"),_) ->
      redundant_hyp_elim := true;
      redundant_hyp_elim_begin_only := false
  | "redundantHypElim", S (("false"|"no"),_) -> redundant_hyp_elim := false
  | "simpEq", S ("remove",_) -> simpeq_remove := true
  | "simpEq", S ("reduce",_) -> simpeq_remove := false
  | "simpEqFinal", _ ->  boolean_param simpeq_final p ext v
  | "eqTreatment", S ("convLin",_) -> eqtreatment := ConvLin
  | "eqTreatment", S ("nonProved",_) -> eqtreatment := NonProved (* Undocumented! *)
  | "symbOrder", S sext -> symb_order := Some sext
  | "reconstructDerivation", _ -> boolean_param reconstruct_derivation p ext v
  | "simplifyDerivation", _ -> boolean_param simplify_derivation p ext v
  | "displayDerivation", _ -> boolean_param display_derivation p ext v
  | "abbreviateDerivation", _ -> boolean_param abbreviate_derivation p ext v
  | _, _ -> Parsing_helper.input_error ("Bad parameter " ^ p ^ "=" ^
			 (match v with S (s,_) -> s | I n -> string_of_int n) ^ ".") ext

(* types *)

let any_type = { tname = "any" }
let bitstring_type = { tname = "bitstring" }
let channel_type = { tname = "channel" }
let sid_type = { tname = "sid" } (* session ids *)
let event_type = { tname = "event" }
let bool_type = { tname = "bool" }
let table_type = { tname = "table" }

let tmp_type = [{ tname = "temporary_type_should_be_removed" }]

let get_type ty =
  if get_ignore_types() then any_type else ty

(* predicates *)

let get_phase_suffix i =
  if i = 0 then "" else "_p" ^ (string_of_int i)

let get_type_suffix t =
  if t == any_type then "" else "_" ^ t.tname

let rec tl_to_string sep = function
    [] -> ""
  | [a] -> a.tname
  | (a::l) -> a.tname ^ sep ^ (tl_to_string sep l)

let build_pred = function
    Attacker(i,t) ->
      { p_name = "attacker" ^ (get_type_suffix t) ^ (get_phase_suffix i);
	p_type = [t];
	p_prop = pred_ANY + pred_TUPLE + pred_ATTACKER;
	p_info = [Attacker(i,t)] }
  | Mess(i,t) ->
      { p_name = "mess" ^ (get_type_suffix t) ^ (get_phase_suffix i);
	p_type = [channel_type; t];
	p_prop = 0;
	p_info = [Mess(i,t)] }
  | InputP(i) ->
      { p_name = "input" ^ (get_phase_suffix i);
	p_type = [channel_type];
	p_prop = 0;
	p_info = [InputP(i)] }
  | OutputP(i) ->
      { p_name = "output" ^ (get_phase_suffix i);
	p_type = [channel_type];
	p_prop = 0;
	p_info = [OutputP(i)] }
  | AttackerBin(i,t) ->
      { p_name = "attacker2" ^ (get_type_suffix t) ^ (get_phase_suffix i);
	p_type = [t;t];
	p_prop = pred_TUPLE + pred_TUPLE_SELECT + pred_ELIMVAR + pred_SIMPEQ + pred_ANY + pred_ATTACKER;
	p_info = [AttackerBin(i,t)] }
  | MessBin(i,t) ->
      { p_name = "mess2" ^ (get_type_suffix t) ^ (get_phase_suffix i);
	p_type = [channel_type; t; channel_type; t];
	p_prop = 0;
	p_info = [MessBin(i,t)] }
  | InputPBin(i) ->
      { p_name = "input2" ^ (get_phase_suffix i);
	p_type = [channel_type; channel_type];
	p_prop = 0;
	p_info = [InputPBin(i)] }
  | OutputPBin(i) ->
      { p_name = "output2" ^ (get_phase_suffix i);
	p_type = [channel_type; channel_type];
	p_prop = 0;
	p_info = [OutputPBin(i)] }
  | AttackerGuess(t) ->
      { p_name = "attacker_guess" ^ (get_type_suffix t);
	p_type = [t;t];
	p_prop = pred_TUPLE + pred_TUPLE_SELECT + pred_ELIMVAR + pred_SIMPEQ + pred_ANY + pred_ATTACKER;
	p_info = [AttackerGuess(t)] }
  | Compromise(t) ->
      { p_name = "comp" ^ (get_type_suffix t);
	p_type = [t];
	p_prop = pred_TUPLE + pred_ANY;
	p_info = [Compromise(t)] }
  | Equal(t) ->
      { p_name = "equal" ^ (get_type_suffix t);
	p_type = [t;t];
	p_prop = 0;
	p_info = [Equal(t)] }
  | Table(i) ->
      { p_name = "table" ^ (get_phase_suffix i);
	p_type = [table_type];
	p_prop = 0;
	p_info = [Table(i)] }
  | TableBin(i) ->
      { p_name = "table2" ^ (get_phase_suffix i);
	p_type = [table_type;table_type];
	p_prop = 0;
	p_info = [TableBin(i)] }
  | PolymPred(s,i,tl) ->
      { p_name = s ^ (if List.for_all (fun x -> x == any_type) tl then "" else
                      if List.for_all (fun x -> x == List.hd tl) tl then "_" ^ (List.hd tl).tname else
		      "_" ^ (tl_to_string "_" tl));
	p_type = tl;
	p_prop = i;
	p_info = [PolymPred(s,i,tl)] }
  | TestUnifP(t) ->
      { p_name = "testunif" ^ (get_type_suffix t);
	p_type = [t; t];
	p_prop = pred_BLOCKING;
	p_info = [TestUnifP(t)] }
  | Combined(pl) ->
      (* Combines predicates in [pl] into a single predicate *)
      { p_name = "combined_" ^ (String.concat "_" (List.map (fun p -> p.p_name) pl));
	p_type = List.concat (List.map (fun p -> p.p_type) pl);
	p_prop = 0;
	p_info = [Combined(pl)] }

let memo f =
  let table = Hashtbl.create 7 in
  fun x ->
    try
      Hashtbl.find table x
    with Not_found ->
    let r = f x in
    Hashtbl.add table x r;
    r

let memo_type f =
  (* Build the memoizing version of [f] before having the type argument *)
  let memo_f = memo f in
  fun ty -> memo_f (get_type ty)
      
let build_pred_memo = memo build_pred

let get_pred info =
  let info =
    if get_ignore_types() then
      match info with
	Attacker(i,t) -> Attacker(i,any_type)
      |	Mess(i,t) -> Mess(i,any_type)
      |	AttackerBin(i,t) -> AttackerBin(i,any_type)
      |	MessBin(i,t) -> MessBin(i,any_type)
      |	AttackerGuess(t) -> AttackerGuess(any_type)
      |	Compromise(t) -> Compromise(any_type)
      |	Equal(t) -> Equal(any_type)
      |	PolymPred(s,i,tl) -> PolymPred(s,i, List.map (fun _ -> any_type) tl)
      |	TestUnifP(t) -> TestUnifP(any_type)
      |	x -> x
    else
      info
  in
  build_pred_memo info

(* For authenticity *)
let end_pred = { p_name = "end"; p_type = [event_type]; p_prop = 0;
		 p_info = [] }
let end_pred_inj = { p_name = "end"; p_type = [sid_type; event_type] ; p_prop = 0;
		     p_info = [] }

(* For non-interference *)

let bad_pred = { p_name = "bad"; p_type = []; p_prop = pred_BLOCKING;
		 p_info = [] }

(* Predicate used as replacement for the conclusion in backward search *)

let dummy_pred = { p_name = "dummy"; p_type = []; p_prop = 0; p_info = [] }

(* For choice *)

let choice_fun =
  memo_type (fun t ->
      { f_orig_name = "choice";
        f_name = "choice";
        f_type = [t;t],t;
        f_cat = Choice;
        f_initial_cat = Choice;
        f_private = true;
        f_options = 0 })

let has_choice = ref false
let has_barrier = ref false
    
(* Values computed from the input file *)

let types_initial = [channel_type; bitstring_type; bool_type]
let dummy_pi_state =
  { pi_process_query = SingleProcess(Nil,[]);
    pi_global_env = Unset;
    pi_glob_table = Unset;
    pi_glob_table_var_name = Unset;
    pi_types = [];
    pi_funs = [];
    pi_freenames = [];
    pi_events = [];
    pi_equations = [];
    pi_max_used_phase = 0;
    pi_input_clauses = [];
    pi_elimtrue = [];
    pi_equivalence_clauses = [];
    pi_destructors_check_deterministic = [];
    pi_disequations = [];
    pi_event_status_table = Unset;
    pi_get_not = (fun _ -> []);
    pi_get_nounif = (fun _ -> []);
    pi_terms_to_add_in_name_params = Unset;
    pi_min_choice_phase = Unset;
    pi_need_vars_in_names = Function(fun _ -> []);
    pi_name_args_exact = true;
  }

let current_state = ref dummy_pi_state

let get_process_query pi_state =
  match pi_state.pi_process_query with
  | SingleProcessSingleQuery(p,q) -> p,q
  | _ -> Parsing_helper.internal_error "SingleProcessSingleQuery expected in get_process_query"
    
let is_noninterf pi_state =
  match pi_state.pi_process_query with
    SingleProcessSingleQuery(_, NonInterfQuery _) -> true
  | _ -> false

let is_equivalence_two_processes pi_state =
  match pi_state.pi_process_query with
    Equivalence _ -> true
  | _ -> false
	
let session1 = { f_orig_name = "session1";
                 f_name = "session1";
		 f_type = [], sid_type;
                 f_private = false;
		 f_options = 0;
		 f_cat = Eq [];
	         f_initial_cat = Eq [] }

let reset_param() =
  (* Do not reset:
     lib_name, tulafale, graph_output, trace_display_graphicx, html_dir, 
     command_line_graph_set, command_line_graph, ansi_color, html_output,
     interactive_dot_command
     which are set on the command-line.

     Do not reset: 
     verbose_explain_clauses, explain_derivation, abbreviate_clauses, typed_frontend
     which are set before parsing the file in a fairly complicated way
     (depends on -in, -test, -tulafale, -html and the extension of the input file).
     That is not perfect because the values of these parameters may remain
     those of a previous input file instead of the desired value.
     No problem for the interactive simulator, and currently we do not 
     load several files in proverif itself. 

     Do not reset:
     allow_tilde, trace_win_open
     Used by interactive simulator *)
  max_depth := (-1);
  max_hyp := (-1);
  active_attacker := true;
  key_compromise := 0;
  ignore_types := NotSet;
  current_query_number := 1;
  derivation_number := 0;
  inside_query_number := 0;
  process_number := 0;
  expand_if_terms_to_terms := false;
  expand_simplify_if_cst := true;
  simplify_process := 1;
  reject_choice_true_false := true;
  reject_no_simplif := true;
  verbose_rules := false;
  verbose_redundant := false;
  verbose_completed := false;
  verbose_eq := true;
  verbose_destr := false;
  verbose_term := true;
  remove_subsumed_clauses_before_display := true;
  reconstruct_derivation := true;
  simplify_derivation := true;
  simplify_derivation_level := AttackerSameTree;
  unify_derivation := true;
  display_derivation := true;
  abbreviate_derivation := true;
  reconstruct_trace := true;
  trace_backtracking := true;
  display_init_state := true;
  select_fun := TermMaxsize;
  should_stop_term := true;
  redundancy_test := SimpleRed;
  move_new := false;
  redundant_hyp_elim := true;
  redundant_hyp_elim_begin_only := true;
  check_pred_calls := true;
  eq_in_names := false;
  simpeq_remove := true;
  simpeq_final := true;
  eqtreatment := ConvLin;
  symb_order := None;
  trace_display := ShortDisplay;
  interactive_swapping := false;
  set_swapping := None;
  has_choice := false;
  has_barrier := false;
  current_state := dummy_pi_state;
  
  if (!tulafale) = 1 then
    begin
      reconstruct_trace := false;
      abbreviate_derivation := false;
      redundant_hyp_elim := true;
      redundant_hyp_elim_begin_only := true
    end;
