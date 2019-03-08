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

let preamble filename =
   output_string filename "begin_problem(Unknown).

list_of_descriptions.
name({*A protocol*}).
author({*Bruno Blanchet - Automatic translator*}).
status(unknown).
description({**}).
end_of_list.\n\n"


let output_ident filename s =
  (* SPASS identifiers can consist of digits, underscore, and alphabetic
     characters. We code other characters into this set by using their
     hexadecimal number. The hex. number is also used for the character 0
     to make sure the conversion is injective. *)
  String.iter (fun c ->
    if (c <= '0') || ((c > '9') && (c < 'A')) || ((c > 'Z') && (c < '_')) ||
                     ((c > '_') && (c < 'a')) || (c > 'z') then
      
      let code = int_of_char c in
      let hex_of_int n =
	if n >= 10 then
	  char_of_int (n + (int_of_char 'A') - 10)
	else
	  char_of_int (n + (int_of_char '0'))
      in
      output_char filename '0';
      output_char filename 'x';
      output_char filename (hex_of_int (code / 16));
      output_char filename (hex_of_int (code mod 16))
    else
      output_char filename c
    ) s

let output_fun_name filename f =
   match f.f_cat with
     Tuple -> 
       output_string filename "tuple_"; 
       if f.f_name = "" then
	 let arity = List.length (fst f.f_type) in
	 if (arity = 0) || (Param.get_ignore_types()) then
	   output_string filename (string_of_int arity)
	 else
	   output_string filename (Terms.tl_to_string "_" (fst f.f_type))

       else
	 output_ident filename f.f_name
   | Name _ -> 
       output_string filename "name_";
       output_ident filename f.f_name
   | Eq _ ->
       output_string filename "constr_";
       output_ident filename f.f_name
   | Failure ->
       Parsing_helper.user_error "The symbol fail cannot be handled by Spass. Stopping the translation"
   | _ ->
       Parsing_helper.internal_error "function symbols of these categories should not appear in rules"

let output_pred_name filename p =
   output_string filename "pred_";
   output_ident filename p.p_name

let output_var_name filename v =
  if v.unfailing then
    Parsing_helper.user_error "May-fail variables cannot be handled by Spass. Stopping the translation";
  output_string filename "var_";
  output_ident filename v.sname;
  output_string filename "_";
  output_string filename (string_of_int v.vname)

let func_set = Hashtbl.create 7
let pred_set = Hashtbl.create 1

let add_func f =
   if not (Hashtbl.mem func_set f) then
     Hashtbl.add func_set f ()

let add_pred p =
   if not (Hashtbl.mem pred_set p) then
     Hashtbl.add pred_set p ()

let output_func_set filename =
   output_string filename "list_of_symbols.\n";
   output_string filename "functions[";
   let start = ref true in
   Hashtbl.iter (fun f _ -> 
    if !start then 
      start := false
    else
      output_string filename ", ";
    output_string filename "(";
    output_fun_name filename f;
    output_string filename ",";
    output_string filename (string_of_int (List.length (fst f.f_type)));
    output_string filename ")") func_set;
   output_string filename "].\n";
   output_string filename "predicates[";
   let start = ref true in
   Hashtbl.iter (fun p _ -> 
    if !start then 
      start := false
    else
      output_string filename ", ";
    output_string filename "(";
    output_pred_name filename p;
    output_string filename ",";
    output_string filename (string_of_int (List.length p.p_type));
    output_string filename ")") pred_set;
   output_string filename "].\n";
   output_string filename "end_of_list.\n"

let rec fun_set_term = function
  Var _ -> ()
| FunApp(f,l) ->
    add_func f;
    List.iter fun_set_term l

let fun_set_fact = function
    Pred(p,l) ->
      add_pred p;
      List.iter fun_set_term l
  | _ ->
      (* TO DO implement translation of begin facts *)
      (* Parsing_helper.user_error "translation of begin facts into the Spass input format not yet\nimplemented" *)
    ()

let fun_set rules =
   List.iter (fun (hyp, concl, _, constra) ->
     List.iter fun_set_fact hyp;
     fun_set_fact concl;
     (* TO DO implement translation of inequalities *)
     match constra with
       [] -> ()
     | _ -> print_string "Warning: translation of inequalities into the Spass input format not yet\nimplemented\n"
     ) rules

let rec output_term filename = function
   Var v -> output_var_name filename v
 | FunApp(f,l) -> 
      output_fun_name filename f;
      if l != [] then
        output_term_list filename l

and output_term_list filename l =
      output_string filename "(";
      let start = ref true in
      List.iter (fun t ->
        if !start then
          start := false
        else
          output_string filename ",";
        output_term filename t) l;
      output_string filename ")"

let output_fact filename = function
    Pred(p,l) ->
      output_pred_name filename p;
      if l != [] then 
	output_term_list filename l
  | Out (t, l) ->
    (* Parsing_helper.internal_error "internal error output_fact" *)
    output_term filename t;
    (* List.iter (fun (_, t) -> output_term filename t) l *)
    ()

let output_fact_list filename l =
      let start = ref true in
      List.iter (fun f ->
        if !start then
          start := false
        else
          output_string filename ",";
        output_fact filename f) l

let output_body filename (hyp, concl, _, constra) =
   match hyp with
     [] -> output_fact filename concl
   | [a] -> output_string filename "implies(";
            output_fact filename a;
            output_string filename ", ";
            output_fact filename concl;
            output_string filename ")"
   | _ -> output_string filename "implies(and(";
            output_fact_list filename hyp;
            output_string filename "), ";
            output_fact filename concl;
            output_string filename ")"

let output_eq filename ((l, _) : (term * term) list * eq_info) =
  let rec term_to_str (t : term) =
    match t with
    | Var b          -> Printf.sprintf "var_%s" b.sname
    | FunApp (f, []) -> Printf.sprintf "name_%s" f.f_name
    | FunApp (f, l)  -> Printf.sprintf "constr_%s(%s)" f.f_name
			  (String.concat ", " (List.map term_to_str l))
  in
  let eq_to_str (t1, t2 : term * term) =
    Printf.sprintf "equal(%s, %s)" (term_to_str t1) (term_to_str t2)
  in
  let rec vars_in_term (t : term) =
    match t with
    | Var b         -> [b.sname]
    | FunApp (_, l) -> List.concat (List.map vars_in_term l)
  in
  List.iter (fun ((t1, t2) as eq) ->
      let eq_str = eq_to_str eq in
      let vars   = List.sort_uniq compare
	  (List.map
	     (fun x -> Printf.sprintf "var_%s" x)
	     (vars_in_term t1 @ vars_in_term t2)
	  )
      in
      output_string filename "formula(";
      begin
	match vars with
	| [] -> output_string filename eq_str
	| _  ->
	  output_string filename "forall([";
	  output_string filename (String.concat "," vars);
	  output_string filename "],";
	  output_string filename eq_str;
	  output_string filename ")";
      end;
      output_string filename ").\n";
    ) l

let output_rule filename ((hyp, concl,_,constra)  as rule) =
  let hyp = List.filter (function 
      Pred _ -> true
    | Out _ -> false) hyp
  in
  let has_no_var = ref true in
  let var_set = Hashtbl.create 1 in
  let add_var v =
     has_no_var := false;
     if not (Hashtbl.mem var_set v) then
       Hashtbl.add var_set v ()
  in
  let rec var_set_term = function
     Var v -> add_var v
   | FunApp(f,l) -> List.iter var_set_term l
  in
  let var_set_fact = function 
      Pred(p,l) ->  List.iter var_set_term l
    | _ -> Parsing_helper.internal_error "var_set_fact of Out"
  in
  List.iter var_set_fact hyp;
  var_set_fact concl;
  output_string filename "formula(";
  if !has_no_var then
    output_body filename rule
  else begin
    output_string filename "forall([";
    let start = ref true in
    Hashtbl.iter (fun v _ ->
      if !start then
        start:=false
      else
        output_string filename ",";
      output_var_name filename v) var_set;
    output_string filename "], ";
    output_body filename rule;
    output_string filename ")"
  end;
  output_string filename ").\n"

let output_eqs_and_rules filename eqs rules =
  output_string filename "list_of_formulae(axioms).\n\n";
  List.iter (output_eq   filename) eqs;
  List.iter (output_rule filename) rules;
  output_string filename "\nend_of_list.\n\n"

let output_query filename query =
  let has_no_var = ref true in
  let var_set = Hashtbl.create 1 in
  let add_var v =
     has_no_var := false;
     if not (Hashtbl.mem var_set v) then
       Hashtbl.add var_set v ()
  in
  let rec var_set_term = function
     Var v -> add_var v
   | FunApp(f,l) -> List.iter var_set_term l
  in
  let var_set_fact = function
      Pred(p,l) ->  List.iter var_set_term l
    | _ -> Parsing_helper.internal_error "query Out"
  in
  var_set_fact query;
  output_string filename "list_of_formulae(conjectures).\n\nformula(";
  if !has_no_var then
    output_fact filename query
  else begin
    output_string filename "exists([";
    let start = ref true in
    Hashtbl.iter (fun v _ ->
      if !start then
        start:=false
      else
        output_string filename ",";
      output_var_name filename v) var_set;
    output_string filename "], ";
    output_fact filename query;
    output_string filename ")"
  end;
  output_string filename ").\nend_of_list.\n\n"

let main filename eqs rules queries =
  (* Spass does not support the special symbol fail and the may-fail
     variables. We eliminate those completely when possible.

     We filter out rules that conclude p(...fail...). This is safe because
     we stop the translation when a rule has fail or a may-fail variable
     in its hypothesis, or when a query contains fail or a may-fail variable,
     so rules that conclude p(...fail...) are useless. *)
  let rules = List.filter (fun (_, concl, _, _) ->
      match concl with
        Pred(_, l) -> 
        List.for_all (function
              FunApp({f_cat = Failure}, []) -> false
            | _ -> true) l
      | _ -> true) rules
  in
  (* Each query must be output in a separate file, otherwise spass tries to 
     prove the disjunction of the queries *)
   let n = ref 0 in
   List.iter (fun query -> 
     incr n;
     let filename' = if !n = 1 then filename else (filename ^ "_" ^ (string_of_int (!n))) in
     let out_ch = open_out filename' in
     preamble out_ch;
     fun_set rules;
     output_func_set out_ch;
     output_eqs_and_rules out_ch eqs rules;
     output_query out_ch query;
     output_string out_ch "end_problem.\n";
     close_out out_ch) queries
