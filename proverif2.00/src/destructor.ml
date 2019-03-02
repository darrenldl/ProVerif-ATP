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

exception Not_deterministic

let compare_two_rewrite_rules f_symb (lhs1,rhs1) (lhs2,rhs2) =
  Terms.auto_cleanup (fun _ ->
    try
      (* We do not need to perform unification modulo the
	 equational theory because we work on rewrite rules
	 after closing under equations *)
      List.iter2 Terms.unify lhs1 lhs2;
      (* TermsEq.check_constraint_list does the copy of the constraints *)
      ignore(TermsEq.check_constraint_list [[Neq(rhs1,rhs2)]]);
      Display.Text.print_string "Error: The destructor ";
      Display.Text.display_function_name f_symb;
      Display.Text.print_string " is not deterministic.";
      Display.Text.newline ();
      Display.Text.print_string "Conflict between the rewrite rules:";
      Display.Text.newline ();
      Display.Text.display_red f_symb [(lhs1,rhs1,[]);(lhs2,rhs2,[])];
      raise Not_deterministic
    with Terms.Unify -> ()
  )


let check_deterministic f_symb_list =
  let rec check_all_rewrite_rule f_symb = function
    | [] -> ()
    | (lhs1,rhs1,[])::q ->
        List.iter (function
          | (lhs2,rhs2,[]) -> compare_two_rewrite_rules f_symb (lhs1,rhs1) (lhs2,rhs2)
          | _ -> ()
        ) q;
        check_all_rewrite_rule f_symb q
    | _::q -> check_all_rewrite_rule f_symb q
  in

  let check_one f_symb =
    try
      match f_symb.f_cat with
        | Red(redlist) ->
	    check_all_rewrite_rule f_symb redlist;
            true
        | _ -> internal_error "[Destructor.is_deterministic] This should be a destructor symbol"
    with
      Not_deterministic -> false
  in

  let all_deter = ref true in
  List.iter (fun f_symb ->
    if not (check_one f_symb) then all_deter := false
  ) f_symb_list;

  if not (!all_deter) then
    begin
      if (!Param.html_output) then
        Display.LangHtml.close ();
      Parsing_helper.user_error "The destructors should be deterministic.";
    end
