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
(* Types module declares types of the abstract syntax
   tree and of sets of messages.
   There are recursive dependencies between these types,
   that is why they are included in the same module
*)

open Stringmap

type occurrence = int

(* Types *)

type typet = { tname : string }

(* Information for predicates. The integer argument corresponds
   to the phase of the predicate *)
type info = 
    Attacker of int * typet
  | Mess of int * typet
  | InputP of int 
  | OutputP of int
  | AttackerBin of int * typet
  | MessBin of int * typet
  | InputPBin of int
  | OutputPBin of int
  | AttackerGuess of typet
  | Compromise of typet
  | Equal of typet
  | Table of int
  | TableBin of int
  | TestUnifP of typet
  | PolymPred of string * int(*value of p_prop*) * typet list
  | Combined of predicate list
	
and predicate = { p_name: string;
                  p_type: typet list;
		  p_prop: int;
		  p_info: info list }

type when_include = 
    Always
  | IfQueryNeedsIt

type eq_info =
    EqNoInfo
  | EqConvergent
  | EqLinear
  | EqNoCheck

type binder = { v_orig_name : string;
                sname : string;
                vname : int;
                unfailing : bool;
		btype : typet;
		mutable link : linktype }
		
(* Processes: patterns *)

and pattern = 
    PatVar of binder
  | PatTuple of funsymb * pattern list
  | PatEqual of term

(* Processes themselves *)
  
and linktype = 
    NoLink
  | VLink of binder
  | TLink of term
  | TLink2 of term (* used only in reduction.ml *)
  | FLink of format (* used only in syntax.ml *)
  | PGLink of (unit -> term) (* used only in pisyntax.ml and pitsyntax.ml *)

(* Meaning of arguments of names *)

and arg_meaning =
    MUnknown
  | MSid of int (* The argument represents a session identifier *)
  | MCompSid
  | MAttSid
  | MVar of binder * string option
	(* The argument represents a variable.
	   The string option is [Some x] when the argument can be 
	   designated by the string [x] in "new a[x = ....]" *)

and name_info = { mutable prev_inputs : term option;
		  mutable prev_inputs_meaning : arg_meaning list }

and funcats = 
    Red of rewrite_rules
  | Eq of (term list * term) list
  | Tuple 
  | Name of name_info
  | SpecVar of binder
  | Syntactic of funsymb	
  | General_var
  | General_mayfail_var
  | Choice
  | Failure

and rewrite_rule = term list * term * (term * term) list

and rewrite_rules = rewrite_rule list

and funsymb = { f_orig_name : string;
		f_name : string;
		mutable f_type : typet list * typet; (* type of the arguments, type of the result *)
		mutable f_cat : funcats;
		f_initial_cat : funcats; (* Used to memorize f_cat before closing using the
                                            equational theory. The initial f_cat is used in reduction.ml,
					    and also in check_several_types *)
		f_private : bool; (* true when the function cannot be applied by the adversary *)
		f_options : int
              }

and term = 
    Var of binder
  | FunApp of funsymb * term list

(* Format, to represent facts with jokers *)

and format = 
    FVar of binder
  | FFunApp of funsymb * format list
  | FAny of binder

type fact_format = predicate * format list

type fact = 
    Pred of predicate * term list
  | Out of term * (binder * term) list

(* Environment elements; environments are needed for terms in queries
   that cannot be expanded before process translation, see link PGTLink
   below *)

type envElement = 
    EFun of funsymb
  | EVar of binder
  | EName of funsymb
  | EPred of predicate
  | EEvent of funsymb
  | EType of typet
  | ETable of funsymb
  | ELetFun of (term list -> (term -> process) -> process) * (typet list) * typet
  | EProcess of binder list * process
	
(* Each restriction "new" is annotated with
   - optionally, the identifiers given between brackets after the "new",
   which serve to determine the arguments in the internal representation
   of the name
   - the current environment at the restriction, which serves to determine
   which variables to use in queries of the form "new a[x = ...]" 

Events may also be annotated with identifiers between brackets.
They serve to determine the variables to include in the environment
used for proving injective correspondences.
*)

and new_args = binder list option * envElement StringMap.t 

(* Processes *)

and process = 
    Nil
  | Par of process * process
  | Repl of process * occurrence
  | Restr of funsymb * new_args * process * occurrence
  | Test of term * process * process * occurrence
  | Input of term * pattern * process * occurrence
  | Output of term * term * process * occurrence
  | Let of pattern * term * process * process * occurrence
  | LetFilter of binder list * fact * process * process * occurrence
  | Event of term  * new_args * process * occurrence
  | Insert of term * process * occurrence
  | Get of pattern * term * process * process * occurrence
  | Phase of int * process * occurrence
  | Barrier of int * string option * process * occurrence
  | AnnBarrier of int * string * funsymb * funsymb * (binder * term) list * process * occurrence
  | NamedProcess of string * term list * process

(* The following constraints are simple constraints.
   A list of simple constraints is a constraint, and represents the OR
   of the simple constraints.
   A list of constraints represents the AND of the simple constraints.
   TRUE can be represented by the list of constraints [].
   FALSE can be represented by any list of constraints that contains [],
   but these representations of FALSE are not used in the program:
   a false constraint leads to the immediate removal of the rule.
*)

type constraints = 
  | Neq of term * term
	
(* Rule descriptions for History.get_rule_hist *)

type rulespec =
  | RElem of predicate list * predicate
  | RApplyFunc of funsymb * predicate
  | RApplyProj of funsymb * int * predicate  (* For projections corresponding to data constructors *)

(* History of construction of rules *)

type onestatus =
    No | NonInj | Inj

type hypspec =
    ReplTag of occurrence * int(*Number of elements of name_params after it*)
  | InputTag of occurrence
  | BeginEvent of occurrence
  | BeginFact
  | LetFilterTag of occurrence
  | LetFilterFact
  | OutputTag of occurrence
  | TestTag of occurrence
  | LetTag of occurrence
  | TestUnifTag of occurrence
  | TestUnifTag2 of occurrence
  | InputPTag of occurrence
  | OutputPTag of occurrence
  | InsertTag of occurrence
  | GetTag of occurrence
  | GetTagElse of occurrence

type label =
    ProcessRule of hypspec list * term list 
  | Apply of funsymb * predicate
  | TestApply of funsymb * predicate
  | TestEq of predicate
  | LblEquiv
  | LblClause
  | LblEq
  | Rl of predicate * predicate
  | Rs of predicate * predicate
  | Ri of predicate * predicate
  | Ro of predicate * predicate
  | Rfail of predicate
  | TestComm of predicate * predicate
  | WeakSecr
  | Rn of predicate
  | Init
  | PhaseChange
  | TblPhaseChange
  | LblComp
  | LblNone
  | Elem of predicate list * predicate
  | TestUnif
  | TestDeterministic of funsymb
  | TestTotal of funsymb
  | Goal 
	
(* Rules *)

type history = 
    Rule of int * label * fact list * fact * constraints list list
  | Removed of int * int * history
  | Any of int * history
  | Empty of fact
  | HEquation of int * fact * fact * history
  | Resolution of history * int * history
  | TestUnifTrue of int * history

type reduction = fact list * fact * history * constraints list list

(* Equational theory *)

type equation = term * term

(* Proof history *)

type fact_tree_desc =
    FHAny
  | FEmpty
  | FRemovedWithProof of fact_tree
  | FRule of int * label * constraints list list * fact_tree list
  | FEquation of fact_tree

and fact_tree = 
    { mutable desc: fact_tree_desc;
      mutable thefact: fact;
    }

(* type of input to the Horn clause resolution solver *)

type t_solver_kind =
    Solve_Standard
  | Solve_Equivalence
  | Solve_WeakSecret of (typet * history) list * int
        (* Weaksecr.attrulenum, max_used_phase *)
  | Solve_Noninterf of (funsymb * term list option) list
	
type t_horn_state =
    { h_clauses : reduction list;
      h_equations : ((term * term) list * eq_info) list;
      h_close_with_equations : bool;
      h_not : fact list;
      h_elimtrue : (int * fact) list;
      h_equiv : (fact list * fact * int) list;
      h_nounif : (fact_format * int) list;
      h_clauses_to_initialize_selfun : reduction list;
      h_solver_kind : t_solver_kind }
