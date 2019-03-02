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
(* Untyped front-end *)

(* Terms *)

type ident = Ptree.ident

type term = PIdent of ident
	  | PFail
          | PFunApp of ident * term_e list
	  | PTuple of term_e list

and term_e = term * Parsing_helper.extent

(* Equational theory *)

type equation = term_e * term_e

(* Functions defined by reduction rules *)

type fundef =  (term_e * term_e) list

(* Nounif *)

type gformat =
    PFGIdent of ident
  | PFGFunApp of ident * gformat_e list
  | PFGTuple of gformat_e list
  | PFGName of ident * (ident * gformat_e) list
  | PFGAny of ident

and gformat_e = gformat * Parsing_helper.extent

type gfact_format =
    ident * gformat_e list * int

(* Queries *)

type gterm = 
    PGIdent of ident
  | PGFunApp of ident * gterm_e list
  | PGTuple of gterm_e list
  | PGName of ident * (ident * gterm_e) list

and gterm_e = gterm * Parsing_helper.extent

type gfact = 
    PGSimpleFact of ident * gterm_e list
  | PGNeq of gterm_e * gterm_e
  | PGEqual of gterm_e * gterm_e

type gfact_e = gfact * Parsing_helper.extent

type event = gfact_e * int

type realquery = PBefore of event * hypelem 

and hypelem =
    PQEvent of event
  | PNestedQuery of realquery
  | POr of hypelem * hypelem
  | PAnd of hypelem * hypelem
  | PFalse

type query = 
    PBinding of ident * gterm_e 
  | PPutBegin of ident * ident list
	(* First ident must be "ev" or "evinj" *)
  | PRealQuery of realquery

(* Clauses *)

type fact = PSimpleFact of ident * term_e list
  | PSNeq of term_e * term_e
  | PSEqual of term_e * term_e

type fact_e = fact * Parsing_helper.extent

type clause = 
    PClause of fact_e list * fact_e 
  | PEquiv of fact_e list * fact_e * bool

(* Processes *)

type pattern = 
    PPatVar of ident
  | PPatTuple of pattern list
  | PPatFunApp of ident * pattern list
  | PPatEqual of term_e

type process = 
    PNil
  | PPar of process * process
  | PRepl of process
  | PRestr of ident * process 
  | PLetDef of ident
  | PTest of fact_e * process * process
  | PInput of term_e * pattern * process
  | POutput of term_e * term_e * process
  | PLet of pattern * term_e * process * process
  | PLetFilter of ident list * fact_e * process * process
  | PEvent of ident * term_e list * process
  | PPhase of int * process
  | PBarrier of int * ident option * process


(* Declarations *)

type decl = 
    FunDecl of ident * int * bool
  | DataFunDecl of ident * int
  | Reduc of fundef * bool
  | ReducFail of (term_e * term_e * ident list) list * bool
  | Equation of equation list
  | PredDecl of ident * int * ident list
  | Param of ident * Ptree.pval
  | PDef of ident * process
  | Query of query list
  | Noninterf of (ident * term_e list option) list
  | Weaksecret of ident
  | NoUnif of gfact_format * int * (ident * gformat_e) list
  | Not of (gfact_e * int) * (ident * gterm_e) list
  | Elimtrue of fact_e * ident list
  | Free of ident list * bool
  | Clauses of (clause * ident list) list

