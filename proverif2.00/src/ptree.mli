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
(* Terms *)

type ident = string * Parsing_helper.extent

type term = 
    PIdent of ident
  | PFunApp of ident * term list
  | PTuple of term list
  | PName of ident * term list

type format = 
    PFIdent of ident
  | PFFunApp of ident * format list
  | PFTuple of format list
  | PFName of ident * format list
  | PFAny of ident

(* Clauses *)

type fact = 
    PSimpleFact of ident * term list
  | PSNeq of term * term

type fact_e = fact * Parsing_helper.extent

type format_fact = ident * format list

type clause = 
    Clause of fact_e list * fact_e 
  | Equiv of fact_e list * fact_e * bool

type pval = 
    S of ident
  | I of int

(* Declarations - untyped front-end *)

type decl = 
    FunDecl of ident * int
  | DataFunDecl of ident * int
  | Equation of (term * term) list
  | Query of fact_e
  | NoUnif of format_fact * int
  | Not of fact_e
  | Elimtrue of fact_e
  | PredDecl of ident * int * ident list
  | Param of ident * pval
  | Reduc of clause list

(* Declarations - typed front-end *)

type envdecl = (ident(*variable*) * ident(*type*)) list

type tdecl = 
    TTypeDecl of ident (* type declaration *)
  | TNameDecl of ident * ident(*type*)
  | TFunDecl of ident * ident list(*argument types*) * ident(*result type*) * ident list(*options*)
  | TConstDecl of ident * ident(*type*) * ident list(*options*)
  | TEquation of (envdecl * term * term) list * ident list(*options*)
  | TQuery of envdecl * fact_e
  | TNoUnif of envdecl * format_fact * int
  | TNot of envdecl * fact_e
  | TElimtrue of envdecl * fact_e
  | TPredDecl of ident * ident list(*argument types*) * ident list(*options*)
  | TSet of ident * pval
  | TReduc of (envdecl * clause) list


