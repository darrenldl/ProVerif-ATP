type visibility =
  | Public
  | Private

type unary_op = Not

type binary_op =
  | Eq
  | Neq
  | And
  | Or

type ty = string

type name_ty =
  { name : string
  ; ty : string }

type term =
  | T_name of string
  | T_tuple of term list
  | T_app of string * term list
  | T_unaryOp of unary_op * term
  | T_binaryOp of binary_op * term * term

type enriched_term =
  | ET_name of string
  | ET_tuple of enriched_term list
  | ET_app of string * enriched_term list
  | ET_unaryOp of unary_op * enriched_term
  | ET_binaryOp of binary_op * enriched_term * enriched_term
  | ET_new of {name : name_ty; next : enriched_term}
  | ET_conditional of
      { cond : enriched_term
      ; true_branch : enriched_term
      ; false_branch : enriched_term option }
  | ET_eval of
      { let_bind_pat : pattern
      ; let_bind_term : enriched_term
      ; true_branch : enriched_term
      ; false_branch : enriched_term option }
  | ET_event of {name : string; terms : enriched_term list}

and process =
  | Proc_null
  | Proc_parallel of process * process
  | Proc_replicate of process
  | Proc_new of {name : name_ty; next : process}
  | Proc_in of {channel : term; message : pattern; next : process}
  | Proc_out of {channel : term; message : term; next : process}
  | Proc_conditional of
      { cond : term
      ; true_branch : process
      ; false_branch : process }
  | Proc_eval of
      { let_bind_name : string
      ; let_bind_term : enriched_term
      ; true_branch : process
      ; false_branch : process }
  | Proc_macro of string * term list

and pattern =
  | Pat_typed_var of name_ty
  | Pat_var of string
  | Pat_tuple of pattern list
  | Pat_eq of term

and decl =
  | Decl_proc of process
