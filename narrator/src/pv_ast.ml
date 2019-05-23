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

type enriched_term =
  | Name of string
  | Var of string
  | Tuple of enriched_term list
  | App of string * enriched_term list
  | UnaryOp of unary_op * enriched_term
  | BinaryOp of binary_op * enriched_term * enriched_term
  | New of {new_name : name_ty; next : enriched_term}
  | Conditional of
      { cond : enriched_term
      ; true_branch : enriched_term
      ; false_branch : enriched_term }
  | Eval of
      { let_bind_pat : pattern
      ; let_bind_term : enriched_term
      ; true_branch : enriched_term
      ; false_branch : enriched_term }
  | Event of {name : string; terms : enriched_term list}

and process =
  | Proc_null
  | Proc_parallel of process * process
  | Proc_replicate of process
  | Proc_new of {new_name : name_ty; next : process}
  | Proc_in of {channel : enriched_term; message : name_ty; next : process}
  | Proc_out of {channel : enriched_term; message : name_ty; next : process}
  | Proc_conditional of
      { cond : enriched_term
      ; true_branch : process
      ; false_branch : process }
  | Proc_eval of
      { let_bind_name : string
      ; let_bind_term : enriched_term
      ; true_branch : process
      ; false_branch : process }
  | Proc_macro of string * enriched_term list

and pattern =
  | Pat_typed_var of string * string
  | Pat_var of string
  | Pat_tuple of pattern list
  | Pat_eq of enriched_term

and decl =
  | Decl_proc of process
