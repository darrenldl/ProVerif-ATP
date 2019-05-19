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
  | Proc_Null
  | Proc_Parallel of process * process
  | Proc_Replicate of process
  | Proc_New of {new_name : name_ty; next : process}
  | Proc_In of {channel : enriched_term; message : name_ty; next : process}
  | Proc_Out of {channel : enriched_term; message : name_ty; next : process}
  | Proc_Conditional of
      { cond : enriched_term
      ; true_branch : process
      ; false_branch : process }
  | Proc_Eval of
      { let_bind_name : string
      ; let_bind_term : enriched_term
      ; true_branch : process
      ; false_branch : process }
  | Proc_Macro of string * enriched_term list

and pattern =
  | Pat_Typed_var of string * string
  | Pat_Var of string
  | Pat_Tuple of pattern list
  | Pat_Eq of enriched_term
