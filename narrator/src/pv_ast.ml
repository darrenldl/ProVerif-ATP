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

type pterm =
  | PT_name of string
  | PT_tuple of pterm list
  | PT_app of string * pterm list
  | PT_unaryOp of unary_op * pterm
  | PT_binaryOp of binary_op * pterm * pterm
  | PT_new of {name : name_ty; next : pterm}
  | PT_conditional of
      { cond : pterm
      ; true_branch : pterm
      ; false_branch : pterm option }
  | PT_eval of
      { let_bind_pat : pattern
      ; let_bind_term : pterm
      ; true_branch : pterm
      ; false_branch : pterm option }
  | PT_insert of {name : string; terms : pterm list; next : pterm}
  | PT_get of
      { name : string
      ; pats : pattern list
      ; true_branch : pterm
      ; false_branch : pterm option }
  | PT_event of {name : string; terms : pterm list}

and process =
  | Proc_null
  | Proc_parallel of process * process
  | Proc_replicate of process
  | Proc_new of {name : name_ty; next : process}
  | Proc_in of {channel : pterm; message : pattern; next : process}
  | Proc_out of {channel : pterm; message : pterm; next : process}
  | Proc_conditional of
      { cond : pterm
      ; true_branch : process
      ; false_branch : process }
  | Proc_eval of
      { let_bind_pat : pattern
      ; let_bind_term : pterm
      ; true_branch : process
      ; false_branch : process }
  | Proc_macro of string * pterm list

and pattern =
  | Pat_typed_var of name_ty
  | Pat_var of string
  | Pat_tuple of pattern list
  | Pat_eq of term

and decl = Decl_proc of process
