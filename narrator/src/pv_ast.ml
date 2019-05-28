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

and pterm =
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
      ; next : (pterm * pterm option) option }
  | PT_event of {name : string; terms : pterm list; next : pterm option}

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

let unary_op_to_string = function Not -> "~"

let binary_op_to_string = function
  | Eq -> "="
  | Neq -> "<>"
  | And -> "&&"
  | Or -> "||"

let rec term_to_string t =
  match t with
  | T_name s -> s
  | T_tuple ts ->
    Printf.sprintf "(%s)" (String.concat ", " (List.map term_to_string ts))
  | T_app (name, args) ->
    Printf.sprintf "%s(%s)" name
      (String.concat ", " (List.map term_to_string args))
  | T_unaryOp (op, t) ->
    Printf.sprintf "%s%s" (unary_op_to_string op)
      (match t with
       | T_name _
       | T_app _
       | T_unaryOp _
         -> term_to_string t
       | _ ->
         Printf.sprintf "(%s)" (term_to_string t))
  | T_binaryOp (op, l, r) ->
    Printf.sprintf "%s %s %s"
      ( match l with
        | T_name _ | T_app _ | T_unaryOp _ ->
          term_to_string l
        | _ ->
          Printf.sprintf "(%s)" (term_to_string l) )
      (binary_op_to_string op)
      ( match r with
        | T_name _ | T_app _ | T_unaryOp _ ->
          term_to_string l
        | _ ->
          Printf.sprintf "(%s)" (term_to_string r) )

let rec pattern_to_string p =
  match p with
  | Pat_typed_var { name; ty } ->
    Printf.sprintf "%s : %s" name ty
  | Pat_var s -> s
  | Pat_tuple ps ->
    Printf.sprintf "(%s)"
      (String.concat ", " (List.map pattern_to_string ps))
  | Pat_eq t ->
    Printf.sprintf "=%s" (term_to_string t)

let rec pterm_to_string t =
  match t with
  | PT_name s -> s
  | PT_tuple ts ->
    Printf.sprintf "(%s)" (String.concat ", " (List.map pterm_to_string ts))
  | PT_app (name, args) ->
    Printf.sprintf "%s(%s)" name
      (String.concat ", " (List.map pterm_to_string args))
  | PT_unaryOp (op, t) ->
    Printf.sprintf "%s%s" (unary_op_to_string op)
      (match t with
       | PT_name _
       | PT_app _
       | PT_unaryOp _
         -> pterm_to_string t
       | _ ->
         Printf.sprintf "(%s)" (pterm_to_string t))
  | PT_binaryOp (op, l, r) ->
    Printf.sprintf "%s %s %s"
      ( match l with
        | PT_name _ | PT_app _ | PT_unaryOp _ ->
          pterm_to_string l
        | _ ->
          Printf.sprintf "(%s)" (pterm_to_string l) )
      (binary_op_to_string op)
      ( match r with
        | PT_name _ | PT_app _ | PT_unaryOp _ ->
          pterm_to_string l
        | _ ->
          Printf.sprintf "(%s)" (pterm_to_string r) )
  | PT_new { name; next } ->
    Printf.sprintf "new %s : %s;\n%s"
      name.name
      name.ty
      (pterm_to_string next)
  | PT_conditional { cond; true_branch; false_branch } -> (
      match false_branch with
      | None ->
        Printf.sprintf "if %s then\n%s" (pterm_to_string cond)
          (pterm_to_string true_branch)
      | Some false_branch ->
        Printf.sprintf "if %s then\n%s\nelse\n%s"
          (pterm_to_string cond)
          (pterm_to_string true_branch)
          (pterm_to_string false_branch)
    )
  | PT_eval { let_bind_pat; let_bind_term; true_branch; false_branch } -> (
      match false_branch with
      | None ->
        Printf.sprintf "let %s = %s in\n%s" (pattern_to_string let_bind_pat)
          (pterm_to_string let_bind_term)
          (pterm_to_string true_branch)
      | Some false_branch ->
        Printf.sprintf "let %s = %s in\n%s\nelse\n%s" (pattern_to_string let_bind_pat)
          (pterm_to_string let_bind_term)
          (pterm_to_string true_branch)
          (pterm_to_string false_branch)
    )
  | PT_insert { name; terms; next } ->
    Printf.sprintf "insert(%s, %s);\n%s"
      name
      (String.concat ", " (List.map pterm_to_string terms))
      (pterm_to_string next)
  | PT_get { name; pats; next } -> (
      match next with
      | None ->
        Printf.sprintf "get(%s, %s)"
          name
          (String.concat ", " (List.map pattern_to_string pats))
      | Some (true_branch, false_branch) -> (
          match false_branch with
          | None ->
            Printf.sprintf "get(%s, %s) in\n%s"
              name
              (String.concat ", " (List.map pattern_to_string pats))
              (pterm_to_string true_branch)
          | Some false_branch ->
            Printf.sprintf "get(%s, %s) in\n%s\nelse\n%s"
              name
              (String.concat ", " (List.map pattern_to_string pats))
              (pterm_to_string true_branch)
              (pterm_to_string false_branch)
        )
    )
  | PT_event { name; terms; next } -> (
      let term_str =
        match terms with
        | [] -> ""
        | l ->
          Printf.sprintf "(%s)"
            (String.concat ", " (List.map ptern_))
      in
      match next with
      | None ->
        Printf.sprintf "evnet%s(%s)"
          name
          (String.concat ", " (List.map pterm_to_string))
    )

