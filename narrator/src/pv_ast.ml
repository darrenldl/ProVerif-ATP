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

and pattern =
  | Pat_var of string
  | Pat_typed_var of name_ty
  | Pat_tuple of pattern list
  | Pat_app of string * pattern list
  | Pat_eq of term

and mayfailterm =
  | MFT_term of term
  | MFT_fail

and process =
  | Proc_null
  | Proc_macro of string * pterm list
  | Proc_parallel of process * process
  | Proc_replicate of process
  | Proc_new of {names : string list; ty : string; next : process}
  | Proc_conditional of
      { cond : pterm
      ; true_branch : process
      ; false_branch : process }
  | Proc_in of {channel : pterm; message : pattern; next : process}
  | Proc_out of {channel : pterm; message : pterm; next : process}
  | Proc_eval of
      { let_bind_pat : pattern
      ; let_bind_term : pterm
      ; true_branch : process
      ; false_branch : process }
  | Proc_insert of {name : string; terms : pterm list; next : process}
  | Proc_get of
      { name : string
      ; pats : pattern list
      ; next : (process * process option) option }
  | Proc_event of {name : string; terms : pterm list; next : process option}

and decl =
  | Decl_ty of string * string list
  | Decl_channel of string list
  | Decl_free of {names : string list; ty : string; options : string list}
  | Decl_const of {names : string list; ty : string; options : string list}
  | Decl_fun of {name : string; arg_tys : string list; ret_ty : string}
  | Decl_equation of
      { eqs : (name_ty list * term * term) list
      ; options : string list }
  | Decl_pred of {name : string; arg_tys : string list}
  | Decl_table of {name : string; tys : string list}
  | Decl_let_proc of {name : string; args : name_ty list; process : process}
  | Decl_event of {name : string; args : name_ty list}
  | Decl_query of query

and query = query_single list

and query_single = Q_term of gterm

and gterm =
  | GT_name of string
  | GT_app of string * gterm list
  | GT_binaryOp of binary_op * gterm * gterm
  | GT_event of gterm list

let unary_op_to_string = function Not -> "~"

let binary_op_to_string = function
  | Eq ->
    "="
  | Neq ->
    "<>"
  | And ->
    "&&"
  | Or ->
    "||"

let rec term_to_string t =
  match t with
  | T_name s ->
    s
  | T_tuple ts ->
    Printf.sprintf "(%s)" (String.concat ", " (List.map term_to_string ts))
  | T_app (name, args) ->
    Printf.sprintf "%s%s" name
      (Misc_utils.map_list_to_string_w_opt_paren term_to_string args)
  | T_unaryOp (op, t) ->
    Printf.sprintf "%s%s" (unary_op_to_string op)
      ( match t with
        | T_name _ | T_app _ | T_unaryOp _ ->
          term_to_string t
        | _ ->
          Printf.sprintf "(%s)" (term_to_string t) )
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
  | Pat_typed_var {name; ty} ->
    Printf.sprintf "%s : %s" name ty
  | Pat_var s ->
    s
  | Pat_tuple ps ->
    Misc_utils.map_list_to_string_w_opt_paren pattern_to_string ps
  | Pat_app (f, ps) ->
    Printf.sprintf "%s%s" f
      (Misc_utils.map_list_to_string_w_opt_paren pattern_to_string ps)
  | Pat_eq t ->
    Printf.sprintf "=%s" (term_to_string t)

let rec pterm_to_string t =
  match t with
  | PT_name s ->
    s
  | PT_tuple ts ->
    Misc_utils.map_list_to_string_w_opt_paren pterm_to_string ts
  | PT_app (name, args) ->
    Printf.sprintf "%s(%s)" name
      (Misc_utils.map_list_to_string_w_opt_paren pterm_to_string args)
  | PT_unaryOp (op, t) ->
    Printf.sprintf "%s%s" (unary_op_to_string op)
      ( match t with
        | PT_name _ | PT_app _ | PT_unaryOp _ ->
          pterm_to_string t
        | _ ->
          Printf.sprintf "(%s)" (pterm_to_string t) )
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
  | PT_new {name; next} ->
    Printf.sprintf "new %s : %s;\n%s" name.name name.ty
      (pterm_to_string next)
  | PT_conditional {cond; true_branch; false_branch} -> (
      match false_branch with
      | None ->
        Printf.sprintf "if %s then\n%s" (pterm_to_string cond)
          (pterm_to_string true_branch)
      | Some false_branch ->
        Printf.sprintf "if %s then\n%s\nelse\n%s" (pterm_to_string cond)
          (pterm_to_string true_branch)
          (pterm_to_string false_branch) )
  | PT_eval {let_bind_pat; let_bind_term; true_branch; false_branch} -> (
      match false_branch with
      | None ->
        Printf.sprintf "let %s = %s in\n%s"
          (pattern_to_string let_bind_pat)
          (pterm_to_string let_bind_term)
          (pterm_to_string true_branch)
      | Some false_branch ->
        Printf.sprintf "let %s = %s in\n%s\nelse\n%s"
          (pattern_to_string let_bind_pat)
          (pterm_to_string let_bind_term)
          (pterm_to_string true_branch)
          (pterm_to_string false_branch) )
  | PT_insert {name; terms; next} ->
    Printf.sprintf "insert(%s, %s);\n%s" name
      (Misc_utils.map_list_to_string_w_opt_paren pterm_to_string terms)
      (pterm_to_string next)
  | PT_get {name; pats; next} -> (
      match next with
      | None ->
        Printf.sprintf "get(%s, %s)" name
          (Misc_utils.map_list_to_string_w_opt_paren pattern_to_string pats)
      | Some (true_branch, false_branch) -> (
          match false_branch with
          | None ->
            Printf.sprintf "get(%s, %s) in\n%s" name
              (Misc_utils.map_list_to_string_w_opt_paren pattern_to_string pats)
              (pterm_to_string true_branch)
          | Some false_branch ->
            Printf.sprintf "get(%s, %s) in\n%s\nelse\n%s" name
              (Misc_utils.map_list_to_string_w_opt_paren pattern_to_string pats)
              (pterm_to_string true_branch)
              (pterm_to_string false_branch) ) )
  | PT_event {name; terms; next} -> (
      let term_str =
        Misc_utils.map_list_to_string_w_opt_paren pterm_to_string terms
      in
      match next with
      | None ->
        Printf.sprintf "event%s%s" name term_str
      | Some next ->
        Printf.sprintf "event%s%s;\n%s" name term_str (pterm_to_string next)
    )

let mayfailterm_to_string t =
  match t with MFT_term t -> term_to_string t | MFT_fail -> "fail"

module Print_context = struct
  type process_structure_type =
    | Let
    | IfElse
    | InOut
    | Zero
    | New
    | Get
    | Insert

  type decl_structure_type =
    | Const
    | Free
    | Table
    | FunDec
    | Equation
    | LetProc
    | Process
    | Query

  let indent_space_count = 2

  type t =
    { mutable proc_name : string option
    ; mutable prev_decl_struct_ty : decl_structure_type option
    ; mutable cur_decl_struct_ty : decl_structure_type option
    ; mutable prev_proc_struct_ty : process_structure_type option
    ; mutable cur_proc_struct_ty : process_structure_type option
    ; mutable out_count : int
    ; mutable indent : int
    ; mutable buffer : (int * string) list }

  let make () =
    { proc_name = None
    ; prev_decl_struct_ty = None
    ; cur_decl_struct_ty = None
    ; prev_proc_struct_ty = None
    ; cur_proc_struct_ty = None
    ; out_count = 0
    ; indent = 0
    ; buffer = [] }

  let reset ctx =
    ctx.proc_name <- None;
    ctx.prev_decl_struct_ty <- None;
    ctx.cur_decl_struct_ty <- None;
    ctx.prev_proc_struct_ty <- None;
    ctx.cur_proc_struct_ty <- None;
    ctx.out_count <- 1;
    ctx.indent <- 0;
    ctx.buffer <- []

  let set_decl_struct_ty ctx ty =
    ctx.prev_decl_struct_ty <- ctx.cur_decl_struct_ty;
    ctx.cur_decl_struct_ty <- Some ty

  let set_proc_struct_ty ctx ty =
    ctx.prev_proc_struct_ty <- ctx.cur_proc_struct_ty;
    ctx.cur_proc_struct_ty <- Some ty

  let set_proc_name ctx x =
    ctx.proc_name <- Some x;
    ctx.prev_proc_struct_ty <- None;
    ctx.cur_proc_struct_ty <- None;
    ctx.out_count <- 0

  let set_proc_name_none ctx =
    ctx.proc_name <- None;
    ctx.prev_proc_struct_ty <- None;
    ctx.cur_proc_struct_ty <- None;
    ctx.out_count <- 0

  let incre_indent ctx = ctx.indent <- ctx.indent + 1

  let decre_indent ctx = ctx.indent <- ctx.indent - 1

  let incre_out_count ctx = ctx.out_count <- ctx.out_count + 1

  let push ctx (s : string) = ctx.buffer <- (ctx.indent, s) :: ctx.buffer

  let insert_blank_line_if_diff_decl_struct_ty ctx =
    match (ctx.prev_decl_struct_ty, ctx.cur_decl_struct_ty) with
    | Some ty1, Some ty2 when ty1 <> ty2 ->
      push ctx ""
    | _ ->
      ()

  let insert_blank_line_anyway_decl_struct_ty ctx =
    match ctx.prev_decl_struct_ty with Some _ -> push ctx "" | None -> ()

  let insert_blank_line_if_diff_proc_struct_ty ctx =
    match (ctx.prev_proc_struct_ty, ctx.cur_proc_struct_ty) with
    | Some ty1, Some ty2 when ty1 <> ty2 ->
      push ctx ""
    | _ ->
      ()

  let insert_blank_line_anyway_proc_struct_ty ctx =
    match ctx.prev_proc_struct_ty with Some _ -> push ctx "" | None -> ()

  let finish ctx =
    String.concat "\n"
      (List.fold_left
         (fun acc (indent, s) ->
            let padding = String.make (indent * indent_space_count) ' ' in
            Printf.sprintf "%s%s" padding s :: acc )
         [] ctx.buffer)
end

let rec process_to_string_debug p =
  match p with
  | Proc_null -> "0"
  | Proc_macro (name, args) ->
    Printf.sprintf "%s%s" name
      (Misc_utils.map_list_to_string_w_opt_paren pterm_to_string args)
  | Proc_parallel (p1, p2) ->
    Printf.sprintf "%s | %s"
      (process_to_string_debug p1)
      (process_to_string_debug p2)
  | Proc_replicate p ->
    Printf.sprintf "! %s" (process_to_string_debug p)
  | Proc_new {names; ty; next} ->
    Printf.sprintf "new %s : %s;\n%s"
      (String.concat ", " names)
      ty
      (process_to_string_debug next)
  | Proc_conditional { cond; true_branch; false_branch } ->
    Printf.sprintf "if %s then\n%s\nelse\n%s"
      (pterm_to_string cond)
      (process_to_string_debug true_branch)
      (process_to_string_debug false_branch)
  | Proc_in { channel; message; next } ->
    Printf.sprintf "in(%s, %s);\n%s"
      (pterm_to_string channel)
      (pattern_to_string message)
      (process_to_string_debug next)
  | Proc_out { channel; message; next } ->
    Printf.sprintf "out(%s, %s);\n%s"
      (pterm_to_string channel)
      (pterm_to_string message)
      (process_to_string_debug next)
  | Proc_eval { let_bind_pat; let_bind_term; true_branch; false_branch } ->
    Printf.sprintf "let %s = %s in\n%s\nelse\n%s"
      (pattern_to_string let_bind_pat)
      (pterm_to_string let_bind_term)
      (process_to_string_debug true_branch)
      (process_to_string_debug false_branch)
  | Proc_insert { name; terms; next } ->
    Printf.sprintf "insert %s(%s);\n%s"
      name
      (Misc_utils.map_list_to_string pterm_to_string terms)
      (process_to_string_debug next)
  | Proc_get { name; pats; next } -> (
      match next with
      | None ->
        Printf.sprintf "get %s(%s)"
          name
          (Misc_utils.map_list_to_string pattern_to_string pats)
      | Some (true_branch, false_branch) ->
        match false_branch with
        | None ->
          Printf.sprintf "get %s(%s) in\n%s"
            name
            (Misc_utils.map_list_to_string pattern_to_string pats)
            (process_to_string_debug true_branch)
        | Some false_branch ->
          Printf.sprintf "get %s(%s) in\n%s\nelse\n%s"
            name
            (Misc_utils.map_list_to_string pattern_to_string pats)
            (process_to_string_debug true_branch)
            (process_to_string_debug false_branch)
    )
  | Proc_event { name; terms; next } -> (
      match next with
      | None ->
        Printf.sprintf "get %s(%s)"
          name
          (Misc_utils.map_list_to_string pterm_to_string terms)
      | Some next ->
        Printf.sprintf "event %s%s;\n%s"
          name
          (Misc_utils.map_list_to_string_w_opt_paren pterm_to_string terms)
          (process_to_string_debug next)
    )

let rec decl_to_string_debug d =
  match d with
  | Decl_ty (ty, options) -> (
      match options with
      | [] -> Printf.sprintf "type %s." ty
      | l ->
        Printf.sprintf "type %s %s." ty
          (Misc_utils.map_list_to_string_w_opt_brack Misc_utils.id l)
    )
  | Decl_channel l ->
  | Decl_free { names; ty; options } ->
  | Decl_const { names; ty; options } ->
  | Decl_fun { names; arg_tys; ret_ty } ->
  | Decl_equation { eqs; options } ->
  | Decl_pred { name; arg_tys } ->
  | Decl_table { name; tys } ->
  | Decl_let_proc { name; args } ->
  | Decl_event { name; args } ->
  | Decl_query qs ->
