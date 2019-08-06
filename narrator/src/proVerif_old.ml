module Expr_components = struct
  type visibility =
    | Public
    | Private

  type ident = string

  type ty = string
end

module Raw_expr = struct
  open Parser_components
  open MParser
  open Expr_components

  type unary_op = Not

  type binary_op =
    | Eq
    | Neq

  let unary_op_to_string = function Not -> "~"

  let binary_op_to_string = function Eq -> "=" | Neq -> "<>"

  type expr =
    | Variable of ident
    | Function of ident * expr list
    | UnaryOp of unary_op * expr
    | BinaryOp of binary_op * expr * expr
    | Tuple of expr list

  type ident_ty_or_pat =
    | Ident_ty of ident * ty
    | Pat of expr

  type ident_or_ident_ty_or_pat =
    | Ident of ident
    | Ident_ty of ident * ty
    | Pat of expr

  let rec expr_to_string f =
    match f with
    | Variable n ->
      n
    | Function (name, fs) ->
      Printf.sprintf "%s(%s)" name
        (String.concat ", " (List.map expr_to_string fs))
    | UnaryOp (op, f) ->
      Printf.sprintf "%s%s" (unary_op_to_string op)
        ( match f with
          | Variable _ | Function _ | UnaryOp _ ->
            expr_to_string f
          | _ ->
            Printf.sprintf "(%s)" (expr_to_string f) )
    | BinaryOp (op, l, r) ->
      Printf.sprintf "%s %s %s"
        ( match l with
          | Variable _ | Function _ | UnaryOp _ ->
            expr_to_string l
          | _ ->
            Printf.sprintf "(%s)" (expr_to_string l) )
        (binary_op_to_string op)
        ( match r with
          | Variable _ | Function _ | UnaryOp _ ->
            expr_to_string r
          | _ ->
            Printf.sprintf "(%s)" (expr_to_string r) )
    | Tuple fs ->
      Printf.sprintf "(%s)" (String.concat ", " (List.map expr_to_string fs))

  module Expr_parser = struct
    let parens (p : expr stateless_p) : expr stateless_p =
      ignore_space (skip_char '(')
      >> p
      >>= fun x -> ignore_space (skip_char ')') >> return x

    let opt_parens p = parens p <|> p

    let prefix (sym : string) (op : unary_op) : (expr, unit) operator =
      Prefix
        (attempt
           ( spaces >> skip_string sym >> spaces
             >> return (fun x -> UnaryOp (op, x)) ))

    let infix (sym : string) (op : binary_op) : (expr, unit) operator =
      Infix
        ( attempt
            ( spaces >> skip_string sym >> spaces
              >> return (fun a b -> BinaryOp (op, a, b)) )
        , Assoc_left )

    let operators = [[prefix "!" Not]; [infix "=" Eq]; [infix "<>" Neq]]

    let rec atom_p s =
      (ignore_space (ident_p >>= fun ident -> return (Variable ident))) s

    and func_p s =
      (ignore_space
         ( ident_p
           >>= fun ident ->
           char '('
           >> sep_by1 expr_p (char ',')
           >>= fun params -> char ')' >> return (Function (ident, params)) ))
        s

    and tuple_p s =
      ( ignore_space (skip_char '(')
        >> sep_by1 expr_p (char ',')
        >>= fun fs -> ignore_space (skip_char ')') >> return (Tuple fs) )
        s

    and sub_expr_p s =
      choice [attempt func_p; attempt atom_p; attempt tuple_p] s

    and expr_p s = expression operators sub_expr_p s
  end

  type ty = string

  type proc_instance_ty =
    | Single
    | Multi

  type pv_proc_expr =
    | Let of ident_or_ident_ty_or_pat list * expr
    | IfElse of if_else
    | In of ident * ident_ty_or_pat list
    | Out of ident * expr
    | Zero
    | New of ident * ty
    | Get of ident * ident_or_ident_ty_or_pat list
    | Insert of ident * ident_or_ident_ty_or_pat list

  and if_else =
    { condition : expr
    ; true_branch : pv_proc_expr list
    ; false_branch : pv_proc_expr list }

  type pv_expr =
    | Const of ident * ty * visibility
    | Free of ident * ty * visibility
    | Table of ident * ty list
    | FunDec of ident * ty list * ty
    | Equation of equation
    | LetProc of ident * (ident * ty) list * pv_proc_expr list
    | Process of pv_proc_expr list * (proc_instance_ty * proc) list
    | Query of expr

  and equation =
    { vars : (ident * ty) list
    ; formula : expr }

  and proc =
    | Name of ident * ident list
    | Proc of pv_proc_expr list

  module Print_context = struct
    type pv_proc_structure_type =
      | Let
      | IfElse
      | InOut
      | Zero
      | New
      | Get
      | Insert

    type pv_structure_type =
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
      ; mutable prev_struct_ty : pv_structure_type option
      ; mutable cur_struct_ty : pv_structure_type option
      ; mutable prev_proc_struct_ty : pv_proc_structure_type option
      ; mutable cur_proc_struct_ty : pv_proc_structure_type option
      ; mutable out_count : int
      ; mutable indent : int
      ; mutable buffer : (int * string) list }

    let make () =
      { proc_name = None
      ; prev_struct_ty = None
      ; cur_struct_ty = None
      ; prev_proc_struct_ty = None
      ; cur_proc_struct_ty = None
      ; out_count = 0
      ; indent = 0
      ; buffer = [] }

    let reset ctx =
      ctx.proc_name <- None;
      ctx.prev_struct_ty <- None;
      ctx.cur_struct_ty <- None;
      ctx.prev_proc_struct_ty <- None;
      ctx.cur_proc_struct_ty <- None;
      ctx.out_count <- 1;
      ctx.indent <- 0;
      ctx.buffer <- []

    let set_struct_ty ctx ty =
      ctx.prev_struct_ty <- ctx.cur_struct_ty;
      ctx.cur_struct_ty <- Some ty

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

    let insert_blank_line_if_diff_struct_ty ctx =
      match (ctx.prev_struct_ty, ctx.cur_struct_ty) with
      | Some ty1, Some ty2 when ty1 <> ty2 ->
        push ctx ""
      | _ ->
        ()

    let insert_blank_line_anyway_struct_ty ctx =
      match ctx.prev_struct_ty with Some _ -> push ctx "" | None -> ()

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
              Printf.sprintf "%s%s" padding s :: acc)
           [] ctx.buffer)
  end

  let rec pv_proc_expr_to_string_debug e =
    match e with
    | Let (args, e) -> (
        match args with
        | [Ident ident] ->
          Printf.sprintf "let %s = %s" ident (expr_to_string e)
        | _ ->
          Printf.sprintf "let (%s) = %s"
            (String.concat ", "
               (List.map
                  (function
                    | Ident i ->
                      i
                    | Ident_ty (i, ty) ->
                      Printf.sprintf "%s : %s" i ty
                    | Pat e ->
                      Printf.sprintf "=%s" (expr_to_string e))
                  args))
            (expr_to_string e) )
    | IfElse x -> (
        let cond = expr_to_string x.condition in
        let true_branch =
          String.concat "\n"
            (List.map pv_proc_expr_to_string_debug x.true_branch)
        in
        let false_branch =
          String.concat "\n"
            (List.map pv_proc_expr_to_string_debug x.false_branch)
        in
        match x.false_branch with
        | [] ->
          Printf.sprintf "if %s then\n%s" cond true_branch
        | _ ->
          Printf.sprintf "if %s then\n%s\nelse\n%s" cond true_branch
            false_branch )
    | In (ident, args) ->
      Printf.sprintf "in(%s, %s);" ident
        (String.concat ", "
           (List.map
              (fun (e : ident_ty_or_pat) ->
                 match e with
                 | Ident_ty (i, ty) ->
                   Printf.sprintf "%s:%s" i ty
                 | Pat e ->
                   Printf.sprintf "=%s" (expr_to_string e))
              args))
    | Out (ident, e) ->
      Printf.sprintf "out(%s, %s);" ident (expr_to_string e)
    | Zero ->
      "0"
    | New (ident, ty) ->
      Printf.sprintf "new %s:%s" ident ty
    | Get (ident, args) ->
      Printf.sprintf "get %s(%s)" ident
        (String.concat ", "
           (List.map
              (function
                | Ident i ->
                  i
                | Ident_ty (i, ty) ->
                  Printf.sprintf "%s : %s" i ty
                | Pat e ->
                  Printf.sprintf "=%s" (expr_to_string e))
              args))
    | Insert (ident, args) ->
      Printf.sprintf "insert %s(%s)" ident
        (String.concat ", "
           (List.map
              (function
                | Ident i ->
                  i
                | Ident_ty (i, ty) ->
                  Printf.sprintf "%s : %s" i ty
                | Pat e ->
                  Printf.sprintf "=%s" (expr_to_string e))
              args))

  and pv_proc_exprs_to_string_debug es =
    String.concat "\n" (List.map pv_proc_expr_to_string_debug es)

  let rec pv_expr_to_string_debug e =
    match e with
    | Const (ident, ty, v) ->
      Printf.sprintf "const %s : %s%s." ident ty
        (match v with Public -> "" | Private -> " [private]")
    | Free (ident, ty, v) ->
      Printf.sprintf "free %s : %s%s." ident ty
        (match v with Public -> "" | Private -> " [private]")
    | Table (ident, tys) ->
      Printf.sprintf "table %s(%s)." ident (String.concat ", " tys)
    | FunDec (ident, tys, ret_ty) ->
      Printf.sprintf "fun %s(%s) : %s." ident (String.concat ", " tys) ret_ty
    | Equation eq ->
      Printf.sprintf "equation forall %s, %s."
        (String.concat " "
           (List.map
              (fun (ident, ty) -> Printf.sprintf "%s:%s" ident ty)
              eq.vars))
        (expr_to_string eq.formula)
    | LetProc (ident, args, es) -> (
        match args with
        | [] ->
          Printf.sprintf "let %s =\n%s" ident
            (pv_proc_exprs_to_string_debug es)
        | _ ->
          Printf.sprintf "let %s(%s) =\n%s" ident
            (String.concat ", "
               (List.map
                  (fun (ident, ty) -> Printf.sprintf "%s : %s" ident ty)
                  args))
            (pv_proc_exprs_to_string_debug es) )
    (* | FunApp(ident, es) -> Printf.sprintf "%s(%s)" ident (String.concat ", " (List.map aux es)) *)
    | Process (proc, ps) ->
      Printf.sprintf "process %s%s"
        (pv_proc_exprs_to_string_debug proc)
        (String.concat " | "
           (List.map
              (fun (instance_ty, p) ->
                 match p with
                 | Name (name, args) -> (
                     match instance_ty with
                     | Single -> (
                         match args with
                         | [] ->
                           name
                         | _ ->
                           Printf.sprintf "%s(%s)" name
                             (String.concat ", " args) )
                     | Multi ->
                       Printf.sprintf "(! %s)"
                         ( match args with
                           | [] ->
                             name
                           | _ ->
                             Printf.sprintf "%s(%s)" name
                               (String.concat ", " args) ) )
                 | Proc p -> (
                     match instance_ty with
                     | Single ->
                       Printf.sprintf "(%s)"
                         (String.concat "\n"
                            (List.map pv_proc_expr_to_string_debug p))
                     | Multi ->
                       Printf.sprintf "(! (%s))"
                         (String.concat "\n"
                            (List.map pv_proc_expr_to_string_debug p)) ))
              ps))
    | Query e ->
      Printf.sprintf "query %s." (expr_to_string e)

  and pv_exprs_to_string_debug es =
    String.concat "\n" (List.map pv_expr_to_string_debug es)

  let pv_proc_expr_to_string ctx e =
    let rec aux e =
      match e with
      | Let (args, e) ->
        Print_context.set_proc_struct_ty ctx Print_context.Let;
        Print_context.insert_blank_line_if_diff_proc_struct_ty ctx;
        Print_context.push ctx
          ( match args with
            | [Ident ident] ->
              Printf.sprintf "let %s = %s" ident (expr_to_string e)
            | _ ->
              Printf.sprintf "let (%s) = %s"
                (String.concat ", "
                   (List.map
                      (function
                        | Ident i ->
                          i
                        | Ident_ty (i, ty) ->
                          Printf.sprintf "%s : %s" i ty
                        | Pat e ->
                          Printf.sprintf "=%s" (expr_to_string e))
                      args))
                (expr_to_string e) )
      | IfElse x -> (
          Print_context.set_proc_struct_ty ctx Print_context.IfElse;
          Print_context.insert_blank_line_if_diff_proc_struct_ty ctx;
          let cond = expr_to_string x.condition in
          Print_context.push ctx (Printf.sprintf "if %s then" cond);
          Print_context.incre_indent ctx;
          aux_s x.true_branch;
          Print_context.decre_indent ctx;
          match x.false_branch with
          | [] ->
            ()
          | _ ->
            Print_context.push ctx "else";
            Print_context.incre_indent ctx;
            aux_s x.false_branch;
            Print_context.decre_indent ctx )
      | In (_, args) ->
        Print_context.set_proc_struct_ty ctx Print_context.InOut;
        Print_context.insert_blank_line_if_diff_proc_struct_ty ctx;
        let proc_name =
          match ctx.proc_name with Some name -> name | None -> ""
        in
        let padding_len =
          match ctx.proc_name with
          | Some name ->
            String.length name + 2 + 4
          | None ->
            0
        in
        let padding = String.make padding_len ' ' in
        Print_context.push ctx
          (Printf.sprintf "%sI -> %s : IN (%s)" padding proc_name
             (String.concat ", "
                (List.map
                   (fun (e : ident_ty_or_pat) ->
                      match e with
                      | Ident_ty (i, ty) ->
                        Printf.sprintf "%s:%s" i ty
                      | Pat e ->
                        Printf.sprintf "=%s" (expr_to_string e))
                   args)))
      | Out (_, e) ->
        Print_context.set_proc_struct_ty ctx Print_context.InOut;
        Print_context.insert_blank_line_if_diff_proc_struct_ty ctx;
        Print_context.incre_out_count ctx;
        let proc_name =
          match ctx.proc_name with Some name -> name | None -> ""
        in
        let proc_step_tag =
          match ctx.proc_name with
          | Some name ->
            Printf.sprintf "%s.%d" name ctx.out_count
          | None ->
            ""
        in
        Print_context.push ctx
          (Printf.sprintf "%s    %s -> I : OUT(%s)" proc_step_tag proc_name
             (expr_to_string e))
      | Zero ->
        Print_context.set_proc_struct_ty ctx Print_context.Zero;
        Print_context.insert_blank_line_if_diff_proc_struct_ty ctx;
        Print_context.push ctx "0"
      | New (ident, _) ->
        Print_context.set_proc_struct_ty ctx Print_context.New;
        Print_context.insert_blank_line_if_diff_proc_struct_ty ctx;
        Print_context.push ctx (Printf.sprintf "new %s" ident)
      | Get (ident, args) ->
        Print_context.set_proc_struct_ty ctx Print_context.Get;
        Print_context.insert_blank_line_if_diff_proc_struct_ty ctx;
        Print_context.push ctx
          (Printf.sprintf "get %s(%s)" ident
             (String.concat ", "
                (List.map
                   (function
                     | Ident i ->
                       i
                     | Ident_ty (i, ty) ->
                       Printf.sprintf "%s : %s" i ty
                     | Pat e ->
                       Printf.sprintf "=%s" (expr_to_string e))
                   args)))
      | Insert (ident, args) ->
        Print_context.set_proc_struct_ty ctx Print_context.Get;
        Print_context.insert_blank_line_if_diff_proc_struct_ty ctx;
        Print_context.push ctx
          (Printf.sprintf "insert %s(%s)" ident
             (String.concat ", "
                (List.map
                   (function
                     | Ident i ->
                       i
                     | Ident_ty (i, ty) ->
                       Printf.sprintf "%s : %s" i ty
                     | Pat e ->
                       Printf.sprintf "=%s" (expr_to_string e))
                   args)))
    and aux_s es = List.iter aux es in
    aux e

  let pv_proc_exprs_to_string ctx es =
    List.iter (pv_proc_expr_to_string ctx) es

  let pv_expr_to_string ?(ctx = Print_context.make ()) e =
    let aux e =
      match e with
      | Const (ident, ty, v) ->
        Print_context.set_struct_ty ctx Print_context.Const;
        Print_context.insert_blank_line_if_diff_struct_ty ctx;
        Print_context.push ctx
          (Printf.sprintf "const %s : %s%s." ident ty
             (match v with Public -> "" | Private -> " [private]"))
      | Free (ident, ty, v) ->
        Print_context.set_struct_ty ctx Print_context.Free;
        Print_context.insert_blank_line_if_diff_struct_ty ctx;
        Print_context.push ctx
          (Printf.sprintf "free %s : %s%s." ident ty
             (match v with Public -> "" | Private -> " [private]"))
      | Table (ident, tys) ->
        Print_context.set_struct_ty ctx Print_context.Table;
        Print_context.insert_blank_line_if_diff_struct_ty ctx;
        Print_context.push ctx
          (Printf.sprintf "table %s(%s)." ident (String.concat ", " tys))
      | FunDec (ident, tys, ret_ty) ->
        Print_context.set_struct_ty ctx Print_context.FunDec;
        Print_context.insert_blank_line_if_diff_struct_ty ctx;
        Print_context.push ctx
          (Printf.sprintf "fun %s(%s) : %s." ident (String.concat ", " tys)
             ret_ty)
      | Equation eq ->
        Print_context.set_struct_ty ctx Print_context.Equation;
        Print_context.insert_blank_line_if_diff_struct_ty ctx;
        Print_context.push ctx
          (Printf.sprintf "equation forall %s, %s."
             (String.concat " "
                (List.map
                   (fun (ident, ty) -> Printf.sprintf "%s:%s" ident ty)
                   eq.vars))
             (expr_to_string eq.formula))
      | LetProc (ident, args, es) ->
        Print_context.set_proc_name ctx ident;
        Print_context.set_struct_ty ctx Print_context.LetProc;
        Print_context.insert_blank_line_anyway_struct_ty ctx;
        ( match args with
          | [] ->
            Print_context.push ctx (Printf.sprintf "let %s =" ident)
          | _ ->
            Print_context.push ctx
              (Printf.sprintf "let %s(%s) =" ident
                 (String.concat ", "
                    (List.map
                       (fun (ident, ty) -> Printf.sprintf "%s : %s" ident ty)
                       args))) );
        Print_context.incre_indent ctx;
        pv_proc_exprs_to_string ctx es;
        Print_context.decre_indent ctx
      | Process (proc, ps) ->
        Print_context.set_proc_name_none ctx;
        Print_context.set_struct_ty ctx Print_context.Process;
        Print_context.insert_blank_line_anyway_struct_ty ctx;
        Print_context.push ctx "process";
        Print_context.incre_indent ctx;
        pv_proc_exprs_to_string ctx proc;
        List.iter
          (fun (instance_ty, p) ->
             match p with
             | Name (name, args) -> (
                 match instance_ty with
                 | Single -> (
                     match args with
                     | [] ->
                       Print_context.push ctx (Printf.sprintf "| %s" name)
                     | _ ->
                       Print_context.push ctx
                         (Printf.sprintf "| %s(%s)" name
                            (String.concat ", " args)) )
                 | Multi -> (
                     match args with
                     | [] ->
                       Print_context.push ctx (Printf.sprintf "| (! %s)" name)
                     | _ ->
                       Print_context.push ctx
                         (Printf.sprintf "| (! %s(%s))" name
                            (String.concat ", " args)) ) )
             | Proc es ->
               ( match instance_ty with
                 | Single ->
                   Print_context.push ctx "| ("
                 | Multi ->
                   Print_context.push ctx "| ! (" );
               Print_context.incre_indent ctx;
               pv_proc_exprs_to_string ctx es;
               Print_context.push ctx ")";
               Print_context.decre_indent ctx)
          ps;
        Print_context.decre_indent ctx
      | Query e ->
        Print_context.set_struct_ty ctx Print_context.Query;
        Print_context.insert_blank_line_if_diff_struct_ty ctx;
        Print_context.set_struct_ty ctx Print_context.Query;
        Print_context.push ctx
          (Printf.sprintf "query %s." (expr_to_string e))
    in
    aux e

  let pv_exprs_to_string es =
    let ctx = Print_context.make () in
    List.iter (pv_expr_to_string ~ctx) es;
    Print_context.finish ctx

  module Parser = struct
    let parens p = skip_char '(' >> p >>= fun x -> skip_char ')' >> return x

    let opt_parens p = parens p <|> p

    let const_p =
      ignore_space
        ( skip_string "const" >> spaces >> ident_p
          >>= fun ident ->
          spaces >> char ':' >> spaces >> ident_p
          >>= fun ty ->
          ignore_space (skip_char '[')
          >> ignore_space (skip_string "private")
          >> ignore_space (skip_char ']')
          >> skip_char '.'
          >> return (Free (ident, ty, Private))
             <|> (skip_char '.' >> return (Free (ident, ty, Public))) )

    let free_p =
      ignore_space
        ( skip_string "free" >> spaces >> ident_p
          >>= fun ident ->
          spaces >> char ':' >> spaces >> ident_p
          >>= fun ty ->
          ignore_space (skip_char '[')
          >> ignore_space (skip_string "private")
          >> ignore_space (skip_char ']')
          >> skip_char '.'
          >> return (Free (ident, ty, Private))
             <|> (skip_char '.' >> return (Free (ident, ty, Public))) )

    let arg_p = ignore_space ident_p

    let args_p =
      many1 (arg_p >>= fun arg -> optional (skip_char ',') >> return arg)

    let ident_ty_p =
      ignore_space ident_p
      >>= fun ident ->
      ignore_space (skip_char ':') >> ident_p >>= fun ty -> return (ident, ty)

    let ident_or_ident_ty_or_pat_p =
      ignore_space
        ( attempt
            ( ident_ty_p
              >>= fun (i, ty) ->
              return (Ident_ty (i, ty) : ident_or_ident_ty_or_pat) )
          <|> (ident_p >>= fun x -> return (Ident x))
          <|> ( skip_char '=' >> Expr_parser.expr_p
                >>= fun e -> return (Pat e : ident_or_ident_ty_or_pat) ) )

    let ident_ty_or_pat_p =
      ignore_space
        ( ident_ty_p
          >>= (fun (i, ty) -> return (Ident_ty (i, ty) : ident_ty_or_pat))
              <|> ( skip_char '=' >> Expr_parser.expr_p
                    >>= fun e -> return (Pat e : ident_ty_or_pat) ) )

    let fun_dec_p =
      ignore_space
        ( skip_string "fun" >> ignore_space ident_p
          >>= fun ident ->
          skip_char '(' >> args_p
          >>= fun tys ->
          skip_char ')'
          >> ignore_space (skip_char ':')
          >> ignore_space ident_p
          >>= fun ret_ty -> skip_char '.' >> return (FunDec (ident, tys, ret_ty))
        )

    let table_p =
      ignore_space
        ( skip_string "table" >> ignore_space ident_p
          >>= fun ident ->
          skip_char '(' >> args_p
          >>= fun tys ->
          ignore_space (skip_char ')')
          >> skip_char '.'
          >> return (Table (ident, tys)) )

    let eq_p =
      ignore_space
        ( skip_string "equation" >> spaces >> skip_string "forall" >> spaces
          >> sep_by ident_ty_p (ignore_space (skip_char ','))
          >>= fun vars ->
          ignore_space (skip_char ';')
          >> Expr_parser.expr_p
          >>= fun formula -> skip_char '.' >> return (Equation {vars; formula})
        )

    let query_p =
      ignore_space
        ( skip_string "query" >> spaces >> Expr_parser.expr_p
          >>= fun f -> skip_char '.' >> return (Query f) )

    let get_p =
      ignore_space (skip_string "get")
      >> ignore_space ident_p
      >>= fun ident ->
      ignore_space (skip_char '(')
      >> sep_by ident_or_ident_ty_or_pat_p (ignore_space (skip_char ','))
      >>= fun args ->
      ignore_space (skip_char ')')
      >> ignore_space (skip_string "in")
      >> return (Get (ident, args))

    let insert_p =
      ignore_space (skip_string "insert")
      >> ignore_space ident_p
      >>= fun ident ->
      ignore_space (skip_char '(')
      >> sep_by ident_or_ident_ty_or_pat_p (ignore_space (skip_char ','))
      >>= fun args ->
      ignore_space (skip_char ')')
      >> ignore_space (optional (skip_string ";"))
      >> return (Insert (ident, args))

    let rec let_p s =
      ( ignore_space (skip_string "let")
        >> ( ignore_space ident_p
             >>= (fun ident ->
                 ignore_space (skip_char '=')
                 >> Expr_parser.expr_p
                 >>= fun f ->
                 ignore_space (skip_string "in")
                 >> return (Let ([Ident ident], f)))
                 <|> ( ignore_space (skip_char '(')
                       >> sep_by ident_or_ident_ty_or_pat_p
                         (ignore_space (skip_char ','))
                       >>= fun args ->
                       ignore_space (skip_char ')')
                       >> ignore_space (skip_char '=')
                       >> Expr_parser.expr_p
                       >>= fun f ->
                       ignore_space (skip_string "in") >> return (Let (args, f)) ) ) )
        s

    and if_else_p s =
      ( ignore_space (skip_string "if")
        >> ignore_space Expr_parser.expr_p
        >>= fun condition ->
        ignore_space (skip_string "then")
        >> ignore_space (opt_parens proc_exprs_p)
        >>= fun true_branch ->
        ignore_space (skip_string "else")
        >> opt_parens
          ( proc_exprs_p
            >>= fun false_branch ->
            return (IfElse {condition; true_branch; false_branch}) )
           <|> return (IfElse {condition; true_branch; false_branch = []}) )
        s

    and in_p =
      ignore_space (skip_string "in")
      >> ignore_space
        ( skip_char '(' >> ignore_space ident_p
          >>= fun ident ->
          ignore_space (skip_char ',')
          >> ( parens
                 ( sep_by1 ident_ty_or_pat_p (ignore_space (skip_char ','))
                   >>= fun args -> return (In (ident, args)) )
               <|> ( ident_ty_p
                     >>= fun (ident, ty) ->
                     return (In (ident, [Ident_ty (ident, ty)])) ) )
          >>= fun r ->
          ignore_space (skip_char ')')
          >> ignore_space (optional (skip_char ';'))
          >> return r )

    and out_p =
      ignore_space (skip_string "out")
      >> ignore_space
        ( skip_char '(' >> ignore_space ident_p
          >>= fun ident ->
          ignore_space (skip_char ',')
          >> Expr_parser.expr_p
          >>= fun e ->
          ignore_space (skip_char ')')
          >> ignore_space (optional (skip_char ';'))
          >> return (Out (ident, e)) )

    and zero_p = ignore_space (char '0') >> return Zero

    and new_p =
      ignore_space (skip_string "new")
      >> ignore_space ident_ty_p
      >>= fun (ident, ty) ->
      ignore_space (optional (skip_char ';')) >> return (New (ident, ty))

    and proc_expr_p s =
      choice
        [ attempt let_p
        ; attempt if_else_p
        ; attempt in_p
        ; attempt out_p
        ; attempt zero_p
        ; attempt new_p
        ; attempt get_p
        ; attempt insert_p ]
        s

    and proc_exprs_p s = many (ignore_space proc_expr_p) s

    let let_proc_p =
      ignore_space (skip_string "let")
      >> ignore_space ident_p
      >>= fun ident ->
      ignore_space (skip_char '(')
      >> sep_by ident_ty_p (ignore_space (skip_char ','))
      >>= (fun args ->
          ignore_space (skip_char ')')
          >> ignore_space (skip_char '=')
          >> proc_exprs_p
          >>= fun es ->
          ignore_space (skip_char '.') >> return (LetProc (ident, args, es)))
          <|> ( ignore_space (skip_char '=')
                >> proc_exprs_p
                >>= fun es ->
                ignore_space (skip_char '.') >> return (LetProc (ident, [], es)) )

    let proc_p =
      ignore_space (skip_string "process")
      >> ( proc_exprs_p
           >>= fun proc ->
           sep_by1
             (ignore_space
                ( attempt
                    (parens
                       ( ignore_space (skip_char '!')
                         >> choice
                           [ ( parens proc_exprs_p
                               >>= fun es -> return (Multi, Proc es) )
                           ; attempt
                               ( ident_p
                                 >>= fun ident ->
                                 ignore_space (skip_char '(')
                                 >> sep_by ident_p (ignore_space (skip_char ','))
                                 >>= fun args ->
                                 ignore_space (skip_char ')')
                                 >> return (Multi, Name (ident, args)) )
                           ; ( ident_p
                               >>= fun ident -> return (Multi, Name (ident, []))
                             ) ] ))
                  <|> choice
                    [ ( parens proc_exprs_p
                        >>= fun es -> return (Single, Proc es) )
                    ; attempt
                        ( ident_p
                          >>= fun ident ->
                          ignore_space (skip_char '(')
                          >> sep_by ident_p (ignore_space (skip_char ','))
                          >>= fun args ->
                          ignore_space (skip_char ')')
                          >> return (Single, Name (ident, args)) )
                    ; ( ident_p
                        >>= fun ident -> return (Single, Name (ident, [])) ) ] ))
             (ignore_space (skip_char '|'))
           >>= fun ps -> return (Process (proc, ps)) )

    let expr_p =
      choice
        [const_p; free_p; table_p; fun_dec_p; query_p; eq_p; let_proc_p; proc_p]

    let exprs_p = many (ignore_space expr_p)

    let comment_p =
      skip_string "(*"
      >> many_until skip_any_char_or_nl (skip_string "*)")
      >> return []

    let not_comment_p =
      many_until any_char_or_nl (look_ahead (skip_string "(*") <|> eof)

    let no_comments_p = many_until (comment_p <|> not_comment_p) eof
  end
end

let remove_comments s =
  match MParser.parse_string Raw_expr.Parser.no_comments_p s () with
  | Success l ->
    Ok (Core_kernel.String.of_char_list (List.concat l))
  | Failed (m, _) ->
    Error m

let process_string s =
  match remove_comments s with
  | Error e ->
    Error e
  | Ok s -> (
      match MParser.parse_string Raw_expr.Parser.exprs_p s () with
      | Success ps ->
        Ok (Raw_expr.pv_exprs_to_string ps)
      | Failed (s, _) ->
        Error s )

let str =
  {|
const ZERO : bitstring.

free c : channel.

fun h(bitstring) : bitstring.

fun xor(bitstring, bitstring) : bitstring.

(* associativity *)
equation forall x:bitstring, y:bitstring, z:bitstring; xor(x, xor(y, z)) = xor(xor(x, y), z).

(* commutativity *)
equation forall x:bitstring, y:bitstring; xor(x, y) = xor(y, x).

(* neutral element *)
equation forall x:bitstring; xor(x, ZERO) = x.

(* nilpotence *)
equation forall x:bitstring; xor(x, x) = ZERO.

fun rotate(bitstring, bitstring) : bitstring.

fun split_L(bitstring) : bitstring.
fun split_R(bitstring) : bitstring.

free k  : bitstring [private].
free ID : bitstring [private].

free objective : bitstring [private].

query attacker(objective).

let R =
  new r1:bitstring;
  out(c, r1);                           (* 1. send r1 R -> T *)
  in(c, (r2             : bitstring,
         left_xor_ID2_g : bitstring));  (* 2. recv left(xor(ID2, g))
                                           T -> R *)
  let g     = h(xor(xor(r1, r2), k)) in
  let ID2   = rotate(ID, g) in
  let left  = split_L(xor(ID2, g)) in
  let right = split_R(xor(ID2, g)) in
  if left = left_xor_ID2_g then (
    out(c, right);                      (* 3. send right(xor(ID2, g))
                                           R -> T *)
    (* authenticated, send out objective *)
    out(c, objective)
  ).

|}

let () =
  match process_string str with
  | Ok s ->
    Js_utils.console_log s
  | Error e ->
    Js_utils.console_log e
