open Pitptree

(* The following pretty printing code (the use of context and style that handles indentation)
 * is largely copied from Narrator
*)

module Print_context = struct
  type tprocess_structure_type =
    | PNil_
    | PPar_
    | PRepl_
    | PRestr_
    | PLetDef_
    | PTest_
    | PInput_
    | POutput_
    | PLet_
    | PLetFilter_
    | PEvent_
    | PPhase_
    | PBarrier_
    | PInsert_
    | PGet_

  type tdecl_structure_type =
    | TTypeDecl_
    | TFunDecl_
    | TEventDecl_
    | TConstDecl_
    | TReduc_
    | TReducFail_
    | TEquation_
    | TPredDecl_
    | TTableDecl_
    | TSet_
    | TPDef_
    | TQuery_
    | TNoninterf_
    | TWeaksecret_
    | TNoUnif_
    | TNot_
    | TElimtrue_
    | TFree_
    | TClauses_
    | TDefine_
    | TExpand_
    | TLetFun_

  let indent_space_count = 2

  type t = {
    mutable prev_tproc_struct_ty : tprocess_structure_type option;
    mutable cur_tproc_struct_ty : tprocess_structure_type option;
    mutable prev_tdecl_struct_ty : tdecl_structure_type option;
    mutable cur_tdecl_struct_ty : tdecl_structure_type option;
    mutable indent : int;
    mutable buffer : (int * string) list;
  }

  let make () =
    { prev_tproc_struct_ty = None;
      cur_tproc_struct_ty = None;
      prev_tdecl_struct_ty = None;
      cur_tdecl_struct_ty = None;
      indent = 0;
      buffer = [];
    }

  let reset ctx =
    ctx.prev_tproc_struct_ty <- None;
    ctx.cur_tproc_struct_ty <- None;
    ctx.prev_tdecl_struct_ty <- None;
    ctx.cur_tdecl_struct_ty <- None;
    ctx.indent <- 0;
    ctx.buffer <- []

  let set_tproc_struct_ty ctx ty =
    ctx.prev_tproc_struct_ty <- ctx.cur_tproc_struct_ty;
    ctx.cur_tproc_struct_ty <- Some ty

  let set_tdecl_struct_ty ctx ty =
    ctx.prev_tproc_struct_ty <- None;
    ctx.cur_tproc_struct_ty <- None;
    ctx.prev_tdecl_struct_ty <- ctx.cur_tdecl_struct_ty;
    ctx.cur_tdecl_struct_ty <- Some ty

  let incre_indent ctx =
    ctx.indent <- ctx.indent + 1

  let decre_indent ctx =
    ctx.indent <- ctx.indent - 1

  let push ctx (s : string) =
    ctx.buffer <- (ctx.indent, s) :: ctx.buffer

  let push_to_last_line ctx (s : string) =
    ctx.buffer <-
      match ctx.buffer with
      | [] -> [(ctx.indent, s)]
      | (i, x) :: xs -> (i, x ^ s) :: xs

  let insert_blank_line_if_diff_tproc_struct_ty ctx =
    match ctx.prev_tproc_struct_ty, ctx.cur_tproc_struct_ty with
    | (Some ty1, Some ty2) when ty1 <> ty2 -> push ctx ""
    | _ -> ()

  let insert_blank_line_anyway_tproc_struct_ty ctx =
    match ctx.prev_tproc_struct_ty with
    | Some _ -> push ctx ""
    | None -> ()

  let insert_blank_line_if_diff_tdecl_struct_ty ctx =
    match ctx.prev_tdecl_struct_ty, ctx.cur_tdecl_struct_ty with
    | (Some ty1, Some ty2) when ty1 <> ty2 -> push ctx ""
    | _ -> ()

  let insert_blank_line_anyway_tdecl_struct_ty ctx =
    match ctx.prev_tdecl_struct_ty with
    | Some _ -> push ctx ""
    | None -> ()

  let finish ctx =
    String.concat "\n"
      (List.fold_left
         (fun acc (indent, s) ->
            let padding = String.make (indent * indent_space_count) ' ' in
            Printf.sprintf "%s%s" padding s :: acc
         )
         []
         ctx.buffer)
end

let list_iter_check_if_last (f : bool -> 'a -> unit) (l : 'a list) =
  let last_index = List.length l - 1 in
  List.iteri (fun index e ->
      f (index = last_index) e
    ) l

let ident_to_string (id, _) = id

let idents_to_string ids =
  String.concat ", "
    (List.map ident_to_string ids)

let rec tpattern_to_string t : string =
  let rec aux t =
    match t with
    | PPatVar (id, ty) -> (
        match ty with
        | None -> ident_to_string id
        | Some ty -> Printf.sprintf "%s : %s" (ident_to_string id) (ident_to_string ty)
      )
    | PPatTuple ts ->
      Printf.sprintf "(%s)"
        (String.concat ", " (List.map aux ts))
    | PPatFunApp (f, args) ->
      Printf.sprintf "%s(%s)"
        (ident_to_string f)
        (String.concat ", " (List.map aux args))
    | PPatEqual t ->
      Printf.sprintf "=%s" (pterm_e_to_string t)
  in

  aux t

and pterm_e_to_string t : string =
  let rec aux (t, _) =
    match t with
    | PPIdent (x, _) -> x
    | PPFunApp ((f, _), [l; r]) when f = "="
                                || f = "<>"
                                || f = "&&"
                                || f = "||" ->
        Printf.sprintf "%s %s %s"
          (pterm_e_to_string l)
          f
          (pterm_e_to_string r)
    | PPFunApp (id, args) ->
      Printf.sprintf "%s(%s)"
        (ident_to_string id)
        (pterm_e_s_to_string args)
    | PPTuple l ->
      Printf.sprintf "(%s)"
        (pterm_e_s_to_string l)
    | PPRestr (id, ids, ty, next) ->
      let ids = match ids with
        | None -> [id]
        | Some l -> id :: l
      in
      Printf.sprintf "new %s : %s; %s" (idents_to_string ids) (ident_to_string ty) (aux next)
    | PPTest (cond, true_branch, false_branch) -> (
        match false_branch with
        | None -> Printf.sprintf "if %s then (%s)"
                    (aux cond)
                    (aux true_branch)
        | Some t -> Printf.sprintf "if %s then (%s) else (%s)"
                      ( aux cond)
                      (aux true_branch)
                      (aux t)
      )
    | PPLet (pat, term, true_branch, false_branch) -> (
        match false_branch with
        | None -> Printf.sprintf "let %s = %s in %s"
                    (tpattern_to_string pat)
                    (aux term)
                    (aux true_branch)
        | Some t -> Printf.sprintf "let %s = %s in %s else %s"
                      (tpattern_to_string pat)
                      (aux term)
                      (aux true_branch)
                      (aux t)
      )
    | PPLetFilter (id_tys, term, true_branch, false_branch) -> (
        let id_tys_string = String.concat ", "
            (List.map (fun (id, ty) ->
                 Printf.sprintf "%s : %s"
                   (ident_to_string id)
                   (ident_to_string ty)
               )
                id_tys)
        in
        match false_branch with
        | None -> Printf.sprintf "let %s suchthat %s in %s"
                    id_tys_string
                    (aux term)
                    (aux true_branch)
        | Some t -> Printf.sprintf "let %s suchthat %s in %s else %s"
                      id_tys_string
                      (aux term)
                      (aux true_branch)
                      (aux t)
      )
    | PPEvent (id, terms, _, next) -> (
        (match terms with
        | [] -> Printf.sprintf "event %s" (ident_to_string id)
        | l -> Printf.sprintf "event %s (%s)"
                 (ident_to_string id)
                 (pterm_e_s_to_string l)
        )
        ^
        (Printf.sprintf "; %s" (aux next))
      )
    | PPInsert (id, terms, next) -> (
        (Printf.sprintf "insert %s(%s)"
          (ident_to_string id)
          (pterm_e_s_to_string terms)
        )
        ^
        (Printf.sprintf "; %s"
           (aux next))
      )
    | PPGet (id, terms, cond, true_branch, false_branch) -> (
        (Printf.sprintf "get %s(%s)"
           (ident_to_string id)
           (String.concat ", "
              (List.map tpattern_to_string terms)))
        ^
        (match cond with
         | None -> ""
         | Some c -> Printf.sprintf " suchthat %s " (aux c)
        )
        ^
        (Printf.sprintf "in (%s)"
           (aux true_branch))
        ^
        (match false_branch with
         | None -> ""
         | Some t -> Printf.sprintf " else (%s)" (aux t)
        )
      )
  in

  aux t

and pterm_e_s_to_string ts : string =
  String.concat ", "
    (List.map pterm_e_to_string ts)

and tpatterns_to_string pats : string =
  String.concat ", "
    (List.map tpattern_to_string pats)

let pval_to_string v : string =
  let open Ptree in

  match v with
  | S s -> ident_to_string s
  | I d -> string_of_int d

let rec term_e_to_string (t, _) : string =
  match t with
  | PIdent s -> ident_to_string s
  | PFail -> "fail"
  | PFunApp (f, args) ->
    Printf.sprintf "%s(%s)"
      (ident_to_string f)
      (term_e_s_to_string args)
  | PProj (id, term) ->
    Printf.sprintf "%s -proj- %s"
      (ident_to_string id)
      (term_e_to_string term)
  | PTuple terms ->
    Printf.sprintf "(%s)"
      (term_e_s_to_string terms)

and term_e_s_to_string ts : string =
  String.concat ", "
    (List.map term_e_to_string ts)

let envdecl_to_string envdecl =
  String.concat ", "
    (List.map (fun (id, ty) ->
         Printf.sprintf "%s : %s"
           (ident_to_string id)
           (ident_to_string ty)
       ) envdecl)

let may_fail_env_decl_to_string may_fail_env_decl =
  String.concat ", "
    (List.map (fun (id, ty, may_fail) ->
         let may_fail_str =
           if may_fail then
             " or fail"
           else
             ""
         in

         Printf.sprintf "%s : %s%s"
           (ident_to_string id)
           (ident_to_string ty)
           may_fail_str
       ) may_fail_env_decl)

let id_tys_to_string = envdecl_to_string

let id_tys_to_string_with_parens_if_not_empty id_tys =
  match id_tys with
  | [] -> ""
  | l -> Printf.sprintf "(%s)" (id_tys_to_string l)

let rec process_tproc ctx (p : tprocess) =
  let open Print_context in

  let push = Print_context.push ctx in
  let push_to_last_line = Print_context.push_to_last_line ctx in

  let set_struct_ty =
    Print_context.set_tproc_struct_ty ctx
  in
  (* let insert_blank_line_if_diff_struct_ty () =
   *   Print_context.insert_blank_line_if_diff_tproc_struct_ty ctx
   * in *)
  let insert_blank_line_anyway () =
    Print_context.insert_blank_line_anyway_tproc_struct_ty ctx
  in
  let incre_indent () =
    Print_context.incre_indent ctx
  in
  let decre_indent () =
    Print_context.decre_indent ctx
  in

  let rec aux p =
    match p with
    | PNil -> (
        set_struct_ty PNil_;
        (* insert_blank_line_if_diff_struct_ty (); *)
        push "0"
      )
    | PPar (p1, p2) -> (
        set_struct_ty PPar_;
        (* insert_blank_line_if_diff_struct_ty (); *)

        push "(";
        incre_indent ();
        aux p1;
        decre_indent ();
        push ")";
        push "| (";
        incre_indent ();
        aux p2;
        decre_indent ();
        push ")";
      )
    | PRepl p -> (
        set_struct_ty PRepl_;
        (* insert_blank_line_if_diff_struct_ty (); *)

        push "! (";
        incre_indent ();
        aux p;
        decre_indent ();
        push ")"
      )
    | PRestr (id, ids, ty, p) -> (
        set_struct_ty PRestr_;
        (* insert_blank_line_if_diff_struct_ty (); *)

        let ids = match ids with
          | None -> [id]
          | Some l -> id :: l
        in
        push (Printf.sprintf "new %s : %s;"
                (idents_to_string ids)
                (ident_to_string ty));
        aux p
      )
    | PLetDef (id, terms) -> (
        set_struct_ty PRestr_;
        (* insert_blank_line_if_diff_struct_ty (); *)

        push (Printf.sprintf "%s%s"
                (ident_to_string id)
                (match terms with
                 | [] -> ""
                 | l -> Printf.sprintf "(%s)"
                          (pterm_e_s_to_string terms)
                )
             )
      )
    | PTest (cond, true_branch, false_branch) -> (
        set_struct_ty PTest_;
        (* insert_blank_line_if_diff_struct_ty (); *)
        insert_blank_line_anyway ();

        push (Printf.sprintf "if %s then" (pterm_e_to_string cond));
        (match false_branch with
         | PNil ->
           aux true_branch;
         | _ ->
           push_to_last_line " (";
           incre_indent ();
           aux true_branch;
           decre_indent ();
           push ") else (";
           incre_indent ();
           aux false_branch;
           decre_indent ();
           push ")";
        )
      )
    | PInput (channel, pat, p) -> (
        set_struct_ty PInput_;
        (* insert_blank_line_if_diff_struct_ty (); *)

        push (Printf.sprintf "in(%s, %s);"
                (pterm_e_to_string channel)
                (tpattern_to_string pat));
        aux p;
      )
    | POutput (channel, term, p) -> (
        set_struct_ty POutput_;
        (* insert_blank_line_if_diff_struct_ty (); *)

        push (Printf.sprintf "out(%s, %s);"
                (pterm_e_to_string channel)
                (pterm_e_to_string term));
        aux p;
      )
    | PLet (pat, term, true_branch, false_branch) -> (
        set_struct_ty PLet_;
        (* insert_blank_line_if_diff_struct_ty (); *)

        push (Printf.sprintf "let %s = %s in"
                (let pat_str = tpattern_to_string pat in
                 match pat with
                 | PPatEqual _ -> Printf.sprintf "(%s)" pat_str
                 | _ -> pat_str)
                (pterm_e_to_string term));
        (match false_branch with
         | PNil ->
           aux true_branch
         | _ ->
           push_to_last_line " (";
           incre_indent ();
           aux true_branch;
           decre_indent ();
           push ") else (";
           incre_indent ();
           aux false_branch;
           decre_indent ();
           push ")"
        )
      )
    | PLetFilter (id_tys, term, true_branch, false_branch) -> (
        set_struct_ty PLetFilter_;
        (* insert_blank_line_if_diff_struct_ty (); *)

        push (Printf.sprintf "let %s such that %s in"
                (id_tys_to_string id_tys)
                (pterm_e_to_string term));
        (match false_branch with
         | PNil ->
           aux true_branch;
         | _ ->
           incre_indent ();
           aux true_branch;
           decre_indent ();
           push "else";
           incre_indent ();
           aux false_branch;
           decre_indent ();
        )
      )
    | PEvent (id, terms, ids, p) -> (
        set_struct_ty PEvent_;
        (* insert_blank_line_if_diff_struct_ty (); *)

        let term_str = match terms with
          | [] -> ""
          | l -> Printf.sprintf "(%s)" (pterm_e_s_to_string l)
        in

        push (Printf.sprintf "event %s%s;"
                (ident_to_string id)
                term_str);
        aux p;
      )
    | PPhase (num, p) -> (
        set_struct_ty PPhase_;
        (* insert_blank_line_if_diff_struct_ty (); *)

        push (Printf.sprintf "phase %d;"
                num);
        aux p;
      )
    | PBarrier (num, id, p) -> (
        set_struct_ty PBarrier_;
        (* insert_blank_line_if_diff_struct_ty (); *)

      )
    | PInsert (id, terms, p) -> (
        set_struct_ty PInsert_;
        (* insert_blank_line_if_diff_struct_ty (); *)

        push (Printf.sprintf "insert %s(%s);"
                (ident_to_string id)
                (String.concat ", " (List.map pterm_e_to_string terms)));
        aux p;
      )
    | PGet (id, pats, cond, true_branch, false_branch) -> (
        set_struct_ty PGet_;
        (* insert_blank_line_if_diff_struct_ty (); *)

        let cond_str = match cond with
          | None -> ""
          | Some c -> Printf.sprintf "such that %s " (pterm_e_to_string c)
        in

        push (Printf.sprintf "get %s(%s) %sin"
                (ident_to_string id)
                (tpatterns_to_string pats)
                cond_str);
        (match false_branch with
         | PNil ->
           aux true_branch;
         | _ ->
           push_to_last_line " (";
           incre_indent ();
           aux true_branch;
           decre_indent ();
           push ") else (";
           incre_indent ();
           aux false_branch;
           decre_indent ();
           push ")"
        )
      )
  in

  aux p

let idents_to_string_with_brackets_if_not_empty ?(prepend_space = true) ids =
  match ids with
  | [] -> ""
  | l -> (if prepend_space then " " else "") ^ Printf.sprintf "[%s]" (idents_to_string l)

let idents_to_string_with_parens_if_not_empty ids =
  match ids with
  | [] -> ""
  | l -> Printf.sprintf "(%s)" (idents_to_string l)

let rec gterm_e_to_string (t, _) =
  match t with
  | PGIdent id -> ident_to_string id
  | PGFunApp ((f, _), [l; r]) when f = "="
                                || f = "<>"
                                || f = "||"
                                || f = "&&"
                                || f = "==>" ->
    Printf.sprintf "%s %s %s"
      (gterm_e_to_string l)
      f
      (gterm_e_to_string r)
  | PGFunApp (f, args) ->
    Printf.sprintf "%s(%s)"
      (ident_to_string f)
      (gterm_e_s_to_string args)
  | PGPhase (f, args, num) ->
    Printf.sprintf "%s(%s) phase %d"
      (ident_to_string f)
      (gterm_e_s_to_string args)
      num
  | PGTuple terms ->
    Printf.sprintf "(%s)"
      (gterm_e_s_to_string terms)
  | PGName (id, bindings) ->
    Printf.sprintf "new %s%s"
      (ident_to_string id)
      (match bindings with
       | [] -> ""
       | l -> Printf.sprintf "[%s]"
                (String.concat "; "
                   (List.map (fun (id, term) ->
                        Printf.sprintf "%s = %s"
                          (ident_to_string id)
                          (gterm_e_to_string term)
                      ) l
                   )
                )
      )
  | PGLet (id, term, next) ->
    Printf.sprintf "let %s = %s in %s"
      (ident_to_string id)
      (gterm_e_to_string term)
      (gterm_e_to_string next)

and gterm_e_s_to_string ts =
  String.concat ", "
    (List.map gterm_e_to_string ts)

let tquery_to_string query =
  match query with
  | PPutBegin (injective, ids) ->
    Printf.sprintf "putbegin %s:%s"
      (if injective then "inj-event" else "event")
      (idents_to_string ids)
  | PRealQuery (term, public_vars) ->
    Printf.sprintf "%s%s"
      (gterm_e_to_string term)
      (match public_vars with
       | [] -> ""
       | l -> Printf.sprintf " public_vars %s" (idents_to_string l)
      )
  | PQSecret (id, public_vars, options) ->
    Printf.sprintf "secret %s%s%s"
      (ident_to_string id)
      (match public_vars with
       | [] -> ""
       | l -> Printf.sprintf " public_vars %s" (idents_to_string l)
      )
      (idents_to_string_with_brackets_if_not_empty options)

let nidecl_to_string (id, terms) =
  (ident_to_string id)
  ^
  (match terms with
   | None -> ""
   | Some l -> Printf.sprintf "among (%s)"
                 (term_e_s_to_string l)
  )

let nidecls_to_string nidecls =
  String.concat ", "
    (List.map nidecl_to_string nidecls)

let rec gformat_e_to_string (g, _) =
  match g with
  | PFGIdent id -> ident_to_string id
  | PFGFunApp (f, args) ->
    Printf.sprintf "%s(%s)"
      (ident_to_string f)
      (gformat_e_s_to_string args)
  | PFGTuple formats ->
    Printf.sprintf "(%s)"
      (gformat_e_s_to_string formats)
  | PFGName (id, bindings) ->
    Printf.sprintf "new %s%s"
      (ident_to_string id)
      (match bindings with
       | [] -> ""
       | l -> Printf.sprintf "[%s]"
                (String.concat ", "
                   (List.map gbinding_to_string l)
                   )
      )
  | PFGAny id ->
    Printf.sprintf "*%s"
      (ident_to_string id)
  | PFGLet (id, format, next) ->
    Printf.sprintf "let %s = %s in %s"
      (ident_to_string id)
      (gformat_e_to_string format)
      (gformat_e_to_string next)

and gformat_e_s_to_string gs =
  String.concat ", "
    (List.map gformat_e_to_string gs)

and gbinding_to_string (id, g) =
  Printf.sprintf "%s = %s"
    (ident_to_string id)
    (gformat_e_to_string g)

let rec nounifdecl_to_string nounifdecl =
  match nounifdecl with
  | BFLet (id, format, next) ->
    Printf.sprintf "let %s = %s in %s"
      (ident_to_string id)
      (gformat_e_to_string format)
      (nounifdecl_to_string next)
  | BFNoUnif ((id, formats, phase), denom) ->
    Printf.sprintf "%s(%s) phase %d / %d"
      (ident_to_string id)
      (gformat_e_s_to_string formats)
      phase
      denom

let tclause_to_string clause =
  match clause with
  | PClause (l, r) ->
    Printf.sprintf "%s -> %s"
      (term_e_to_string l)
      (term_e_to_string r)
  | PFact t ->
    Printf.sprintf "%s"
      (term_e_to_string t)
  | PEquiv (l, r, allow_replacements) ->
    Printf.sprintf "%s %s %s"
      (term_e_to_string l)
      (if allow_replacements then "<->" else "<=>")
      (term_e_to_string r)

let rec process_tdecl ctx decl =
  let open Print_context in

  let push = push ctx in
  let push_to_last_line = push_to_last_line ctx in

  let set_struct_ty =
    Print_context.set_tdecl_struct_ty ctx
  in
  let insert_blank_line_if_diff_struct_ty () =
    Print_context.insert_blank_line_if_diff_tdecl_struct_ty ctx
  in
  let insert_blank_line_anyway () =
    Print_context.insert_blank_line_anyway_tdecl_struct_ty ctx
  in
  let incre_indent () =
    Print_context.incre_indent ctx
  in
  let decre_indent () =
    Print_context.decre_indent ctx
  in

  let rec aux decl =
    match decl with
    | TTypeDecl id -> (
        set_struct_ty TTypeDecl_;
        insert_blank_line_if_diff_struct_ty ();

        push (Printf.sprintf "type %s."
                (ident_to_string id))
      )
    | TFunDecl (f, arg_tys, res_ty, options) -> (
        set_struct_ty TFunDecl_;
        insert_blank_line_if_diff_struct_ty ();

        push (Printf.sprintf "fun %s(%s) : %s%s."
                (ident_to_string f)
                (idents_to_string arg_tys)
                (ident_to_string res_ty)
                (idents_to_string_with_brackets_if_not_empty options));
      )
    | TEventDecl (id, arg_tys) -> (
        set_struct_ty TEventDecl_;
        insert_blank_line_if_diff_struct_ty ();

        push (Printf.sprintf "event %s%s."
                (ident_to_string id)
                (idents_to_string_with_parens_if_not_empty arg_tys));
      )
    | TConstDecl (id, ty, options) -> (
        set_struct_ty TConstDecl_;
        insert_blank_line_if_diff_struct_ty ();

        push (Printf.sprintf "const %s : %s%s."
                (ident_to_string id)
                (ident_to_string ty)
                (idents_to_string_with_brackets_if_not_empty options));
      )
    | TReduc (reducs, options) -> (
        set_struct_ty TReduc_;
        insert_blank_line_if_diff_struct_ty ();

        push "reduc";
        incre_indent ();
        list_iter_check_if_last (fun last (envdecl, l, r) ->
            push (
              (match envdecl with
               | [] -> ""
               | l -> Printf.sprintf "forall %s; "
                        (envdecl_to_string l);
              )
              ^
              (Printf.sprintf "%s = %s"
                 (term_e_to_string l)
                 (term_e_to_string r))
              ^
              (if last then
                 Printf.sprintf "%s." (idents_to_string_with_brackets_if_not_empty options)
               else
                 ";"
              )
            )
          ) reducs;
        decre_indent ();
      )
    | TReducFail (f, tys, res_ty, reducs, options) -> (
        set_struct_ty TReducFail_;
        insert_blank_line_if_diff_struct_ty ();

        push (Printf.sprintf "%s(%s) : %s"
                (ident_to_string f)
                (idents_to_string tys)
                (ident_to_string res_ty));
        push "reduc";
        incre_indent ();
        list_iter_check_if_last (fun last (may_fail_env_decl, l, r) ->
            push (
              (match may_fail_env_decl with
               | [] -> ""
               | l -> Printf.sprintf "forall %s; "
                        (may_fail_env_decl_to_string l);
              )
              ^
              (Printf.sprintf "%s = %s"
                 (term_e_to_string l)
                 (term_e_to_string r))
              ^
              (if last then
                 Printf.sprintf "%s." (idents_to_string_with_brackets_if_not_empty options)
               else
                 ";"
              )
            )
          ) reducs;
        decre_indent();
      )
    | TEquation (eqs, options) -> (
        set_struct_ty TEquation_;
        insert_blank_line_if_diff_struct_ty ();

        push "equation";
        incre_indent ();
        list_iter_check_if_last (fun last (envdecl, (term, _)) ->
            push (match envdecl with
                | [] -> ""
                | l -> Printf.sprintf "forall %s; "
                         (envdecl_to_string l)
              );
            incre_indent ();
            push (
              (match term with
               | PFunApp (("=", _), [l; r]) -> Printf.sprintf "%s = %s"
                                                 (term_e_to_string l)
                                                 (term_e_to_string r)
               | _ -> failwith "Unexpected pattern"
              )
              ^
              (if last then
                 Printf.sprintf "%s." (idents_to_string_with_brackets_if_not_empty options)
               else
                 ";"
              )
            );
            decre_indent ();
          ) eqs;
        decre_indent ();
      )
    | TPredDecl (id, arg_tys, options) -> (
        set_struct_ty TPredDecl_;
        insert_blank_line_if_diff_struct_ty ();

        push (Printf.sprintf "pred %s%s%s."
                (ident_to_string id)
                (idents_to_string_with_parens_if_not_empty arg_tys)
                (idents_to_string_with_brackets_if_not_empty options))
      )
    | TTableDecl (id, arg_tys) -> (
        set_struct_ty TTableDecl_;
        insert_blank_line_if_diff_struct_ty ();

        push (Printf.sprintf "table %s(%s)."
                (ident_to_string id)
                (idents_to_string arg_tys))
      )
    | TSet (id, pval) -> (
        set_struct_ty TSet_;
        insert_blank_line_if_diff_struct_ty ();

        push (Printf.sprintf "set %s = %s."
                (ident_to_string id)
                (pval_to_string pval))
      )
    | TPDef (id, args, p) -> (
        set_struct_ty TPDef_;
        insert_blank_line_anyway ();

        push (Printf.sprintf "let %s%s ="
                (ident_to_string id)
                (match args with
                 | [] -> ""
                 | l -> Printf.sprintf "(%s)"
                          (may_fail_env_decl_to_string args)
                )
             );
        incre_indent ();
        process_tproc ctx p;
        push_to_last_line ".";
        decre_indent ();
      )
    | TQuery (envdecl, queries) -> (
        set_struct_ty TQuery_;
        insert_blank_line_if_diff_struct_ty ();

        push (Printf.sprintf "query %s"
                (match envdecl with
                 | [] -> ""
                 | l -> Printf.sprintf "%s;"
                          (envdecl_to_string envdecl)
                )
             );
        incre_indent ();
        list_iter_check_if_last (fun last query ->
            push (
              (tquery_to_string query)
              ^
              (if last then "." else ";")
            )
          ) queries;
        decre_indent ();
      )
    | TNoninterf (envdecl, nidecls) -> (
        set_struct_ty TNoninterf_;
        insert_blank_line_if_diff_struct_ty ();

        push (Printf.sprintf "noninterf %s%s."
                (match envdecl with
                 | [] -> ""
                 | l -> Printf.sprintf "[%s]; " (envdecl_to_string l)
                )
                (nidecls_to_string nidecls)
             )
      )
    | TWeaksecret id -> (
        set_struct_ty TWeaksecret_;
        insert_blank_line_if_diff_struct_ty ();

        push (Printf.sprintf "weaksecret %s."
                (ident_to_string id))
      )
    | TNoUnif (envdecl, nounifdecl) -> (
        set_struct_ty TNoUnif_;
        insert_blank_line_if_diff_struct_ty ();

        push (Printf.sprintf "nounif %s%s."
                (match envdecl with
                 | [] -> ""
                 | l -> Printf.sprintf "%s;"
                          (envdecl_to_string l)
                )
                (nounifdecl_to_string nounifdecl)
             )
      )
    | TNot (envdecl, term) -> (
        set_struct_ty TNot_;
        insert_blank_line_if_diff_struct_ty ();

        push (Printf.sprintf "not %s%s."
                (match envdecl with
                 | [] -> ""
                 | l -> Printf.sprintf "%s;"
                          (envdecl_to_string envdecl)
                )
                (gterm_e_to_string term)
             )
      )
    | TElimtrue (may_fail_env_decl, term) -> (
        set_struct_ty TElimtrue_;
        insert_blank_line_if_diff_struct_ty ();

        push (Printf.sprintf "elimtrue %s%s"
                (match may_fail_env_decl with
                 | [] -> ""
                 | l -> Printf.sprintf "%s;"
                          (may_fail_env_decl_to_string l)
                )
                (term_e_to_string term)
             )
      )
    | TFree (id, ty, options) -> (
        set_struct_ty TFree_;
        insert_blank_line_if_diff_struct_ty ();

        push (Printf.sprintf "free %s : %s%s."
                (ident_to_string id)
                (ident_to_string ty)
                (idents_to_string_with_brackets_if_not_empty options)
             )
      )
    | TClauses clauses -> (
        set_struct_ty TClauses_;
        insert_blank_line_if_diff_struct_ty ();

        push "clauses";
        incre_indent ();
        list_iter_check_if_last (fun last (may_fail_env_decl, clause) ->
            push (Printf.sprintf "forall %s;"
                    (may_fail_env_decl_to_string may_fail_env_decl)
                 );
            incre_indent ();
            push (
              (tclause_to_string clause)
              ^
              (if last then "." else ";")
            );
            decre_indent ();
          ) clauses;
        decre_indent ();
      )
    | TDefine (id, tys, decls) -> (
        set_struct_ty TDefine_;
        insert_blank_line_if_diff_struct_ty ();

        push (Printf.sprintf "def %s(%s) {"
                (ident_to_string id)
                (idents_to_string tys)
             );
        incre_indent ();
        process_tdecls ctx decls;
        decre_indent ();
        push "}";
      )
    | TExpand (id, tys) -> (
        set_struct_ty TExpand_;
        insert_blank_line_if_diff_struct_ty ();

        push (Printf.sprintf "expand %s(%s)."
                (ident_to_string id)
                (idents_to_string tys)
             )
      )
    | TLetFun (f, may_fail_env_decl, term) -> (
        set_struct_ty TLetFun_;
        insert_blank_line_if_diff_struct_ty ();

        push (Printf.sprintf "letfun %s%s = %s."
                (ident_to_string f)
                (match may_fail_env_decl with
                 | [] -> ""
                 | l -> Printf.sprintf "(%s)"
                          (may_fail_env_decl_to_string may_fail_env_decl)
                )
                (pterm_e_to_string term)
             )
      )
  in

  aux decl

and process_tdecls ctx tdecls =
  List.iter (fun tdecl -> process_tdecl ctx tdecl) tdecls

let tdecls_to_string tdecls =
  let ctx = Print_context.make () in

  process_tdecls ctx tdecls;

  Print_context.finish ctx

let tproc_to_string_with_indent tproc =
  let ctx = Print_context.make () in

  Print_context.incre_indent ctx;

  process_tproc ctx tproc;

  Print_context.decre_indent ctx;

  Print_context.finish ctx
