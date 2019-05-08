open Graph
open Misc_utils

module Raw_expr = struct
  (* open Parser_components *)
  (* open MParser *)
  open Misc_utils
  open Printf
  open Expr_components

  type expr =
    | Variable of identifier
    | Function of string * expr list
    | UnaryOp of unary_op * expr
    | BinaryOp of binary_op * expr * expr
    | Quantified of quantifier * identifier list * expr
    | False
    | InsertedF of int list

  let rec expr_to_string (e : expr) : string =
    match e with
    | Variable ident -> ident
    | Function (name, params) ->
      sprintf "%s(%s)" name
        (join_with_comma (List.map expr_to_string params))
    | UnaryOp (op, expr) ->
      sprintf "%s%s" (unary_op_to_string op)
        ( match expr with
          | Variable _ as e -> expr_to_string e
          | Function _ as e -> expr_to_string e
          | UnaryOp _ as e -> expr_to_string e
          | _ as e -> sprintf "(%s)" (expr_to_string e) )
    | BinaryOp (op, l, r) ->
      sprintf "%s %s %s"
        ( match l with
          | Variable _ as e -> expr_to_string e
          | Function _ as e -> expr_to_string e
          | UnaryOp _ as e -> expr_to_string e
          | _ as e -> sprintf "(%s)" (expr_to_string e) )
        (binary_op_to_string op)
        ( match r with
          | Variable _ as e -> expr_to_string e
          | Function _ as e -> expr_to_string e
          | UnaryOp _ as e -> expr_to_string e
          | _ as e -> sprintf "(%s)" (expr_to_string e) )
    | Quantified (q, idents, e) ->
      sprintf "%s [%s] : %s" (quantifier_to_string q)
        (join_with_comma idents) (expr_to_string e)
    | False -> "$false"
    | InsertedF l -> String.concat "" (List.map string_of_int l)

  let rec of_tptp_fof_formula (f : Tptp_ast.fof_formula) =
    let open Tptp_ast in
    let rec aux f =
      match f with
      | FOF_F_binary (b_op, l, r) -> BinaryOp (b_op, aux l, aux r)
      | FOF_F_unary (u_op, f) -> UnaryOp (u_op, aux f)
      | FOF_F_quantified (q, vars, f) -> Quantified (q, vars, aux f)
      | FOF_F_atomic t -> of_tptp_fof_term t
    in
    aux f

  and of_tptp_fof_term (t : Tptp_ast.fof_term) =
    let open Tptp_ast in
    let rec aux t =
      match t with
      | FOF_T_var "$false" -> False
      | FOF_T_var v -> Variable v
      | FOF_T_const "$false" -> False
      | FOF_T_const c -> Variable c
      | FOF_T_fun_app (f, args) -> Function (f, List.map aux args)
    in
    aux t

  (* module Parser : sig
   * 
   *   val expr_p : expr stateless_p
   * 
   * end = struct
   *   let parens (p : expr stateless_p) : expr stateless_p =
   *     skip_char '(' >> p >>= (fun x -> skip_char ')' >> return x)
   * 
   *   let prefix (sym : string) (op : unary_op) : (expr, unit) operator =
   *     Prefix (attempt (spaces >> skip_string sym >> spaces >> return (fun x -> UnaryOp (op, x))))
   * 
   *   let infix (sym : string) (op : binary_op) : (expr, unit) operator =
   *     Infix (attempt (spaces >> skip_string sym >> spaces >> return (fun a b -> BinaryOp (op, a, b))),
   *            Assoc_left)
   * 
   *   let operators =
   *     [
   *       [prefix "~"  Not];
   *       [infix  "&"  And];
   *       [infix  "|"  Or];
   *       [infix  "=>" Impl; infix "<=>" Iff];
   *       [infix  "="  Eq];
   *       [infix  "!=" Neq];
   *       [infix  "<-" Subsume];
   *     ]
   * 
   *   let false_p =
   *     ignore_space (string "$false" >> return False)
   * 
   *   let solver_inserted_p =
   *     (ignore_space (char '{' >>
   *                    sep_by (ignore_space (many1_chars digit)) (char ',') >>=
   *                    (fun l -> char '}' >> return (InsertedF (List.map int_of_string l))))) <|>
   *     (ignore_space (many1_chars digit >>=
   *                    (fun x -> return (InsertedF ([int_of_string x])))))
   * 
   *   let rec
   *     atom_p s = (ignore_space
   *                   (ident_p >>= (fun ident -> return (Variable ident)))) s
   *   and
   *     func_p s = (ignore_space
   *                   (ident_p >>= (fun ident -> char '(' >>
   *                                  sep_by1 expr_p (char ',') >>=
   *                                  (fun params -> char ')' >>
   *                                    return (Function (ident, params)))))) s
   *   and
   *     quant_p s = (choice [char '!' >> return Forall;
   *                          char '?' >> return Exists;] >>=
   *                  (fun quantifier ->
   *                     spaces >> char '[' >>
   *                     sep_by ident_p (char ',') >>=
   *                     (fun idents ->
   *                        char ']' >> spaces >> char ':' >> spaces >>
   *                        expr_p >>=
   *                        (fun expr ->
   *                           return (Quantified (quantifier, idents, expr)))))) s
   *   and
   *     sub_expr_p s = choice [attempt quant_p;
   *                            attempt func_p;
   *                            attempt (parens expr_p);
   *                            attempt atom_p;
   *                            attempt false_p;
   *                            attempt solver_inserted_p;
   *                           ] s
   *   and
   *     expr_p s     = expression operators sub_expr_p s
   * end *)
end

module Raw_line = struct
  (* open MParser *)
  (* open Parser_components *)
  open Printf

  type line = string * Raw_expr.expr * string * string list

  (* let node_no : int stateless_p =
   *   many1_chars digit |>> int_of_string >>=
   *   (fun x -> char '.' >> return x)
   * 
   * let non_digit_p =
   *   many_chars (letter <|> space)
   * 
   * let int_p =
   *   many1_chars digit |>> int_of_string
   * 
   * let parent_brack : (string * int list) stateless_p =
   *   spaces >> char '[' >> non_digit_p >>=
   *   (fun descr ->
   *      sep_by int_p (char ',') >>=
   *      (fun x ->
   *         char ']' >> return (Core_kernel.String.strip descr, x)
   *      )
   *   )
   * 
   * let line_p : line option stateless_p =
   *   choice [attempt (node_no >>=
   *                    (fun node_no ->
   *                       spaces >> Raw_expr.Parser.expr_p >>=
   *                       (fun expr ->
   *                          spaces >> parent_brack >>=
   *                          (fun (descr, parent_no_s) ->
   *                             many newline >>
   *                             return (Some (node_no, expr, descr, parent_no_s))
   *                          )
   *                       )
   *                    ));
   *           attempt (newline >> return None);
   *           attempt (spaces >> newline >> return None);
   *           attempt (char '%' >> many_until any_char newline >> return None);
   *           attempt (string "//" >> many_until any_char newline >> return None);
   *           attempt (string "----" >> many_until any_char eof >> return None);
   *          ] *)

  let line_to_string (line : line option) : string =
    match line with
    | None -> "Blank line"
    | Some (node_no, expr, derive_descr, parent_no_s) ->
      sprintf "%s. %s (%s) [%s]" node_no
        (Raw_expr.expr_to_string expr)
        derive_descr
        (Misc_utils.join_with_comma parent_no_s)

  let rec of_tptp_decl (decl : Tptp_ast.decl) =
    let open Tptp_ast in
    let aux decl =
      match decl with
      | Include _ -> None
      | Annotated_formula (Fof_annotated f) ->
        let {name; formula; annotations; _} = f in
        let descr, parent_ids =
          match annotations_to_descr_parent_ids annotations with
          | None -> ("", [])
          | Some p -> p
        in
        Some (name, Raw_expr.of_tptp_fof_formula formula, descr, parent_ids)
    in
    aux decl

  and annotations_to_descr_parent_ids ann =
    match ann with
    | None -> None
    | Some t -> collect_descr_parent_ids_from_general_term t

  and collect_descr_parent_ids_from_general_term t =
    let open Tptp_ast in
    match t with
    | GT_single d -> collect_descr_parent_ids_from_general_data d
    | _ -> None

  and collect_descr_parent_ids_from_general_data d =
    let open Tptp_ast in
    match d with
    | GD_fun ("inference", [GT_single (GD_word descr); _; GT_list parents]) ->
      Js_utils.console_log descr;
      let parents =
        parents
        |> List.fold_left
          (fun acc p ->
             match p with GT_single (GD_word s) -> s :: acc | _ -> acc )
          []
        |> List.rev
      in
      Some (descr, parents)
    | _ -> None
end

(* module File_parser = struct
 *   open MParser
 * 
 *   let refutation_proof_p =
 *     many Raw_line.line_p >>=
 *     (fun x ->
 *        eof >> return x
 *     )
 * 
 *   let parse_refutation_proof_channel (ic : in_channel) : Raw_line.line option list MParser.result =
 *     parse_channel refutation_proof_p ic ()
 * 
 *   let parse_refutation_proof_string (input : string) : Raw_line.line option list MParser.result =
 *     parse_string refutation_proof_p input ()
 * end *)

module File_parser = struct
  let parse_refutation_proof_string (input : string) :
    (Raw_line.line option list, string) result =
    let lexbuf = Lexing.from_string input in
    match Tptp.parse_with_error lexbuf with
    | Ok l -> Ok (List.map (fun x -> Raw_line.of_tptp_decl x) l)
    | Error msg -> Error msg
end

module Analyzed_expr = struct
  open Expr_components
  open Printf
  open Misc_utils

  type variable = boundedness * identifier

  type expr =
    | Variable of variable
    | Function of string * expr list
    | UnaryOp of unary_op * expr
    | BinaryOp of binary_op * expr * expr
    | Quantified of quantifier * identifier list * expr
    | False
    | InsertedF of int list

  type context =
    { quantifier : quantifier
    ; quantified_idents : identifier list }

  type variable_map_error =
    | Unexpected_unsure_var
    | Unexpected_universal_var
    | Unexpected_existential_var
    | Unmatching_free_var
    | Unmatching_structure

  exception Unexpected_unsure_var

  exception Unexpected_universal_var

  exception Unexpected_existential_var

  exception Unexpected_exists_quantifier

  exception Unmatching_free_var

  exception Unmatching_structure

  type pattern_match_direction =
    | Unidirectional
    | Bidirectional

  module ExprMap = Map.Make (struct
      type t = expr

      let compare = compare
    end)

  module ExprSet = Set.Make (struct
      type t = expr

      let compare = compare
    end)

  module VarMap = Map.Make (struct
      type t = identifier

      let compare = compare
    end)

  let is_quantified (ctx : context list) (e : identifier) : quantifier option =
    let rec aux (ctx : context list) (e : identifier) : quantifier option =
      match ctx with
      | [] -> None
      | x :: xs ->
        if List.mem e x.quantified_idents then Some x.quantifier
        else aux xs e
    in
    aux ctx e

  let raw_expr_to_analyzed_expr (raw : Raw_expr.expr) : expr =
    let rec aux (ctx : context list) (raw : Raw_expr.expr) : expr =
      match raw with
      | Variable ident -> (
          match is_quantified ctx ident with
          | None -> Variable (Unsure, ident)
          | Some `Exists -> Variable (Existential, ident)
          | Some `Forall -> Variable (Universal, ident) )
      | Function (name, params) -> Function (name, List.map (aux ctx) params)
      | UnaryOp (op, e) -> UnaryOp (op, aux ctx e)
      | BinaryOp (op, l, r) -> BinaryOp (op, aux ctx l, aux ctx r)
      | Quantified (q, idents, e) ->
        let new_ctx = {quantifier = q; quantified_idents = idents} in
        Quantified (q, idents, aux (new_ctx :: ctx) e)
      | False -> False
      | InsertedF formulas -> InsertedF formulas
    in
    aux [] raw

  let rec expr_to_string_debug (e : expr) : string =
    match e with
    | Variable (Free, x) -> sprintf "%s[free]" x
    | Variable (Universal, x) -> sprintf "%s[U]" x
    | Variable (Existential, x) -> sprintf "%s[E]" x
    | Variable (Unsure, x) -> sprintf "%s[unsure]" x
    | Function (name, params) ->
      sprintf "%s(%s)" name
        (join_with_comma (List.map expr_to_string_debug params))
    | UnaryOp (op, expr) ->
      sprintf "%s(%s)" (unary_op_to_string op) (expr_to_string_debug expr)
    | BinaryOp (op, l, r) ->
      sprintf "(%s) %s (%s)" (expr_to_string_debug l)
        (binary_op_to_string op) (expr_to_string_debug r)
    | Quantified (q, idents, e) ->
      sprintf "%s [%s] : %s" (quantifier_to_string q)
        (join_with_comma idents) (expr_to_string_debug e)
    | False -> "$false"
    | InsertedF l -> String.concat "" (List.map string_of_int l)

  let rec expr_to_string (e : expr) : string =
    match e with
    | Variable (Free, x) -> sprintf "%s" x
    | Variable (Universal, x) -> sprintf "%s" x
    | Variable (Existential, x) -> sprintf "%s" x
    | Variable (Unsure, x) -> sprintf "%s" x
    | Function (name, params) ->
      sprintf "%s(%s)" name
        (join_with_comma (List.map expr_to_string params))
    | UnaryOp (op, expr) ->
      sprintf "%s%s" (unary_op_to_string op)
        ( match expr with
          | Variable _ as e -> expr_to_string e
          | Function _ as e -> expr_to_string e
          | UnaryOp _ as e -> expr_to_string e
          | _ as e -> sprintf "(%s)" (expr_to_string e) )
    | BinaryOp (op, l, r) -> (
        match op with
        | And | Or | Imply | Left_imply | Not_or | Not_and ->
          sprintf "%s %s %s"
            ( match l with
              | Variable _ as e -> expr_to_string e
              | Function _ as e -> expr_to_string e
              | UnaryOp _ as e -> expr_to_string e
              | _ as e -> sprintf "(%s)" (expr_to_string e) )
            (binary_op_to_string op)
            ( match r with
              | Variable _ as e -> expr_to_string e
              | Function _ as e -> expr_to_string e
              | UnaryOp _ as e -> expr_to_string e
              | _ as e -> sprintf "(%s)" (expr_to_string e) )
        | Eq | Iff | Xor ->
          sprintf "%s %s %s" (expr_to_string l) (binary_op_to_string op)
            (expr_to_string r) )
    | Quantified (q, idents, e) ->
      sprintf "%s [%s] : %s" (quantifier_to_string q)
        (join_with_comma idents) (expr_to_string e)
    | False -> "$false"
    | InsertedF l -> String.concat "" (List.map string_of_int l)

  let get_boundedness (e : expr) : (string * boundedness) list =
    let rec aux (e : expr) acc : (string * boundedness) list =
      match e with
      | Variable (b, v) -> (v, b) :: acc
      | Function (_, params) -> List.fold_left (fun x y -> aux y x) acc params
      | UnaryOp (_, e) -> aux e acc
      | BinaryOp (_, l, r) -> aux l (aux r acc)
      | Quantified (_, _, e) -> aux e acc
      | False -> acc
      | InsertedF _ -> acc
    in
    aux e []

  let mark_if_unsure (bound : boundedness) (e : expr) : expr =
    let rec aux (e : expr) : expr =
      match e with
      | Variable (Unsure, v) -> Variable (bound, v)
      | Variable (Free, v) -> Variable (Free, v)
      | Variable (Universal, v) -> Variable (Universal, v)
      | Variable (Existential, v) -> Variable (Existential, v)
      | Function (name, params) -> Function (name, List.map aux params)
      | UnaryOp (op, e) -> UnaryOp (op, aux e)
      | BinaryOp (op, l, r) -> BinaryOp (op, aux l, aux r)
      | Quantified (q, idents, e) -> Quantified (q, idents, aux e)
      | False -> False
      | InsertedF formulas -> InsertedF formulas
    in
    aux e

  let update_boundedness (e : expr) (changes : (string * boundedness) list) :
    expr =
    let rec aux (e : expr) : expr =
      match e with
      | Variable (b, v) -> (
          match List.assoc_opt v changes with
          | None -> Variable (b, v)
          | Some new_b -> (
              match (new_b, b) with
              | x, Unsure -> Variable (x, v)
              | _, _h -> Variable (b, v) (* only update when unsure *) ) )
      | Function (name, params) -> Function (name, List.map aux params)
      | UnaryOp (op, e) -> UnaryOp (op, aux e)
      | BinaryOp (op, l, r) -> BinaryOp (op, aux l, aux r)
      | Quantified (q, idents, e) -> Quantified (q, idents, aux e)
      | False -> False
      | InsertedF formulas -> InsertedF formulas
    in
    aux e

  let get_function_names (e : expr) : string list =
    let rec aux (e : expr) : string list =
      match e with
      | Variable _ -> []
      | Function (name, params) -> name :: List.concat (List.map aux params)
      | UnaryOp (_, e) -> aux e
      | BinaryOp (_, e1, e2) -> List.append (aux e1) (aux e2)
      | Quantified (_, _, e) -> aux e
      | False -> []
      | InsertedF _ -> []
    in
    List.sort_uniq compare (aux e)

  let get_vars ?(boundedness : boundedness option) (e : expr) : string list =
    let rec aux (e : expr) : string list =
      match e with
      | Variable (b, name) -> (
          match boundedness with
          | Some boundedness -> if b = boundedness then [name] else []
          | None -> [name] )
      | Function (name, params) -> name :: List.concat (List.map aux params)
      | UnaryOp (_, e) -> aux e
      | BinaryOp (_, e1, e2) -> List.append (aux e1) (aux e2)
      | Quantified (_, _, e) -> aux e
      | False -> []
      | InsertedF _ -> []
    in
    List.sort_uniq compare (aux e)

  let pattern_matches ~(pattern : expr) (expr : expr) : bool =
    let rec aux (pattern : expr) (expr : expr) : bool =
      match (pattern, expr) with
      | Variable (Unsure, _), _ -> raise Unexpected_unsure_var
      | _, Variable (Unsure, _) -> raise Unexpected_unsure_var
      | Variable (Existential, _), _ -> raise Unexpected_existential_var
      | _, Variable (Existential, _) -> raise Unexpected_existential_var
      | Quantified (`Exists, _, _), _ -> raise Unexpected_exists_quantifier
      | _, Quantified (`Exists, _, _) -> raise Unexpected_exists_quantifier
      | (Variable (Free, _) as v1), (Variable (Free, _) as v2) ->
        if v1 = v2 then true else false
      | Variable (Universal, _), _ -> true
      | Function (f1, es1), Function (f2, es2) ->
        if f1 = f2 && List.length es1 = List.length es2 then aux_list es1 es2
        else false
      | UnaryOp (op1, e1), UnaryOp (op2, e2) ->
        if op1 = op2 then aux e1 e2 else false
      | BinaryOp (op1, e1a, e1b), BinaryOp (op2, e2a, e2b) ->
        if op1 = op2 then aux e1a e2a && aux e1b e2b else false
      | Quantified (`Forall, _, e1), Quantified (`Forall, _, e2) -> aux e1 e2
      | Quantified (`Forall, _, e1), (_ as e2) -> aux e1 e2
      | False, False -> true
      | InsertedF l1, InsertedF l2 -> l1 = l2
      | _ -> false
    and aux_list (es1 : expr list) (es2 : expr list) : bool =
      List.length es1 = List.length es2
      && List.fold_left2 (fun res e1 e2 -> res && aux e1 e2) true es1 es2
    in
    aux pattern expr

  let pattern_search ?(s : ExprSet.t = ExprSet.empty) ~(pattern : expr)
      (expr : expr) : expr list =
    let rec aux (pattern : expr) (expr : expr) (s : ExprSet.t) : ExprSet.t =
      let s =
        if pattern_matches ~pattern expr then ExprSet.add expr s else s
      in
      match expr with
      | Variable _ -> s
      | Function (_, es) -> aux_list pattern es s
      | UnaryOp (_, e) -> aux pattern e s
      | BinaryOp (_, e1, e2) -> aux_list pattern [e1; e2] s
      | Quantified (_, _, e) -> aux pattern e s
      | False -> s
      | InsertedF _ -> s
    and aux_list (pattern : expr) (es : expr list) (s : ExprSet.t) : ExprSet.t
      =
      List.fold_left (fun s e -> aux pattern e s) s es
    in
    ExprSet.elements (aux pattern expr s)

  let var_bindings_in_pattern_match ?(m : expr VarMap.t = VarMap.empty)
      ~(pattern : expr) (expr : expr) : expr VarMap.t =
    let rec aux (pattern : expr) (expr : expr) (m : expr VarMap.t) :
      expr VarMap.t =
      match (pattern, expr) with
      | Variable (Free, _), _ -> m
      | Variable (Universal, name), (_ as v) -> VarMap.add name v m
      | Variable (Existential, _), _ -> raise Unexpected_existential_var
      | Function (_, es1), Function (_, es2) -> aux_list es1 es2 m
      | UnaryOp (_, e1), UnaryOp (_, e2) -> aux e1 e2 m
      | BinaryOp (_, e1a, e1b), BinaryOp (_, e2a, e2b) ->
        aux_list [e1a; e1b] [e2a; e2b] m
      | Quantified (_, _, e1), Quantified (_, _, e2) -> aux e1 e2 m
      | False, False -> m
      | InsertedF _, InsertedF _ -> m
      | _ -> raise Unmatching_structure
    and aux_list (es1 : expr list) (es2 : expr list) (m : expr VarMap.t) :
      expr VarMap.t =
      List.fold_left2 (fun m e1 e2 -> aux e1 e2 m) m es1 es2
    in
    if pattern_matches ~pattern expr then aux pattern expr m else m

  let var_bindings_compatible ~(smaller : expr VarMap.t)
      ~(larger : expr VarMap.t) : bool =
    let keys = List.map (fun (k, _) -> k) (VarMap.bindings smaller) in
    List.fold_left
      (fun res k ->
         res
         &&
         match VarMap.find_opt k larger with
         | None -> true
         | Some c -> VarMap.find k smaller = c )
      true keys

  let fill_in_pattern ~(pattern : expr) (var_bindings : expr VarMap.t) : expr =
    let rec aux (pattern : expr) (var_bindings : expr VarMap.t) : expr =
      match pattern with
      | Variable (Unsure, _) -> raise Unexpected_unsure_var
      | Variable (Free, _) as e -> e
      | Variable (Existential, _) -> raise Unexpected_existential_var
      | Variable (Universal, name) -> VarMap.find name var_bindings
      | Function (name, es1) -> Function (name, aux_list es1 var_bindings)
      | UnaryOp (op, e) -> UnaryOp (op, aux e var_bindings)
      | BinaryOp (op, e1, e2) ->
        BinaryOp (op, aux e1 var_bindings, aux e2 var_bindings)
      | Quantified (q, ids, e) -> Quantified (q, ids, aux e var_bindings)
      | False as e -> e
      | InsertedF _ as e -> e
    and aux_list (patterns : expr list) (var_bindings : expr VarMap.t) :
      expr list =
      List.map (fun e -> aux e var_bindings) patterns
    in
    aux pattern var_bindings

  let has_universal_var (e : expr) : bool =
    let rec aux (e : expr) : bool =
      match e with
      | Variable (Unsure, _) -> raise Unexpected_unsure_var
      | Variable (Free, _) -> false
      | Variable (Existential, _) -> false
      | Variable (Universal, _) -> true
      | Function (_, es) -> aux_list es
      | UnaryOp (_, e) -> aux e
      | BinaryOp (_, e1, e2) -> aux e1 || aux e2
      | Quantified (_, _, e) -> aux e
      | False -> false
      | InsertedF _ -> false
    and aux_list (es : expr list) : bool =
      List.fold_left (fun res e -> res || aux e) false es
    in
    aux e

  let negate (e : expr) : expr =
    let rec aux (e : expr) : expr =
      match e with
      | UnaryOp (Not, e) -> e
      | Variable _ -> UnaryOp (Not, e)
      | Function _ -> UnaryOp (Not, e)
      | BinaryOp (And, e1, e2) -> BinaryOp (Or, aux e1, aux e2)
      | BinaryOp (Or, e1, e2) -> BinaryOp (And, aux e1, aux e2)
      | BinaryOp (Eq, _, _) -> UnaryOp (Not, e)
      | BinaryOp (Iff, e1, e2) -> BinaryOp (Xor, e1, e2)
      | BinaryOp (Imply, e1, e2) -> BinaryOp (And, e1, aux e2)
      | BinaryOp (Left_imply, e1, e2) -> BinaryOp (And, aux e1, e2)
      | BinaryOp (Xor, e1, e2) -> BinaryOp (Iff, e1, e2)
      | BinaryOp (Not_or, e1, e2) -> BinaryOp (Or, e1, e2)
      | BinaryOp (Not_and, e1, e2) -> BinaryOp (And, e1, e2)
      | Quantified (`Forall, vars, e) -> Quantified (`Exists, vars, aux e)
      | Quantified (`Exists, vars, e) -> Quantified (`Forall, vars, aux e)
      | False -> UnaryOp (Not, False)
      | InsertedF _ -> UnaryOp (Not, e)
    in
    aux e

  let strip_pred_attacker (e : expr) : expr =
    match e with Function ("attacker", [e]) -> e | _ -> e

  let strip_not (e : expr) : expr =
    match e with UnaryOp (Not, e) -> e | _ as e -> e

  let strip_att (e : expr) : expr =
    match e with Function ("attacker", [e]) -> e | _ as e -> e

  let strip_quant (e : expr) : expr =
    match e with Quantified (_, _, e) -> e | _ -> e

  let get_function_args (e : expr) : expr list =
    match e with Function (_, es) -> es | _ -> []

  (* let unwrap_subsume (e : expr) : expr =
   *   match e with
   *   | BinaryOp (Subsume, e, _) -> e
   *   | _                   as e -> e *)

  let remove_subsumptions (e : expr) : expr =
    let rec aux (e : expr) : expr =
      match e with
      | Variable _ -> e
      | Function (f, args) -> Function (f, List.map aux args)
      | UnaryOp (op, e) -> UnaryOp (op, aux e)
      | BinaryOp (Or, e, UnaryOp (Not, Variable (_, v)))
        when has_prefix v "spl" ->
        e
      | BinaryOp (Or, UnaryOp (Not, Variable (_, v)), e)
        when has_prefix v "spl" ->
        e
      | BinaryOp (op, e1, e2) -> BinaryOp (op, aux e1, aux e2)
      | Quantified (q, vars, e) -> Quantified (q, vars, aux e)
      | False -> e
      | InsertedF _ -> e
    in
    aux e

  let split_on_and (e : expr) : expr list =
    let rec aux (e : expr) : expr list =
      match e with BinaryOp (And, e1, e2) -> aux e1 @ aux e2 | _ as e -> [e]
    in
    aux e

  let split_on_or (e : expr) : expr list =
    let rec aux (e : expr) : expr list =
      match e with BinaryOp (Or, e1, e2) -> aux e1 @ aux e2 | _ as e -> [e]
    in
    aux e

  let split_on_impl (e : expr) : (expr * expr) option =
    match e with BinaryOp (Imply, e1, e2) -> Some (e1, e2) | _ -> None

  let length (e : expr) : int =
    let rec aux (acc : int) (e : expr) : int =
      let acc = acc + 1 in
      match e with
      | Variable _ -> acc
      | Function (_, es) -> aux_list acc es
      | UnaryOp (_, e) -> aux acc e
      | BinaryOp (_, e1, e2) -> aux_list acc [e1; e2]
      | Quantified (_, _, e) -> aux acc e
      | False -> acc
      | InsertedF _ -> acc
    and aux_list (acc : int) (es : expr list) : int =
      List.fold_left (fun acc e -> aux acc e) acc es
    in
    aux 0 e

  let rewrite (base : expr) ~(rewrite_rule_from : expr)
      ~(rewrite_rule_to : expr) ~(expr_from : expr) : expr =
    let rec aux (base : expr) (expr_from : expr) (to_expr : expr) : expr =
      if base = expr_from then to_expr
      else
        match base with
        | Variable _ as e -> e
        | Function (name, es) -> Function (name, aux_list es expr_from to_expr)
        | UnaryOp (op, e) -> UnaryOp (op, aux e expr_from to_expr)
        | BinaryOp (op, e1, e2) ->
          BinaryOp (op, aux e1 expr_from to_expr, aux e2 expr_from to_expr)
        | Quantified (q, ids, e) -> Quantified (q, ids, aux e expr_from to_expr)
        | False as e -> e
        | InsertedF _ as e -> e
    and aux_list (bases : expr list) (expr_from : expr) (to_expr : expr) :
      expr list =
      List.map (fun e -> aux e expr_from to_expr) bases
    in
    let var_bindings =
      var_bindings_in_pattern_match ~pattern:rewrite_rule_from expr_from
    in
    let to_expr = fill_in_pattern ~pattern:rewrite_rule_to var_bindings in
    aux base expr_from to_expr

  let similarity (e1 : expr) (e2 : expr) : float =
    let rec aux (e1 : expr) (e2 : expr) : int =
      match (e1, e2) with
      | Variable (Free, n1), Variable (Free, n2) -> if n1 = n2 then 2 else 0
      | Variable (Universal, _), (_ as v) -> 1 + length v
      | (_ as v), Variable (Universal, _) -> 1 + length v
      | Variable (Existential, _), _ -> raise Unexpected_existential_var
      | _, Variable (Existential, _) -> raise Unexpected_existential_var
      | Function (n1, es1), Function (n2, es2) ->
        if n1 = n2 then 2 + aux_list es1 es2 else 0
      | UnaryOp (op1, e1), UnaryOp (op2, e2) ->
        if op1 = op2 then 2 + aux e1 e2 else 0
      | BinaryOp (op1, e1a, e1b), BinaryOp (op2, e2a, e2b) ->
        if op1 = op2 then 2 + aux_list [e1a; e1b] [e2a; e2b] else 0
      | Quantified (_, _, e1), Quantified (_, _, e2) -> aux e1 e2
      | False, False -> 2
      | InsertedF n1, InsertedF n2 -> if n1 = n2 then 2 else 0
      | _ -> 0
    and aux_list (es1 : expr list) (es2 : expr list) : int =
      List.fold_left2 (fun acc e1 e2 -> acc + aux e1 e2) 0 es1 es2
    in
    let total_matches = aux e1 e2 in
    float_of_int total_matches /. float_of_int (length e1 + length e2)

  let pattern_multi_match_map (exprs1 : expr list) (exprs2 : expr list) :
    expr ExprMap.t option =
    let all_combinations (exprs1 : expr list) (exprs2 : expr list) :
      (expr * expr) list =
      let rec aux (acc : (expr * expr) list) (exprs1 : expr list)
          (exprs : expr list) : (expr * expr) list =
        match exprs1 with
        | [] -> acc
        | p :: ps ->
          let acc = List.map (fun e -> (p, e)) exprs @ acc in
          aux acc ps exprs
      in
      aux [] exprs1 exprs2
    in
    (* let filter_by_pattern_matches (combinations : (expr * expr) list) : (expr * expr) list =
     *   let rec aux (acc : (expr * expr) list) (combinations : (expr * expr) list) : (expr * expr) list =
     *     match combinations with
     *     | []             -> acc
     *     | (e1, e2) :: cs ->
     *       let acc =
     *         if pattern_matches ~pattern:e1 e2 then (e1, e2) :: acc
     *         else                                               acc
     *       in
     *       aux acc cs
     *   in
     *   aux [] combinations
     * in *)
    let group_by_exprs (combinations : (expr * expr) list) :
      expr list ExprMap.t =
      let rec aux (m : expr list ExprMap.t) (combinations : (expr * expr) list)
        : expr list ExprMap.t =
        match combinations with
        | [] -> m
        | (p, e) :: cs ->
          let m =
            match ExprMap.find_opt p m with
            | None -> ExprMap.add p [e] m
            | Some l -> ExprMap.add p (e :: l) m
          in
          aux m cs
      in
      aux ExprMap.empty combinations
    in
    let generate_possible_solutions (m : expr list ExprMap.t) :
      expr ExprMap.t list =
      let rec aux (keys : expr list) (m : expr list ExprMap.t)
          (cur : expr ExprMap.t) : expr ExprMap.t list =
        match keys with
        | [] -> [cur]
        | k :: ks ->
          let vals = ExprMap.find k m in
          List.concat
            (List.map
               (fun v ->
                  let cur = ExprMap.add k v cur in
                  aux ks m cur )
               vals)
      in
      let keys = List.map (fun (k, _) -> k) (ExprMap.bindings m) in
      aux keys m ExprMap.empty
    in
    let filter_by_non_overlapping_exprs_expressions (l : expr ExprMap.t list) :
      expr ExprMap.t list =
      let no_overlaps (m : expr ExprMap.t) : bool =
        let rec aux (keys : expr list) (m : expr ExprMap.t)
            (exprs1_used : ExprSet.t) (exprs2_used : ExprSet.t) : bool =
          match keys with
          | [] -> true
          | pat :: ks ->
            let expr = ExprMap.find pat m in
            let pattern_no_overlap = not (ExprSet.mem pat exprs1_used) in
            let expr_no_overlap = not (ExprSet.mem expr exprs2_used) in
            let no_overlaps = pattern_no_overlap && expr_no_overlap in
            if no_overlaps then
              aux ks m
                (ExprSet.add pat exprs1_used)
                (ExprSet.add expr exprs2_used)
            else false
        in
        let keys = List.map (fun (k, _) -> k) (ExprMap.bindings m) in
        aux keys m ExprSet.empty ExprSet.empty
      in
      List.filter (fun m -> no_overlaps m) l
    in
    let filter_by_compatible_var_bindings (solutions : expr ExprMap.t list) :
      expr ExprMap.t list =
      let no_overlaps (m : expr ExprMap.t) : bool =
        let rec aux (keys : expr list) (var_bindings : expr VarMap.t)
            (m : expr ExprMap.t) : bool =
          match keys with
          | [] -> true
          | pat :: ks ->
            let expr = ExprMap.find pat m in
            let bindings = var_bindings_in_pattern_match ~pattern:pat expr in
            if var_bindings_compatible ~smaller:bindings ~larger:var_bindings
            then
              let var_bindings =
                var_bindings_in_pattern_match ~m:var_bindings ~pattern:pat
                  expr
              in
              aux ks var_bindings m
            else false
        in
        let keys = List.map (fun (k, _) -> k) (ExprMap.bindings m) in
        aux keys VarMap.empty m
      in
      List.filter (fun m -> no_overlaps m) solutions
    in
    let solution_score (m : expr ExprMap.t) : float =
      let rec aux (keys : expr list) (score_acc : float) (m : expr ExprMap.t) :
        float =
        match keys with
        | [] -> score_acc
        | pat :: ks ->
          let expr = ExprMap.find pat m in
          let score_acc = similarity pat expr +. score_acc in
          aux ks score_acc m
      in
      let keys = List.map (fun (k, _) -> k) (ExprMap.bindings m) in
      aux keys 0.0 m
    in
    let sort_solutions_by_score_descending (solutions : expr ExprMap.t list) :
      expr ExprMap.t list =
      List.sort
        (fun m1 m2 ->
           Misc_utils.compare_rev (solution_score m1) (solution_score m2) )
        solutions
    in
    let valid_combinations =
      all_combinations exprs1 exprs2
      (* |> filter_by_pattern_matches *)
    in
    Js_utils.console_log
      (Printf.sprintf "Number of valid combinations : %d"
         (List.length valid_combinations));
    let possible_solutions =
      valid_combinations |> group_by_exprs |> generate_possible_solutions
    in
    (* Js_utils.console_log (Printf.sprintf "Number of possible solutions : %d" (List.length possible_solutions)); *)
    let valid_solutions =
      possible_solutions |> filter_by_non_overlapping_exprs_expressions
      |> filter_by_compatible_var_bindings
    in
    (* Js_utils.console_log (Printf.sprintf "Number of valid solutions : %d" (List.length valid_solutions)); *)
    let sorted_solutions =
      valid_solutions |> sort_solutions_by_score_descending
    in
    (* Js_utils.console_log (Printf.sprintf "Number of sorted solutions : %d" (List.length sorted_solutions)); *)
    (* List.iter
     *   (fun m ->
     *      Js_utils.console_log (Printf.sprintf "Solution :");
     *      ExprMap.iter
     *        (fun k v ->
     *           Js_utils.console_log (Printf.sprintf "  %s -> %s" (expr_to_string k) (expr_to_string v))
     *        )
     *        m
     *   )
     *   sorted_solutions; *)
    match sorted_solutions with [] -> None | hd :: _ -> Some hd

  (* let rewrite_match_map ~(rewrite_rule_from : expr) ~(rewrite_rule_to : expr) ~(expr_from : expr) ~(expr_to : expr) : (expr * expr) * (expr * expr) =
   *   let all_combinations (rewrite_rule_from : expr) (rewrite_rule_to : expr) (expr_from : expr) (expr_to : expr) : ((expr * expr) * (expr * expr)) list =
   *     let rec aux (acc : ((expr * expr) * (expr * expr)) list) (sub_expr_froms : expr list) (sub_expr_tos : expr list) : ((expr * expr) * (expr * expr)) list =
   *       match sub_expr_froms with
   *       | []      -> acc
   *       | f :: fs ->
   *         let acc = (List.map (fun t -> (f, t)) sub_expr_tos) @ acc in
   *         aux acc fs sub_expr_tos
   *     in
   *     let sub_expr_froms = pattern_search ~pattern:rewrite_rule_from expr_from in
   *     let sub_expr_tos   = pattern_search ~pattern:rewrite_rule_to   expr_to   in
   *     aux sub_Expr_froms sub_expr_tos
   *   in
   *   let filter_by_pattern_matches (combinations : (expr * expr) list) : (expr * expr) list =
   *     let rec aux (acc : (expr * expr) list) (combinations : (expr * expr) list) : (expr * expr) list =
   *       match combinations with
   *       | []           -> acc
   *       | (p, e) :: cs ->
   *         let acc =
   *           if pattern_matches ~pattern:p e then
   *             (p, e) :: acc
   *           else
   *             acc
   *         in
   *         aux acc cs
   *     in
   *     aux [] combinations
   *   in
   *   let filter_by_matching_rewrite_result
   *       (expr_from         : expr)
   *       (expr_to           : expr)
   *       (rewrite_rule_from : expr)
   *       (rewrite_rule_to   : expr)
   *       (combinations      : (expr * expr) list)
   *     : (expr * expr) list =
   *     List.filter
   *       (fun (sub_expr_from, _) ->
   *          let res = rewrite expr_from ~rewrite_rule_from ~rewrite_rule_to ~expr_from:sub_expr_from in
   *          res = expr_to
   *       )
   *       combinations
   *   in
   *   let filter_by_compatible_var_bindings (solutions : ) *)

  (* let map_out_variable_substitution (rewriter : expr) (e : expr) : (expr ExprMap.t, variable_map_error) result =
   *   let rec aux (rewriter : expr) (e : expr) (m : expr ExprMap.t) : (expr ExprMap.t, variable_map_error) result =
   *     match (rewriter, e) with
   *     | (Variable (Unsure, _)           ), (_                              ) -> Error Unexpected_unsure_var
   *     | (_                              ), (Variable (Unsure, _)           ) -> Error Unexpected_unsure_var
   *     | (Variable (Existential, _)      ), (_                              ) -> Error Unexpected_existential_var
   *     | (_                              ), (Variable (Existential, _)      ) -> Error Unexpected_existential_var
   *     | (Variable (Free,   _)      as v1), (Variable (Free,   _)      as v2) -> if v1 = v2 then Ok m else Error Unmatching_free_var
   *     | (Variable (Universal, _)   as v1), (Variable (Universal,  _)  as v2) -> Ok (ExprMap.add v1 v2 m)
   *     | (Variable (Universal, _)   as v1), (Variable (Free, _)        as v2) -> Ok (ExprMap.add v1 v2 m)
   *     | (Function (f1, es1)        as v1), (Function (f2, es2)             ) ->
   *       if f1 = f2 then aux_list es1 es2 (Ok m)
   *       else            aux_list 
   *     | (UnaryOp  (op1, e1)             ), (UnaryOp  (op2, e2)             ) -> if op1 = op2 then aux e1 e2 m else Error Unmatching_structure
   *     | (BinaryOp (op1, e1a, e1b)       ), (BinaryOp (op2, e2a, e2b)       ) ->
   *       if op1 = op2 then aux_list [e1a; e1b] [e2a; e2b] (Ok m)
   *       else              Error Unmatching_structure
   *     | (Quantified (q))
   *     | _                                                                    -> Error Unmatching_structure
   *   and
   *   and aux_list (es1 : expr list) (es2 : expr list) (m_res : (expr ExprMap.t, variable_map_error) result) : (expr ExprMap.t, variable_map_error) result =
   *     List.fold_left2
   *       (fun m_res e1 e2 ->
   *          match m_res with
   *          | Ok m         -> aux e1 e2 m
   *          | Error _ as e -> e
   *       )
   *       m_res
   *       es1 es2
   *   in
   *   aux rewriter e ExprMap.empty *)

  let replace_universal_var_name (original : string) (replacement : string)
      (e : expr) : expr =
    let rec aux (original : string) (replacement : string) (e : expr) : expr =
      match e with
      | Variable (Universal, name) ->
        Variable (Universal, if name = original then replacement else name)
      | Variable _ as e -> e
      | Function (name, es) -> Function (name, aux_list original replacement es)
      | UnaryOp (op, e) -> UnaryOp (op, aux original replacement e)
      | BinaryOp (op, e1, e2) ->
        BinaryOp
          (op, aux original replacement e1, aux original replacement e2)
      | Quantified (q, ids, e) ->
        Quantified (q, ids, aux original replacement e)
      | False -> False
      | InsertedF _ as e -> e
    and aux_list (original : string) (replacement : string) (es : expr list) :
      expr list =
      List.map (aux original replacement) es
    in
    aux original replacement e

  let replace_universal_var_names (l : (string * string) list) (e : expr) :
    expr =
    let rec aux (l : (string * string) list) (e : expr) : expr =
      match l with
      | [] -> e
      | (name, replacement) :: l ->
        aux l (replace_universal_var_name name replacement e)
    in
    aux l e

  let universal_var_names (e : expr) : string list =
    let rec aux (e : expr) : string list =
      match e with
      | Variable (Universal, name) -> [name]
      | Variable _ -> []
      | Function (_, es) -> aux_list es
      | UnaryOp (_, e) -> aux e
      | BinaryOp (_, e1, e2) -> aux e1 @ aux e2
      | Quantified (_, _, e) -> aux e
      | False -> []
      | InsertedF _ -> []
    and aux_list (es : expr list) : string list =
      List.concat (List.map aux es)
    in
    aux e

  let make_gen_id (prefix : string) : unit -> string =
    let count = ref 0 in
    fun () ->
      let res = Printf.sprintf "%s%d" prefix !count in
      count := !count + 1;
      res

  let uniquify_universal_var_names_clause_sets (prefix : string)
      (ess : expr list list) : expr list list =
    let rec aux (gen_id : unit -> string) (acc : expr list list)
        (ess : expr list list) : expr list list =
      match ess with
      | [] -> List.rev acc
      | es :: ess ->
        let names =
          List.sort_uniq compare
            (List.concat (List.map universal_var_names es))
        in
        let name_map = List.map (fun n -> (n, gen_id ())) names in
        let res =
          List.map (fun e -> replace_universal_var_names name_map e) es
        in
        aux gen_id (res :: acc) ess
    in
    let gen_id = make_gen_id prefix in
    aux gen_id [] ess

  let uniquify_universal_var_names_generic
      ~(replace_id : string -> string -> 'a -> 'a)
      ~(get_exprs : 'a -> expr list) (prefix : string) (xs : 'a list) : 'a list
    =
    let rec aux (gen_id : unit -> string)
        (replace_id : string -> string -> 'a -> 'a)
        (get_exprs : 'a -> expr list) (acc : 'a list) (xs : 'a list) : 'a list
      =
      match xs with
      | [] -> List.rev acc
      | x :: xs ->
        let exprs = get_exprs x in
        let names =
          List.sort_uniq compare
            (List.concat (List.map universal_var_names exprs))
        in
        let name_map = List.map (fun n -> (n, gen_id ())) names in
        let res =
          List.fold_left
            (fun x (original, replacement) ->
               replace_id original replacement x )
            x name_map
        in
        aux gen_id replace_id get_exprs (res :: acc) xs
    in
    let gen_id = make_gen_id prefix in
    aux gen_id replace_id get_exprs [] xs

  let var_bindings_in_generic ?(m : expr VarMap.t = VarMap.empty)
      ~(get_pairs : 'a -> (expr * expr) list) (x : 'a) : expr VarMap.t =
    let pairs = get_pairs x in
    List.fold_left
      (fun m (k, v) ->
         m
         |> (fun m -> var_bindings_in_pattern_match ~m ~pattern:k v)
         |> fun m -> var_bindings_in_pattern_match ~m ~pattern:v k )
      m pairs

  let var_bindings_in_pairs ?(m : expr VarMap.t = VarMap.empty)
      (pairs : (expr * expr) list) : expr VarMap.t =
    List.fold_left
      (fun m (k, v) ->
         m
         |> (fun m -> var_bindings_in_pattern_match ~m ~pattern:k v)
         |> fun m -> var_bindings_in_pattern_match ~m ~pattern:v k )
      m pairs

  type data = {expr_str : string}

  type id = string

  let id_to_string x = x

  type node =
    | Data of data
    | Group

  let first_id = "0"

  let next_id s = s ^ "0"

  let label_internal (_id : id) (node : node) : string =
    match node with Data node -> node.expr_str | Group -> "Group"

  let color_internal (_id : id) (_node : node) : string = "#67cd61"

  (* match node.core with
     * | Some c -> "#67cd61"
     * | None   -> "#800000" *)

  let size_internal (_ : id) (_ : node) : int = 40

  let node_shape_internal (_ : id) (_ : node) : Cytoscape.node_shape = Circle
end

module Analyzed_expr_graph = Graph.Make (Analyzed_expr)

let expr_to_nodes (e : Analyzed_expr.expr) :
  Analyzed_expr_graph.node_record list =
  let gen_id =
    let f = Misc_utils.make_gen_id () in
    fun x -> string_of_int (f x)
  in
  let parent_to_list (parent : string option) : string list =
    match parent with None -> [] | Some x -> [x]
  in
  let children = [] in
  let group = None in
  let rec aux (parent : string option) (e : Analyzed_expr.expr) :
    Analyzed_expr_graph.node_record list =
    let id = gen_id () in
    let parents = parent_to_list parent in
    match e with
    | Variable (_, name) ->
      [ { id
        ; node = Some (Data {expr_str = name})
        ; parents = Some parents
        ; children = Some children
        ; group
        ; node_visible = Some true
        ; label_visible = Some true } ]
    | Function (name, es) ->
      { id
      ; node = Some (Data {expr_str = name})
      ; parents = Some parents
      ; children = Some children
      ; group
      ; node_visible = Some true
      ; label_visible = Some true }
      :: List.concat (List.map (aux (Some id)) es)
    | UnaryOp (op, e) ->
      { id
      ; node = Some (Data {expr_str = Expr_components.unary_op_to_string op})
      ; parents = Some parents
      ; children = Some children
      ; group
      ; node_visible = Some true
      ; label_visible = Some true }
      :: aux (Some id) e
    | BinaryOp (op, l, r) ->
      let left = aux (Some id) l in
      let right = aux (Some id) r in
      { id
      ; node =
          Some (Data {expr_str = Expr_components.binary_op_to_string op})
      ; parents = Some parents
      ; children = Some children
      ; group
      ; node_visible = Some true
      ; label_visible = Some true }
      :: (left @ right)
    | Quantified (q, _, e) ->
      { id
      ; node =
          Some (Data {expr_str = Expr_components.quantifier_to_string q})
      ; parents = Some parents
      ; children = Some children
      ; group
      ; node_visible = Some true
      ; label_visible = Some true }
      :: aux (Some id) e
    | False ->
      [ { id
        ; node = Some (Data {expr_str = "~"})
        ; parents = Some parents
        ; children = Some children
        ; group
        ; node_visible = Some true
        ; label_visible = Some true } ]
    | InsertedF l ->
      [ { id
        ; node =
            Some
              (Data
                 { expr_str =
                     Printf.sprintf "Inserted formula %s"
                       (String.concat ", " (List.map string_of_int l)) })
        ; parents = Some parents
        ; children = Some children
        ; group
        ; node_visible = Some true
        ; label_visible = Some true } ]
  in
  aux None e

let expr_to_node_map (e : Analyzed_expr.expr) : Analyzed_expr_graph.t =
  Analyzed_expr_graph.add_nodes_via_records Append (expr_to_nodes e)
    Analyzed_expr_graph.empty

type classification =
  | Unsure
  | Axiom
  | InitialKnowledge
  | Rewriting
  | Knowledge
  | NegatedGoal
  | Goal
  | Contradiction
  | ProtocolStep
  | InteractiveProtocolStep
  | Alias

(* |  *)

let classification_to_string (c : classification) : string =
  match c with
  | Unsure -> "unsure"
  | Axiom -> "axiom"
  | InitialKnowledge -> "initial knowledge"
  | Rewriting -> "rewriting"
  | Knowledge -> "knowledge"
  | Goal -> "goal"
  | NegatedGoal -> "negated goal"
  | Contradiction -> "contradiction"
  | ProtocolStep -> "protocol step"
  | InteractiveProtocolStep -> "interactive protocol step"
  | Alias -> "alias"

module Analyzed_graph_base = struct
  type data =
    { expr : Analyzed_expr.expr
    ; derive_descr : string
    ; classification : classification
    ; chain : string * string * string list }

  type node =
    | Data of data
    | Group

  let first_id = "0"

  let next_id s = s ^ "0"

  type id = string

  let id_to_string x = x

  let label_internal (_id : id) (node : node) : string =
    let open Printf in
    match node with
    | Data node ->
      (* sprintf "%d. %s %s"
       *   _id
       *   (Analyzed_expr.expr_to_string node.expr)
       *   (StringLabels.capitalize_ascii (classification_to_string node.classification)) *)
      sprintf "%s %s"
        (Analyzed_expr.expr_to_string node.expr)
        (StringLabels.capitalize_ascii
           (classification_to_string node.classification))
    | Group -> sprintf "%s. Group" _id

  let color_internal (_id : id) (node : node) : string =
    match node with
    | Data node -> (
        match node.classification with
        | Unsure -> "#FFC300"
        | Axiom -> "#74C2F6"
        | InitialKnowledge -> "#64db7e"
        | Rewriting -> "#5C91E5"
        | Knowledge -> "#30873E"
        | Goal -> "#4C5967"
        | NegatedGoal -> "#4C5967"
        | Contradiction -> "#4C5967"
        | ProtocolStep -> "#F67476"
        | InteractiveProtocolStep -> "#E10E11"
        | Alias -> "#979890" )
    | Group -> "#ff0000"

  let size_internal (_id : id) (node : node) : int =
    match node with Data _ -> 40 | Group -> 80

  let node_shape_internal (_id : id) (_node : node) : Cytoscape.node_shape =
    Circle
end

module Analyzed_graph = Graph.Make (Analyzed_graph_base)

let line_to_node_record (line : Raw_line.line) : Analyzed_graph.node_record =
  let id, raw_expr, derive_descr, parents = line in
  { id
  ; children = Some []
  ; parents = Some parents
  ; node =
      Some
        (Data
           { expr = Analyzed_expr.raw_expr_to_analyzed_expr raw_expr
           ; classification = Unsure
           ; derive_descr
           ; chain = (id, id, [id]) })
  ; group = None
  ; node_visible = Some true
  ; label_visible = Some true }

type node = Analyzed_graph.node

type node_graph = Analyzed_graph.t

type info_source =
  | Step of string
  | Axiom of Analyzed_expr.expr
  | Expr of Analyzed_expr.expr

type derive_explanation =
  | Nothing_to_explain
  | Dont_know_how
  | Rewrite of (Analyzed_expr.expr * Analyzed_expr.expr) list
  | Combine_knowledge of info_source list * Analyzed_expr.expr list
  | Gain_knowledge of
      info_source list
      * (Analyzed_expr.expr * Analyzed_expr.expr) list
      * (Analyzed_expr.expr * Analyzed_expr.expr) list

type grouped_derive_explanations =
  | Nothing_to_explain
  | Dont_know_how
  | Rewrites of Analyzed_expr.expr list list
  | Combine_knowledge of info_source list * Analyzed_expr.expr list
  | Gain_knowledge of info_source list * Analyzed_expr.expr list

let uniquify_universal_var_names_derive_explanations
    (explanations : derive_explanation list) : derive_explanation list =
  let replace_id (original : string) (replacement : string)
      (explanation : derive_explanation) : derive_explanation =
    let replace_id_for_pairs (original : string) (replacement : string)
        (pairs : (Analyzed_expr.expr * Analyzed_expr.expr) list) :
      (Analyzed_expr.expr * Analyzed_expr.expr) list =
      List.map
        (fun (k, v) ->
           ( Analyzed_expr.replace_universal_var_name original replacement k
           , Analyzed_expr.replace_universal_var_name original replacement v )
        )
        pairs
    in
    match explanation with
    | Nothing_to_explain -> explanation
    | Dont_know_how -> explanation
    | Rewrite pairs ->
      Rewrite (replace_id_for_pairs original replacement pairs)
    | Combine_knowledge (infos, es) ->
      Combine_knowledge
        ( List.map
            (fun info ->
               match info with
               | Expr e ->
                 Expr
                   (Analyzed_expr.replace_universal_var_name original
                      replacement e)
               | _ -> info )
            infos
        , List.map
            (Analyzed_expr.replace_universal_var_name original replacement)
            es )
    | Gain_knowledge (infos, pairs1, pairs2) ->
      Gain_knowledge
        ( infos
        , replace_id_for_pairs original replacement pairs1
        , replace_id_for_pairs original replacement pairs2 )
  in
  let get_exprs (explanation : derive_explanation) : Analyzed_expr.expr list =
    let pairs_to_exprs (pairs : (Analyzed_expr.expr * Analyzed_expr.expr) list)
      : Analyzed_expr.expr list =
      List.fold_left (fun acc (k, v) -> k :: v :: acc) [] pairs
    in
    match explanation with
    | Nothing_to_explain -> []
    | Dont_know_how -> []
    | Rewrite pairs -> pairs_to_exprs pairs
    | Combine_knowledge (infos, es) ->
      List.map
        (fun info ->
           match info with Expr e -> e | _ -> failwith "Unexpected case" )
        (List.filter
           (fun info ->
              match info with
              | Step _ -> false
              | Axiom _ -> false
              | Expr _ -> true )
           infos)
      @ es
    (* | Combine_knowledge (_, _)              -> [] *)
    | Gain_knowledge (_, pairs1, pairs2) ->
      pairs_to_exprs pairs1 @ pairs_to_exprs pairs2
  in
  Analyzed_expr.uniquify_universal_var_names_generic ~replace_id ~get_exprs "X"
    explanations

let var_bindings_in_explanations (explanations : derive_explanation list) :
  Analyzed_expr.expr Analyzed_expr.VarMap.t =
  let open Analyzed_expr in
  let get_pairs (explanation : derive_explanation) : (expr * expr) list =
    match explanation with
    | Nothing_to_explain -> []
    | Dont_know_how -> []
    | Rewrite pairs -> pairs
    | Combine_knowledge _ -> []
    | Gain_knowledge (_, pairs1, pairs2) -> pairs1 @ pairs2
  in
  List.fold_left
    (fun m e -> var_bindings_in_generic ~m ~get_pairs e)
    VarMap.empty explanations

let mark_free_variables (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let mark_free_variable_possibly () (id : id) (node : node) (m : node_graph) =
    let data = unwrap_data node in
    let parents = find_parents id m in
    let data =
      { data with
        expr =
          ( if parents = [] then Analyzed_expr.mark_if_unsure Free data.expr
            else data.expr ) }
    in
    ((), Analyzed_graph.add_node Overwrite id (Data data) m)
  in
  let (), m =
    Analyzed_graph.linear_traverse ()
      (Full_traversal mark_free_variable_possibly) m
  in
  m

let mark_universal_variables (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let mark_universal_variable_possibly () (id : id) (node : node)
      (m : node_graph) =
    let data = unwrap_data node in
    let data =
      {data with expr = Analyzed_expr.mark_if_unsure Universal data.expr}
    in
    ((), Analyzed_graph.add_node Overwrite id (Data data) m)
  in
  let (), m =
    Analyzed_graph.linear_traverse ()
      (Full_traversal mark_universal_variable_possibly) m
  in
  m

let propagate_variable_boundedness (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let propagate_boundedness_to_child (m : node_graph) target_id child_id =
    let boundedness =
      Analyzed_expr.get_boundedness (unwrap_data (find_node target_id m)).expr
    in
    let node = unwrap_data (find_node child_id m) in
    let node =
      {node with expr = Analyzed_expr.update_boundedness node.expr boundedness}
    in
    Analyzed_graph.add_node Overwrite child_id (Data node) m
  in
  let propagate_boundedness_to_children () (id : id) (_node : node)
      (m : node_graph) =
    let children = find_children id m in
    ( ()
    , List.fold_left
        (fun m child_id -> propagate_boundedness_to_child m id child_id)
        m children )
  in
  let (), m =
    Analyzed_graph.linear_traverse ()
      (Full_traversal propagate_boundedness_to_children) m
  in
  m

module Protocol_step = struct
  type direction =
    | Client_to_intruder
    | Intruder_to_client

  type in_out = In | Out

  type t =
    { proc_name : string option
    ; in_out : in_out
    ; direction : direction
    ; step_num : int
    ; expr : Analyzed_expr.expr }

  let break_down_step_string (s : string) : string option * in_out option * int option =
    let rec aux (parts : string list) (proc_name_parts : string list) (in_out : in_out option)
        (n : int option) : string option * in_out option * int option =
      match parts with
      | [] ->
        ( ( match List.rev proc_name_parts with
              | [] -> None
              | l -> Some (String.concat "_" l) )
          , in_out
          , n )
      | ["out"; n] -> aux [] proc_name_parts (Some Out) (int_of_string_opt n)
      | ["in"; n] -> aux [] proc_name_parts (Some In) (int_of_string_opt n)
      | x :: xs -> aux xs (x :: proc_name_parts) in_out n
    in
    aux (String.split_on_char '_' s) [] None None

  let node_to_steps (node : node) : t list =
    match node with
    | Group -> []
    | Data node -> (
        match node.classification with
        | ProtocolStep -> (
            match Analyzed_expr.(node.expr |> strip_att) with
            | Function (name, [expr]) -> (
                match break_down_step_string name with
                | proc_name, Some in_out, Some step_num ->
                  [ { proc_name
                    ; in_out
                    ; step_num
                    ; direction = Client_to_intruder
                    ; expr } ]
                | _ -> []
              )
            | _ -> [] )
        | InteractiveProtocolStep -> (
            let pre, e =
              let open Analyzed_expr in
              node.expr |> strip_quant |> split_on_impl
              |> (function None -> failwith "Unexpected None" | Some x -> x)
              |> fun (x, y) -> (strip_att x, strip_att y)
            in
            match Analyzed_expr.get_function_args e with
            | [e1; e2] -> (
                match break_down_step_string (Analyzed_expr.expr_to_string e2) with
                | None, Some in_out, Some step_num ->
                  [ { proc_name = None
                    ; in_out
                    ; step_num
                    ; direction = Client_to_intruder
                    ; expr = e1 }
                  ; { proc_name = None
                    ; in_out
                    ; step_num
                    ; direction = Intruder_to_client
                    ; expr = pre } ]
                | Some proc_name, Some in_out, Some step_num ->
                  [ { proc_name = Some proc_name
                    ; in_out
                    ; step_num
                    ; direction = Client_to_intruder
                    ; expr = e1 }
                  ; { proc_name = Some proc_name
                    ; in_out
                    ; step_num
                    ; direction = Intruder_to_client
                    ; expr = pre } ]
                | _ -> [] )
            | _ -> [] )
        | _ -> [] )
end

let classify_negated_goal (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let classify () (id : id) (node : node) (m : node_graph) : unit * node_graph
    =
    let data = unwrap_data node in
    match data.classification with
    | Unsure ->
      let classification =
        if data.derive_descr = "negated_conjecture" then NegatedGoal
        else
          let parents = find_nodes (find_parents id m) m in
          let all_parents_negated_goal =
            List.for_all
              (fun x -> (unwrap_data x).classification = NegatedGoal)
              parents
          in
          if parents <> [] && all_parents_negated_goal then NegatedGoal
          else data.classification
      in
      let data = {data with classification} in
      ((), add_node Overwrite id (Data data) m)
    | _ -> ((), m)
  in
  linear_traverse () (Full_traversal classify) m |> unwrap_tuple_1

let classify_goal (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let classify () (id : id) (node : node) (m : node_graph) : unit * node_graph
    =
    let data = unwrap_data node in
    match data.classification with
    | Unsure ->
      let classification =
        let no_parents = find_parents id m = [] in
        let children = find_nodes (find_children id m) m in
        let any_child_negated_goal =
          List.filter
            (fun x -> (unwrap_data x).classification = NegatedGoal)
            children
          <> []
        in
        if no_parents && any_child_negated_goal then Goal
        else data.classification
      in
      let data = {data with classification} in
      ((), add_node Overwrite id (Data data) m)
    | _ -> ((), m)
  in
  linear_traverse () (Full_traversal classify) m |> unwrap_tuple_1

let classify_protocol_step (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let check_tag (tag : string) : bool =
    match Protocol_step.break_down_step_string tag with
    | _, Some _, Some _ -> true
    | _ -> false
  in
  let classify () (id : id) (node : node) (m : node_graph) : unit * node_graph
    =
    let data = unwrap_data node in
    match data.classification with
    | Unsure -> (
        match find_parents id m with
        | [] ->
          let classification =
            match data.expr with
            | Function
                ("attacker", [Function (name, _)]) ->
              (match Protocol_step.break_down_step_string name with
               | _, Some _, Some _ -> ProtocolStep
               | _ -> data.classification)
            | Quantified
                ( _
                , _
                , BinaryOp
                    ( Imply
                    , Function
                        ( "attacker"
                        , [Function (name_1, _)])
                    , Function
                        ( "attacker"
                        , [Function (name_2, _)] ) )
                )
              ->
              (match Protocol_step.break_down_step_string name_1, Protocol_step.break_down_step_string name_2 with
               | (_, Some _, Some _), (_, Some _, Some _) -> InteractiveProtocolStep
               | _ -> data.classification
              )
            | _ -> data.classification
          in
          let data = {data with classification} in
          ((), add_node Overwrite id (Data data) m)
        | _ -> ((), m) )
    | _ -> ((), m)
  in
  linear_traverse () (Full_traversal classify) m |> unwrap_tuple_1

let classify_axiom (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let classify () (id : id) (node : node) (m : node_graph) : unit * node_graph
    =
    let data = unwrap_data node in
    match data.classification with
    | Unsure -> (
        match find_parents id m with
        | [] ->
          let classification =
            match data.expr with
            | Quantified (`Forall, _, BinaryOp (Eq, _, _)) ->
              (Axiom : classification)
            | Quantified (`Forall, _, BinaryOp (Imply, _, _)) -> Axiom
            | _ -> data.classification
          in
          let data = {data with classification} in
          ((), add_node Overwrite id (Data data) m)
        | _ -> ((), m) )
    | _ -> ((), m)
  in
  linear_traverse () (Full_traversal classify) m |> unwrap_tuple_1

let classify_rewriting (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let classify () (id : id) (node : node) (m : node_graph) : unit * node_graph
    =
    let data = unwrap_data node in
    match data.classification with
    | Unsure ->
      let parents = find_nodes (find_parents id m) m in
      let all_parents_axiom_or_rewriting =
        List.for_all
          (fun x ->
             (unwrap_data x).classification = Axiom
             || (unwrap_data x).classification = Rewriting )
          parents
      in
      let classification =
        if parents <> [] && all_parents_axiom_or_rewriting then Rewriting
        else data.classification
      in
      let data = {data with classification} in
      ((), add_node Overwrite id (Data data) m)
    | _ -> ((), m)
  in
  linear_traverse () (Full_traversal classify) m |> unwrap_tuple_1

let classify_initial_knowledge (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let classify () (id : id) (node : node) (m : node_graph) : unit * node_graph
    =
    let data = unwrap_data node in
    match data.classification with
    | Unsure -> (
        match find_parents id m with
        | [] ->
          let classification =
            match data.expr with
            | Function ("attacker", _) -> InitialKnowledge
            | _ -> data.classification
          in
          let data = {data with classification} in
          ((), add_node Overwrite id (Data data) m)
        | _ -> ((), m) )
    | _ -> ((), m)
  in
  linear_traverse () (Full_traversal classify) m |> unwrap_tuple_1

let classify_contradiction (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let classify () (id : id) (node : node) (m : node_graph) : unit * node_graph
    =
    let data = unwrap_data node in
    match data.classification with
    | Unsure ->
      let classification =
        match data.expr with
        | False -> Contradiction
        | _ -> data.classification
      in
      let data = {data with classification} in
      ((), add_node Overwrite id (Data data) m)
    | _ -> ((), m)
  in
  linear_traverse () (Full_traversal classify) m |> unwrap_tuple_1

let classify_knowledge (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let classify () (id : id) (node : node) (m : node_graph) : unit * node_graph
    =
    let data = unwrap_data node in
    match data.classification with
    | Unsure ->
      let parents = find_nodes (find_parents id m) m in
      let any_parents_protocol_step_or_knowledge =
        List.exists
          (fun x ->
             (unwrap_data x).classification = InteractiveProtocolStep
             || (unwrap_data x).classification = ProtocolStep
             || (unwrap_data x).classification = InitialKnowledge
             || (unwrap_data x).classification = Knowledge )
          parents
      in
      let classification =
        if any_parents_protocol_step_or_knowledge then Knowledge
        else data.classification
      in
      let data = {data with classification} in
      ((), add_node Overwrite id (Data data) m)
    | _ -> ((), m)
  in
  linear_traverse () (Full_traversal classify) m |> unwrap_tuple_1

let classify_alias (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let classify () (id : id) (node : node) (m : node_graph) : unit * node_graph
    =
    let data = unwrap_data node in
    match data.classification with
    | Unsure -> (
        match find_parents id m with
        | [] ->
          let classification =
            match data.expr with
            | BinaryOp (Iff, _, _) -> Alias
            | _ -> data.classification
          in
          let data = {data with classification} in
          ((), add_node Overwrite id (Data data) m)
        | parent_ids ->
          let parents = find_nodes parent_ids m in
          let any_parent_alias =
            List.exists
              (fun x -> (unwrap_data x).classification = Alias)
              parents
          in
          let classification =
            if any_parent_alias then
              let aliases =
                List.filter
                  (fun id ->
                     (unwrap_data (find_node id m)).classification = Alias )
                  parent_ids
              in
              let alias = List.nth aliases 0 in
              (* look at the classifiction of the origninal node *)
              let children =
                List.filter (fun x -> x <> id) (find_children alias m)
              in
              match children with
              | [] -> data.classification
              | children ->
                let original = find_node (List.nth children 0) m in
                (unwrap_data original).classification
            else data.classification
          in
          let data = {data with classification} in
          ((), add_node Overwrite id (Data data) m) )
    | _ -> ((), m)
  in
  linear_traverse () (Full_traversal classify) m |> unwrap_tuple_1

let redraw_alias_arrows (m : node_graph) : node_graph =
  let open Analyzed_graph in
  (* find node with more than one Alais parent *)
  let nodes =
    to_assoc_list
      (filter
         (fun id _node m ->
            let parents = find_nodes (find_parents id m) m in
            let alias_count =
              List.length
                (List.filter
                   (fun n -> (unwrap_data n).classification = Alias)
                   parents)
            in
            alias_count > 1 )
         m)
  in
  (* redraw arrows *)
  List.fold_left
    (fun m (id, n) ->
       let parents = find_parents id m in
       let connected_aliases =
         List.filter
           (fun id -> (unwrap_data (find_node id m)).classification = Alias)
           parents
       in
       let parents =
         List.filter (fun id -> not (List.mem id connected_aliases)) parents
       in
       let children = find_children id m @ connected_aliases in
       (* let children = connected_aliases in *)
       add_node Overwrite id n ~children ~parents m )
    m nodes

let rewrite_conclusion (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let collect_ids_to_remove (goal_id : id) (m : node_graph) : id list =
    let rec aux acc id m =
      let acc = id :: acc in
      match find_children id m with
      | [] -> acc
      | l -> List.fold_left (fun acc x -> aux acc x m) acc l
    in
    aux [] goal_id m
  in
  (* get things related to contradiction node *)
  (* let contra_id =
   *   unwrap_opt
   *     (filter_first_opt
   *        (fun _ node _ -> (unwrap_data node).classification = Contradiction) m)
   * in
   * let contra_parents = find_parents contra_id m in *)

  (* get things related to goal node **)
  match
    filter_first_opt
      (fun _ node _ -> (unwrap_data node).classification = Goal)
      m
  with
  | None -> m
  | Some goal_id ->
    let goal = find_node goal_id m in
    let remove_ids = collect_ids_to_remove goal_id m in
    let exclude_parent_ids = goal_id :: remove_ids in
    (* collect parents *)
    let parents =
      List.filter
        (fun x -> not (List.mem x exclude_parent_ids))
        (List.fold_left (fun acc id -> find_parents id m @ acc) [] remove_ids)
    in
    (* remove unneeded nodes *)
    let m = remove_nodes remove_ids m in
    (* replace contradiction with goal *)
    add_node Overwrite goal_id goal ~children:[] ~parents m

let classify_nodes (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let classify_node () (id : id) (node : node) (m : node_graph) =
    let parents = find_parents id m in
    let new_node =
      match parents with
      | [] ->
        let data = unwrap_data node in
        let is_negated_goal = data.derive_descr = "negated conjecture" in
        let func_names = Analyzed_expr.get_function_names data.expr in
        let is_axiom =
          match data.expr with
          | Analyzed_expr.Quantified _ -> true
          | _ -> false
        in
        let is_knowledge_possibly =
          List.filter (fun x -> x = "attacker") func_names <> []
        in
        { data with
          classification =
            ( if is_negated_goal then NegatedGoal
              else if is_axiom then Axiom
              else if is_knowledge_possibly then InitialKnowledge
              else Unsure ) }
      | parents ->
        let data = unwrap_data node in
        let is_negated_goal = data.derive_descr = "negated conjecture" in
        let is_contradiction = data.expr = False in
        let parents = find_nodes parents m in
        let any_parent_negated_goal =
          List.filter
            (fun (x : node) -> (unwrap_data x).classification = NegatedGoal)
            parents
          <> []
        in
        let all_parents_rewrite =
          List.filter
            (fun (x : node) ->
               let data = unwrap_data x in
               data.classification = Axiom || data.classification = Rewriting
            )
            parents
          = parents
          && parents <> []
        in
        let any_parent_knowledge =
          List.filter
            (fun (x : node) ->
               let data = unwrap_data x in
               data.classification = InitialKnowledge
               || data.classification = Knowledge )
            parents
          <> []
        in
        { data with
          classification =
            ( if is_contradiction then Contradiction
              else if is_negated_goal then NegatedGoal
              else if all_parents_rewrite then Rewriting
              else if any_parent_knowledge then Knowledge
              else if any_parent_negated_goal then NegatedGoal
              else Unsure ) }
    in
    ((), Analyzed_graph.add_node Overwrite id (Data new_node) m)
  in
  let (), m =
    Analyzed_graph.linear_traverse () (Full_traversal classify_node) m
  in
  m

let remove_goal (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let remove_if_goal () (id : id) (node : node) (m : node_graph) =
    let children = find_children id m in
    let parents = find_parents id m in
    match children with
    | [] -> ((), m)
    | l ->
      let data = unwrap_data node in
      let is_negated_goal = data.classification = NegatedGoal in
      let children = find_nodes l m in
      let any_child_negated_goal =
        List.filter
          (fun (x : node) ->
             let data = unwrap_data x in
             data.classification = NegatedGoal )
          children
        <> []
      in
      if (not is_negated_goal) && parents = [] && any_child_negated_goal then
        ((), Analyzed_graph.remove_node id m)
      else ((), m)
  in
  linear_traverse () (Full_traversal remove_if_goal) m
  |> Misc_utils.unwrap_tuple_1

let get_chain (m : node_graph) (id : string) : string * string * string list =
  let open Analyzed_graph in
  let rec aux (m : node_graph) (id : string) (acc : string list) :
    string * string * string list =
    let node = find_node id m in
    let data = unwrap_data node in
    let parents = find_parents id m in
    let children = find_children id m in
    let acc =
      if
        (parents = [] || List.length parents = 1)
        && data.classification <> Contradiction
      then id :: acc
      else acc
    in
    match children with
    | [x] -> aux m x acc
    | _ ->
      let tail = List.hd acc in
      let acc = List.rev acc in
      let head = List.hd acc in
      (head, tail, acc)
  in
  aux m id []

let mark_chains (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let rec update_chain (m : node_graph) chain ids =
    match ids with
    | [] -> m
    | x :: xs ->
      let node = find_node x m in
      let data = unwrap_data node in
      let data = {data with chain} in
      update_chain
        (Analyzed_graph.add_node Overwrite x (Data data) m)
        chain xs
  in
  let mark_chain () (id : id) (_node : node) (m : node_graph) =
    let parents = find_parents id m in
    match parents with
    | [] ->
      let hd, tl, chain = get_chain m id in
      ((), update_chain m (hd, tl, chain) chain)
    | _ -> ((), m)
  in
  linear_traverse () (Full_traversal mark_chain) m |> Misc_utils.unwrap_tuple_1

let compress_chains (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let compress_chain () (id : id) (node : node) (m : node_graph) =
    let parents = find_parents id m in
    match parents with
    | [] ->
      (* let (_, tl, chain)  = (unwrap_data node).chain in
       * let m               = Analyzed_graph.remove_nodes (List.tl (List.rev chain)) m in
       * let tail            = find_node tl m in
       * let data            = unwrap_data tail in
       * let data            = { data with
       *                         expr           = data.expr;
       *                         classification = data.classification;
       *                       } in
       * ((), add_node id (Data data) m) *)
      let data = unwrap_data node in
      let _, tl, chain = data.chain in
      let tail = unwrap_data (find_node tl m) in
      let tail =
        { tail with
          expr = data.expr
        ; derive_descr = data.derive_descr
        ; classification = data.classification }
      in
      ( ()
      , m
        |> Analyzed_graph.remove_nodes (List.tl (List.rev chain))
        (* |> Analyzed_graph.remove_nodes (List.tl chain) *)
        |> Analyzed_graph.add_node Overwrite tl (Data tail) )
    | _ -> ((), m)
  in
  linear_traverse () (Full_traversal compress_chain) m
  |> Misc_utils.unwrap_tuple_1

let compress_rewrite_trees (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let op () (id : id) (node : node) (m : node_graph) : unit * node_graph =
    let m =
      match node with
      | Data data -> (
          match data.classification with
          | Rewriting -> compress_bfs Bottom_to_top id m
          | _ -> m )
      | Group -> m
    in
    ((), m)
  in
  let bottom_id, _ =
    List.hd (to_assoc_list (filter (fun id _n m -> find_children id m = []) m))
  in
  let _, m = bfs_traverse bottom_id () Bottom_to_top (Full_traversal op) m in
  m

let compress_knowledge_trees (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let op () (id : id) (node : node) (m : node_graph) : unit * node_graph =
    let m =
      match node with
      | Data data -> (
          match data.classification with
          | Knowledge -> compress_bfs Bottom_to_top id m
          | _ -> m )
      | Group -> m
    in
    ((), m)
  in
  let bottom_id, _ =
    List.hd (to_assoc_list (filter (fun id _n m -> find_children id m = []) m))
  in
  let _, m = bfs_traverse bottom_id () Bottom_to_top (Full_traversal op) m in
  m

let node_list_to_map (node_records : Analyzed_graph.node_record list) :
  node_graph =
  let classify (m : node_graph) : node_graph =
    m |> classify_negated_goal |> classify_goal |> classify_protocol_step
    |> classify_axiom |> classify_rewriting |> classify_initial_knowledge
    |> classify_contradiction |> classify_knowledge
  in
  Analyzed_graph.add_nodes_via_records Overwrite node_records
    Analyzed_graph.empty
  |> mark_free_variables |> propagate_variable_boundedness
  |> mark_universal_variables |> classify |> classify_alias |> classify
  |> rewrite_conclusion |> redraw_alias_arrows

(* |> mark_chains *)
(* |> compress_chains *)
(* |> compress_rewrite_trees *)
(* |> compress_knowledge_trees *)

let trace_sources (id : Analyzed_graph.id) (m : node_graph) : info_source list
  =
  let open Analyzed_graph in
  let check_tag (tag : string) : bool =
    match Protocol_step.break_down_step_string tag with
    | _, Some _, Some _ -> true
    | _ -> false
  in
  let reformat_tag (tag : string) : string =
    match Protocol_step.break_down_step_string tag with
    | Some p, Some In, Some n -> Printf.sprintf "%s.in.%d" p n
    | Some p, Some Out, Some n -> Printf.sprintf "%s.out.%d" p n
    | None, Some In, Some n -> Printf.sprintf "GLOBAL.in.%d" n
    | None, Some Out, Some n -> Printf.sprintf "GLOBAL.out.%d" n
    | _ -> failwith "Unexpected case"
  in
  let rec aux (id : id) (m : node_graph) : info_source list =
    match find_parents id m with
    | [] -> (
        let data = unwrap_data (find_node id m) in
        match data.expr with
        | Function
            ("attacker", [Function ("tuple_2", [_; Variable (Free, tag)])])
          when check_tag tag ->
          [Step (reformat_tag tag)]
        | Quantified
            ( _
            , _
            , BinaryOp
                ( Imply
                , _
                , Function
                    ( "attacker"
                    , [Function ("tuple_2", [_; Variable (Free, tag)])] ) ) )
          when check_tag tag ->
          [Step (reformat_tag tag)]
        | _ -> [Axiom data.expr] )
    | ps -> List.concat (List.map (fun p -> aux p m) ps)
  in
  List.sort_uniq compare (aux id m)

let info_source_to_string (x : info_source) : string =
  match x with
  | Step tag -> Printf.sprintf "step %s" tag
  | Axiom ax -> Printf.sprintf "axiom %s" (Analyzed_expr.expr_to_string ax)
  | Expr e -> Printf.sprintf "%s" (Analyzed_expr.expr_to_string e)

let explain_construction_single (id : Analyzed_graph.id) (m : node_graph) :
  derive_explanation =
  let open Analyzed_graph in
  let open Analyzed_expr in
  let is_rewrite (e : expr) : bool =
    match e with BinaryOp (Eq, _, _) -> true | _ -> false
  in
  let base = unwrap_data (find_node id m) in
  match find_children id m with
  | [] -> Nothing_to_explain
  | [result_id] -> (
      let result = unwrap_data (find_node result_id m) in
      match List.filter (fun x -> x <> id) (find_parents result_id m) with
      | [] -> Nothing_to_explain
      | [agent_id] -> (
          (* explain single base, agent, and result *)
          let agent = unwrap_data (find_node agent_id m) in
          let base_expr = remove_subsumptions base.expr in
          let agent_expr = remove_subsumptions agent.expr in
          let result_expr = remove_subsumptions result.expr in
          (* let base_expr   = unwrap_subsume base.expr   in
           * let agent_expr  = unwrap_subsume agent.expr  in
           * let result_expr = unwrap_subsume result.expr in *)
          let base_expr = base_expr |> Analyzed_expr.negate |> strip_quant in
          let agent_expr = agent_expr |> Analyzed_expr.negate |> strip_quant in
          let result_expr =
            result_expr |> Analyzed_expr.negate |> strip_quant
          in
          let base_exprs = split_on_and base_expr in
          let agent_exprs = split_on_and agent_expr in
          let result_exprs = split_on_and result_expr in
          let base_exprs =
            base_exprs |> List.map strip_not
            |> List.map strip_pred_attacker
            |> List.filter (fun x -> x <> False)
          in
          let agent_exprs =
            agent_exprs |> List.map strip_not
            |> List.map strip_pred_attacker
            |> List.filter (fun x -> x <> False)
          in
          let result_exprs =
            result_exprs |> List.map strip_not
            |> List.map strip_pred_attacker
            |> List.filter (fun x -> x <> False)
          in
          match (base_exprs, agent_exprs, result_exprs) with
          | [b_expr], [a_expr], [r_expr] when is_rewrite a_expr ->
            Rewrite [(r_expr, b_expr)]
          | [b_expr], _, r_exprs ->
            Combine_knowledge
              ( trace_sources agent_id m @ List.map (fun x -> Expr x) r_exprs
              , [b_expr] )
          | b_exprs, [a_expr], r_exprs
            when is_rewrite a_expr && List.length b_exprs = List.length r_exprs
            ->
            let match_map = pattern_multi_match_map r_exprs b_exprs in
            Js_utils.console_log
              (Printf.sprintf "match_map size : %d"
                 (List.length (ExprMap.bindings (unwrap_opt match_map))));
            Rewrite (ExprMap.bindings (unwrap_opt match_map))
          | b_exprs, a_exprs, r_exprs
            when List.length b_exprs
                 = List.length a_exprs + List.length r_exprs ->
            let match_map =
              unwrap_opt
                (pattern_multi_match_map (a_exprs @ r_exprs) b_exprs)
            in
            let new_knowledge =
              ExprMap.bindings match_map
              |> List.filter (fun (k, _) -> List.mem k a_exprs)
            in
            let old_knowledge =
              ExprMap.bindings match_map
              |> List.filter (fun (k, _) -> List.mem k r_exprs)
            in
            Gain_knowledge
              (trace_sources agent_id m, new_knowledge, old_knowledge)
          | _ -> Dont_know_how )
      | _ -> Dont_know_how )
  | _ -> Dont_know_how

let explain_construction_single_chained (id : Analyzed_graph.id)
    (m : node_graph) : derive_explanation list =
  let open Analyzed_graph in
  let open Analyzed_expr in
  let get_chain (id : id) (m : node_graph) : id list =
    let rec aux (acc : id list) (id : id) : id list =
      let acc = id :: acc in
      match find_children id m with [] -> acc | c :: _ -> aux acc c
    in
    aux [] id
  in
  List.map (fun id -> explain_construction_single id m) (get_chain id m)

let group_derive_explanations (explanations : derive_explanation list) :
  grouped_derive_explanations list =
  let open Analyzed_expr in
  let same_group (e1 : derive_explanation) (e2 : derive_explanation) : bool =
    match (e1, e2) with
    | Nothing_to_explain, Nothing_to_explain -> true
    | Dont_know_how, Dont_know_how -> true
    | Rewrite _, Rewrite _ -> true
    | Combine_knowledge _, Combine_knowledge _ -> true
    | Gain_knowledge _, Gain_knowledge _ -> true
    | _ -> false
  in
  let group_into_list (explanations : derive_explanation list) :
    derive_explanation list list =
    let rec aux (acc : derive_explanation list list)
        (explanations : derive_explanation list) : derive_explanation list list
      =
      match explanations with
      | [] -> List.rev (List.map List.rev acc)
      | e :: es ->
        let acc : derive_explanation list list =
          match acc with
          | [] -> [[e]]
          | last_es :: acc -> (
              match last_es with
              | [] -> [e] :: acc
              | last_e :: last_es ->
                if same_group e last_e then (e :: last_e :: last_es) :: acc
                else [e] :: (last_e :: last_es) :: acc )
        in
        aux acc es
    in
    aux [] explanations
  in
  let convert_rewrite (explanations : derive_explanation list) :
    grouped_derive_explanations =
    let rec match_into_buckets (buckets : expr list list)
        (pairs_list : (expr * expr) list list) : expr list list =
      match pairs_list with
      | [] -> List.map List.rev buckets
      | pairs :: rest ->
        let buckets =
          match buckets with
          | [] -> List.map (fun (k, v) -> [k; v]) pairs
          | buckets ->
            let pair_heads = List.map (fun (k, _) -> k) pairs in
            let bucket_heads = List.map List.hd buckets in
            let match_map =
              unwrap_opt (pattern_multi_match_map bucket_heads pair_heads)
            in
            List.map
              (fun l ->
                 match l with
                 | [] -> []
                 | hd :: tl ->
                   let new_hd =
                     List.assoc (ExprMap.find hd match_map) pairs
                   in
                   new_hd :: hd :: tl )
              buckets
        in
        match_into_buckets buckets rest
    in
    let match_pairs_list : (expr * expr) list list =
      List.map
        (fun x ->
           match x with
           | Rewrite pairs -> pairs
           | _ -> failwith "Incorrect case" )
        explanations
    in
    Rewrites (match_into_buckets [] match_pairs_list)
  in
  let convert_combine_knowledge (explanations : derive_explanation list) :
    grouped_derive_explanations list =
    List.map
      (fun (e : derive_explanation) ->
         ( match e with
           | Combine_knowledge (info_src, es) -> Combine_knowledge (info_src, es)
           | _ -> failwith "Incorrect case"
                  : grouped_derive_explanations ) )
      explanations
  in
  let convert_gain_knowledge (explanations : derive_explanation list) :
    grouped_derive_explanations list =
    List.map
      (fun (e : derive_explanation) ->
         ( match e with
           | Gain_knowledge (info_src, new_knowledge, _) ->
             Gain_knowledge
               (info_src, List.map (fun (k, _) -> k) new_knowledge)
           | _ -> failwith "Incorrect case"
                  : grouped_derive_explanations ) )
      explanations
  in
  let convert_to_grouped (grouped_explanations : derive_explanation list list)
    : grouped_derive_explanations list =
    let rec aux (acc : grouped_derive_explanations list)
        (grouped_explanations : derive_explanation list list) :
      grouped_derive_explanations list =
      match grouped_explanations with
      | [] -> List.rev acc
      | g :: gs ->
        let acc =
          match g with
          | [] -> acc
          | Nothing_to_explain :: _ -> Nothing_to_explain :: acc
          | Dont_know_how :: _ -> Dont_know_how :: acc
          | Rewrite _ :: _ -> convert_rewrite g :: acc
          | Combine_knowledge _ :: _ -> convert_combine_knowledge g @ acc
          | Gain_knowledge _ :: _ -> convert_gain_knowledge g @ acc
        in
        aux acc gs
    in
    aux [] grouped_explanations
  in
  let explanations =
    explanations |> uniquify_universal_var_names_derive_explanations
    |> List.filter (fun (x : derive_explanation) ->
        x <> Nothing_to_explain && x <> Dont_know_how )
  in
  let var_bindings = var_bindings_in_explanations explanations in
  List.iter
    (fun (k, v) ->
       Js_utils.console_log (Printf.sprintf "%s -> %s" k (expr_to_string v)) )
    (VarMap.bindings var_bindings);
  let grouped_explanations = group_into_list explanations in
  convert_to_grouped grouped_explanations

let explain_construction_chain (id : Analyzed_graph.id) (m : node_graph) :
  grouped_derive_explanations list =
  let open Analyzed_graph in
  let open Analyzed_expr in
  let get_chain (id : id) (m : node_graph) : id list =
    let rec aux (acc : id list) (id : id) : id list =
      let acc = id :: acc in
      match find_children id m with [] -> acc | c :: _ -> aux acc c
    in
    aux [] id
  in
  let explanations =
    List.map (fun id -> explain_construction_single id m) (get_chain id m)
  in
  group_derive_explanations explanations

let derive_explanation_to_string (explanation : derive_explanation) : string =
  let open Analyzed_expr in
  match explanation with
  | Nothing_to_explain -> "N/A"
  | Dont_know_how -> "N/A"
  | Rewrite rewrites ->
    Printf.sprintf
      "Attacker rewrites\n%s\n                                          "
      (String.concat "\n\n"
         (List.map
            (fun (e_from, e_to) ->
               Printf.sprintf "  %s\nto\n  %s" (expr_to_string e_from)
                 (expr_to_string e_to) )
            rewrites))
  | Combine_knowledge (srcs_from, es_gain) ->
    Printf.sprintf
      "From\n\
       %s\n\
       attacker knows\n\
       %s\n\
      \                                           "
      (String.concat "\n"
         (List.map
            (fun x -> Printf.sprintf "  %s" (info_source_to_string x))
            srcs_from))
      (String.concat "\n"
         (List.map
            (fun x -> Printf.sprintf "  %s" (expr_to_string x))
            es_gain))
  | Gain_knowledge (srcs_from, new_knowledge, old_knowledge) ->
    Printf.sprintf "From\n%s\nattacker learns\n%s\n"
      (String.concat "\n"
         (List.map
            (fun x -> Printf.sprintf "  %s" (info_source_to_string x))
            srcs_from))
      (* (String.concat "\n"
                                                                 *    (List.map
                                                                 *       (fun (x, _) -> Printf.sprintf "  %s" (expr_to_string x))
                                                                 *       old_knowledge
                                                                 *    )
                                                                 * ) *)
      (String.concat "\n"
         (List.map
            (fun (x, _) -> Printf.sprintf "  %s" (expr_to_string x))
            new_knowledge))

let grouped_derive_explanations_to_string
    (explanation : grouped_derive_explanations) : string =
  let open Analyzed_expr in
  match explanation with
  | Nothing_to_explain -> "Nothing to explain"
  | Dont_know_how -> "Don't know how to explain"
  | Rewrites buckets ->
    Printf.sprintf "%s\n"
      (String.concat "\n\n"
         (List.map
            (fun b ->
               Printf.sprintf "Attacker rewrites %s"
                 (String.concat " to\n"
                    (List.map Analyzed_expr.expr_to_string b)) )
            buckets))
  | Combine_knowledge (srcs_from, es_gain) ->
    Printf.sprintf
      "From\n\
       %s\n\
       attacker knows\n\
       %s\n\
      \                                           "
      (String.concat "\n"
         (List.map
            (fun x -> Printf.sprintf "  %s" (info_source_to_string x))
            srcs_from))
      (String.concat "\n"
         (List.map
            (fun x -> Printf.sprintf "  %s" (expr_to_string x))
            es_gain))
  | Gain_knowledge (srcs_from, es_gain) ->
    Printf.sprintf
      "From\n\
       %s\n\
       attacker knows\n\
       %s\n\
      \                                           "
      (String.concat "\n"
         (List.map
            (fun x -> Printf.sprintf "  %s" (info_source_to_string x))
            srcs_from))
      (String.concat "\n"
         (List.map
            (fun x -> Printf.sprintf "  %s" (expr_to_string x))
            es_gain))

let grouped_derive_explanations_list_to_string
    (explanations : grouped_derive_explanations list) : string =
  String.concat "\n"
    (List.map grouped_derive_explanations_to_string explanations)

let node_to_string_debug (id : Analyzed_graph.id) (node : node)
    (m : node_graph) : string =
  let open Analyzed_graph in
  match node with
  | Group -> "Group node"
  | Data data ->
    let expr_str = Analyzed_expr.expr_to_string_debug data.expr in
    let parents = find_parents id m in
    let children = find_children id m in
    Printf.sprintf
      "%s.\n\
      \   %s\n\
      \   [description    : %s]\n\
      \   [classification : %s]\n\
      \   [functions used : %s]\n\
      \   [parents        : %s]\n\
      \   [children       : %s]\n\
      \   [chain          : %s->%s]"
      id expr_str data.derive_descr
      (classification_to_string data.classification)
      (Misc_utils.join_with_comma
         (Analyzed_expr.get_function_names data.expr))
      (Misc_utils.join_with_comma parents)
      (Misc_utils.join_with_comma children)
      (let hd, _, _ = data.chain in
       hd)
      (let _, tl, _ = data.chain in
       tl)

let write_map_debug (out : out_channel) (m : node_graph) : unit =
  let open Analyzed_graph in
  linear_traverse ()
    (Full_traversal_pure
       (fun () id node m ->
          Printf.fprintf out "%s\n" (node_to_string_debug id node m) ))
    m
  |> ignore

let map_debug_string (m : node_graph) : string =
  let open Analyzed_graph in
  let acc, _ =
    linear_traverse []
      (Full_traversal_pure
         (fun acc id node m -> node_to_string_debug id node m :: acc))
      m
  in
  String.concat "\n" (List.rev acc)

let print_map_debug (m : node_graph) : unit =
  let open Analyzed_graph in
  linear_traverse ()
    (Full_traversal_pure
       (fun () id node m -> print_endline (node_to_string_debug id node m)))
    m
  |> ignore

let write_map_DAG (out : out_channel) (m : node_graph) : unit =
  let open Printf in
  let open Analyzed_graph in
  let write_node (out : out_channel) (id : id) (node : node) (m : node_graph) :
    unit =
    let children = find_children id m in
    List.iter (fun x -> fprintf out "%s --> %s;\n" id x) children;
    fprintf out "%s(\"" id;
    let data = unwrap_data node in
    let head, tail, _ = data.chain in
    if head <> tail then fprintf out "%s->%s" head tail
    else fprintf out "%s" id;
    fprintf out ". ";
    fprintf out "%s <br>" (Analyzed_expr.expr_to_string data.expr);
    fprintf out "%s"
      (String.capitalize_ascii (classification_to_string data.classification));
    fprintf out "\");\n"
  in
  (* setup code *)
  fprintf out "graph BT;\n";
  linear_traverse ()
    (Full_traversal_pure (fun () id node m -> write_node out id node m))
    m
  |> ignore

let print_map_DAG (m : node_graph) : unit = write_map_DAG stdout m

let lines_to_node_map (lines : Raw_line.line option list) : node_graph =
  node_list_to_map
    (List.map line_to_node_record
       (List.map Misc_utils.unwrap_opt
          (List.filter (function Some _ -> true | None -> false) lines)))

let process_string (input : string) : (node_graph, string) result =
  match File_parser.parse_refutation_proof_string input with
  | Ok x ->
    x |> lines_to_node_map
    (* |> Analyzed_graph.(filter (fun _id node _m ->
     *     match node with
     *     | Data x -> List.mem x.classification
     *                   [InitialKnowledge;
     *                    Knowledge;
     *                    NegatedGoal;
     *                    Contradiction]
     *     | Group  -> true
     *   )) *)
    |> fun x -> Ok x
  | Error msg -> Error msg

let collect_steps (m : node_graph) : Protocol_step.t list =
  let open Protocol_step in
  let open Analyzed_graph in
  (* let op (l : Protocol_step.t list) (_id : Analyzed_graph.id) (node : node) (_m : node_graph) : Protocol_step.t list =
   *   let step = Protocol_step.node_to_steps node in
   *   step @ l
   * in *)
  let paths_to_root (id : id) (m : node_graph) : id list list =
    let rec aux (cur_path : id list) id m =
      let children = find_children id m in
      match children with
      | [] -> [List.rev (id :: cur_path)]
      | l ->
        let cur_path = id :: cur_path in
        List.concat (List.map (fun c -> aux cur_path c m) l)
    in
    aux [] id m
  in
  let steps_reachable (path : id list) (m : node_graph) : Protocol_step.t list
    =
    (* let find_steps_at_top  (id : id) (m : node_graph) : Protocol_step.t list =
     *   let rec aux (acc : Protocol_step.t list) id m : Protocol_step.t list =
     *     match find_parents id m with
     *     | [] -> (\* reached top, check classification *\)
     *       let node = find_node id m in
     *       let classification = (unwrap_data node).classification in
     *       if classification = ProtocolStep || classification = InteractiveProtocolStep then
     *         (Protocol_step.node_to_steps node) @ acc
     *       else
     *         acc
     *     | ps ->
     *       List.fold_left (fun acc parent -> aux acc parent m) acc ps
     *   in
     *   aux [] id m
     * in *)
    let find_steps_at_top (acc : Protocol_step.t list) (id : id) (_node : node)
        (m : node_graph) =
      match find_parents id m with
      | [] ->
        (* reached top, check classification *)
        let node = find_node id m in
        let classification = (unwrap_data node).classification in
        if
          classification = ProtocolStep
          || classification = InteractiveProtocolStep
        then
          let steps = Protocol_step.node_to_steps node in
          steps @ List.filter (fun s -> not (List.mem s steps)) acc
        else acc
      | _ -> acc
    in
    let rec aux (acc : Protocol_step.t list) (last_id : id option)
        (path : id list) (m : node_graph) =
      match path with
      | [] -> List.rev acc
      | x :: xs ->
        (* check if any other path upward (i.e. a turn) to take *)
        let choices_upward =
          List.filter
            (fun x ->
               match last_id with
               | None -> true
               | Some last_id -> x <> last_id )
            (find_parents x m)
        in
        (* collect steps reachable from the paths upward *)
        let acc =
          List.fold_left
            (fun acc parent ->
               let r, _ =
                 bfs_traverse parent acc Bottom_to_top
                   (Full_traversal_pure find_steps_at_top) m
               in
               r )
            acc choices_upward
        in
        aux acc (Some x) xs m
    in
    aux [] None path m
  in
  (* get all step nodes *)
  let step_nodes =
    to_assoc_list
      (filter
         (fun _id n _m ->
            (unwrap_data n).classification = ProtocolStep
            || (unwrap_data n).classification = InteractiveProtocolStep )
         m)
  in
  let paths =
    List.concat (List.map (fun (id, _) -> paths_to_root id m) step_nodes)
  in
  let steps =
    List.fold_left
      (fun acc l ->
         Js_utils.console_log
           (Printf.sprintf "list : [%s]"
              (String.concat ", "
                 (List.map
                    (fun x ->
                       Printf.sprintf "%s.%d"
                         (match x.proc_name with None -> "" | Some x -> x)
                         x.step_num )
                    l)));
         Misc_utils.zip l acc )
      []
      (List.map (fun path -> steps_reachable path m) paths)
  in
  let steps =
    List.fold_left
      (* if there are multiple occurances of a step, only keep the later ones *)
      (fun acc s -> if List.mem s acc then acc else s :: acc )
      [] (List.rev steps)
  in
  (* let steps = List.hd (List.map (fun path -> steps_reachable path m) paths) in *)
  (* let immediate_roots = Analyzed_graph.find_parents bottom_id m in
   * let steps = List.fold_left
   *     (fun acc id ->
   *        let (r, _) = Analyzed_graph.bfs_traverse id [] Bottom_to_top (Full_traversal_pure op) m in
   *        Misc_utils.zip (List.rev r) acc
   *     )
   *     []
   *     immediate_roots
   * in *)
  let grouped_steps =
    Misc_utils.group_list (fun s1 s2 -> s1.proc_name = s2.proc_name) steps
  in
  List.concat
    (List.map
       (fun l -> List.sort (fun s1 s2 -> compare s1.step_num s2.step_num) l)
       grouped_steps)
