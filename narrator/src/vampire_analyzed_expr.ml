open Expr_components
open Printf
open Misc_utils

type variable = bound * identifier

type expr =
  | Variable of variable
  | Pred of string * expr
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

module VarSet = Set.Make (struct
    type t = identifier

    let compare = compare
  end)

let is_quantified (ctx : context list) (e : identifier) : quantifier option =
  let rec aux (ctx : context list) (e : identifier) : quantifier option =
    match ctx with
    | [] ->
      None
    | x :: xs ->
      if List.mem e x.quantified_idents then Some x.quantifier else aux xs e
  in
  aux ctx e

let raw_expr_to_analyzed_expr (raw : Vampire_raw_expr.expr) : expr =
  let rec aux (ctx : context list) (raw : Vampire_raw_expr.expr) : expr =
    match raw with
    | Variable ident -> (
        match is_quantified ctx ident with
        | None ->
          Variable (Unsure, ident)
        | Some Exists ->
          Variable (Existential, ident)
        | Some Forall ->
          Variable (Universal, ident) )
    | Pred (name, param) ->
      Pred (name, aux ctx param)
    | Function (name, params) ->
      Function (name, List.map (aux ctx) params)
    | UnaryOp (op, e) ->
      UnaryOp (op, aux ctx e)
    | BinaryOp (op, l, r) ->
      BinaryOp (op, aux ctx l, aux ctx r)
    | Quantified (q, idents, e) ->
      let new_ctx = {quantifier = q; quantified_idents = idents} in
      Quantified (q, idents, aux (new_ctx :: ctx) e)
    | False ->
      False
    | InsertedF formulas ->
      InsertedF formulas
  in
  aux [] raw

let rec expr_to_string_debug (e : expr) : string =
  match e with
  | Variable (Free, x) ->
    sprintf "%s[free]" x
  | Variable (Universal, x) ->
    sprintf "%s[U]" x
  | Variable (Existential, x) ->
    sprintf "%s[E]" x
  | Variable (Unsure, x) ->
    sprintf "%s[unsure]" x
  | Pred (name, param) ->
    sprintf "%s(%s)" name (expr_to_string_debug param)
  | Function (name, params) ->
    sprintf "%s(%s)" name
      (join_with_comma (List.map expr_to_string_debug params))
  | UnaryOp (op, expr) ->
    sprintf "%s(%s)" (unary_op_to_string op) (expr_to_string_debug expr)
  | BinaryOp (op, l, r) ->
    sprintf "(%s) %s (%s)" (expr_to_string_debug l) (binary_op_to_string op)
      (expr_to_string_debug r)
  | Quantified (q, idents, e) ->
    sprintf "%s [%s] : %s" (quantifier_to_string q) (join_with_comma idents)
      (expr_to_string_debug e)
  | False ->
    "$false"
  | InsertedF l ->
    String.concat "" (List.map string_of_int l)

let rec expr_to_string (e : expr) : string =
  match e with
  | Variable (Free, x) ->
    sprintf "%s" x
  | Variable (Universal, x) ->
    sprintf "%s" x
  | Variable (Existential, x) ->
    sprintf "%s" x
  | Variable (Unsure, x) ->
    sprintf "%s" x
  | Pred (name, param) ->
    sprintf "%s(%s)" name (expr_to_string param)
  | Function (name, params) ->
    sprintf "%s(%s)" name (join_with_comma (List.map expr_to_string params))
  | UnaryOp (op, expr) ->
    sprintf "%s%s" (unary_op_to_string op)
      ( match expr with
        | Variable _ as e ->
          expr_to_string e
        | Function _ as e ->
          expr_to_string e
        | UnaryOp _ as e ->
          expr_to_string e
        | _ as e ->
          sprintf "(%s)" (expr_to_string e) )
  | BinaryOp (op, l, r) -> (
      match op with
      (* | And | Or | Imply | Left_imply | Not_or | Not_and -> *)
      | And | Or | Imply | Neq ->
        sprintf "%s %s %s"
          ( match l with
            | Variable _ as e ->
              expr_to_string e
            | Function _ as e ->
              expr_to_string e
            | UnaryOp _ as e ->
              expr_to_string e
            | _ as e ->
              sprintf "(%s)" (expr_to_string e) )
          (binary_op_to_string op)
          ( match r with
            | Variable _ as e ->
              expr_to_string e
            | Function _ as e ->
              expr_to_string e
            | UnaryOp _ as e ->
              expr_to_string e
            | _ as e ->
              sprintf "(%s)" (expr_to_string e) )
      | Eq | Iff | Subsume ->
        sprintf "%s %s %s" (expr_to_string l) (binary_op_to_string op)
          (expr_to_string r) )
  | Quantified (q, idents, e) ->
    sprintf "%s [%s] : %s" (quantifier_to_string q) (join_with_comma idents)
      (expr_to_string e)
  | False ->
    "$false"
  | InsertedF l ->
    String.concat "" (List.map string_of_int l)

let get_bound (e : expr) : (string * bound) list =
  let rec aux (e : expr) acc : (string * bound) list =
    match e with
    | Variable (b, v) ->
      (v, b) :: acc
    | Pred (_, e) ->
      aux e acc
    | Function (_, params) ->
      List.fold_left (fun x y -> aux y x) acc params
    | UnaryOp (_, e) ->
      aux e acc
    | BinaryOp (_, l, r) ->
      aux l (aux r acc)
    | Quantified (_, _, e) ->
      aux e acc
    | False ->
      acc
    | InsertedF _ ->
      acc
  in
  aux e []

let mark_var_bound (e : expr) : expr =
  let rec aux (e : expr) : expr =
    match e with
    | Variable (_, v) ->
      let bound =
        if Core_kernel.String.substr_index ~pattern:"name_" v = Some 0 then
          Free
        else if Core_kernel.String.substr_index ~pattern:"constr_" v = Some 0
        then Free
        else if Core_kernel.String.substr_index ~pattern:"X" v = Some 0 then
          Universal
        else Unsure
      in
      Variable (bound, v)
    | Pred (name, param) ->
      Pred (name, aux param)
    | Function (name, params) ->
      Function (name, List.map aux params)
    | UnaryOp (op, e) ->
      UnaryOp (op, aux e)
    | BinaryOp (op, l, r) ->
      BinaryOp (op, aux l, aux r)
    | Quantified (q, idents, e) ->
      Quantified (q, idents, aux e)
    | False ->
      False
    | InsertedF formulas ->
      InsertedF formulas
  in
  aux e

(* let mark_if_unsure (bound : bound) (e : expr) : expr =
 *   let rec aux (e : expr) : expr =
 *     match e with
 *     | Variable (Unsure, v) ->
 *       Variable (bound, v)
 *     | Variable (Free, v) ->
 *       Variable (Free, v)
 *     | Variable (Universal, v) ->
 *       Variable (Universal, v)
 *     | Variable (Existential, v) ->
 *       Variable (Existential, v)
 *     | Pred (name, param) ->
 *       Pred (name, aux param)
 *     | Function (name, params) ->
 *       Function (name, List.map aux params)
 *     | UnaryOp (op, e) ->
 *       UnaryOp (op, aux e)
 *     | BinaryOp (op, l, r) ->
 *       BinaryOp (op, aux l, aux r)
 *     | Quantified (q, idents, e) ->
 *       Quantified (q, idents, aux e)
 *     | False ->
 *       False
 *     | InsertedF formulas ->
 *       InsertedF formulas
 *   in
 *   aux e *)

let update_bound (e : expr) (changes : (string * bound) list) : expr =
  let rec aux (e : expr) : expr =
    match e with
    | Variable (b, v) -> (
        match List.assoc_opt v changes with
        | None ->
          Variable (b, v)
        | Some new_b -> (
            match (new_b, b) with
            | x, Unsure ->
              Variable (x, v)
            | _, _h ->
              Variable (b, v) (* only update when unsure *) ) )
    | Pred (name, e) ->
      Pred (name, aux e)
    | Function (name, params) ->
      Function (name, List.map aux params)
    | UnaryOp (op, e) ->
      UnaryOp (op, aux e)
    | BinaryOp (op, l, r) ->
      BinaryOp (op, aux l, aux r)
    | Quantified (q, idents, e) ->
      Quantified (q, idents, aux e)
    | False ->
      False
    | InsertedF formulas ->
      InsertedF formulas
  in
  aux e

let get_function_names (e : expr) : string list =
  let rec aux (e : expr) : string list =
    match e with
    | Variable _ ->
      []
    | Pred (name, param) ->
      name :: aux param
    | Function (name, params) ->
      name :: List.concat (List.map aux params)
    | UnaryOp (_, e) ->
      aux e
    | BinaryOp (_, e1, e2) ->
      List.append (aux e1) (aux e2)
    | Quantified (_, _, e) ->
      aux e
    | False ->
      []
    | InsertedF _ ->
      []
  in
  List.sort_uniq compare (aux e)

let get_vars ?(bound : bound option) (e : expr) : string list =
  let rec aux (e : expr) : string list =
    match e with
    | Variable (b, name) -> (
        match bound with
        | Some bound ->
          if b = bound then [name] else []
        | None ->
          [name] )
    | Pred (_, param) ->
      aux param
    | Function (_, params) ->
      List.concat (List.map aux params)
    | UnaryOp (_, e) ->
      aux e
    | BinaryOp (_, e1, e2) ->
      List.append (aux e1) (aux e2)
    | Quantified (_, _, e) ->
      aux e
    | False ->
      []
    | InsertedF _ ->
      []
  in
  List.sort_uniq compare (aux e)

let has_universal_var (e : expr) : bool =
  let rec aux (e : expr) : bool =
    match e with
    | Variable (Unsure, _) ->
      raise Unexpected_unsure_var
    | Variable (Free, _) ->
      false
    | Variable (Existential, _) ->
      false
    | Variable (Universal, _) ->
      true
    | Pred (_, e) ->
      aux e
    | Function (_, es) ->
      aux_list es
    | UnaryOp (_, e) ->
      aux e
    | BinaryOp (_, e1, e2) ->
      aux e1 || aux e2
    | Quantified (_, _, e) ->
      aux e
    | False ->
      false
    | InsertedF _ ->
      false
  and aux_list (es : expr list) : bool =
    List.fold_left (fun res e -> res || aux e) false es
  in
  aux e

let negate (e : expr) : expr =
  let rec aux (e : expr) : expr =
    match e with
    | UnaryOp (Not, e) ->
      e
    | Variable _ ->
      UnaryOp (Not, e)
    | Pred _ ->
      UnaryOp (Not, e)
    | Function _ ->
      UnaryOp (Not, e)
    | BinaryOp (And, e1, e2) ->
      BinaryOp (Or, aux e1, aux e2)
    | BinaryOp (Or, e1, e2) ->
      BinaryOp (And, aux e1, aux e2)
    | BinaryOp (Eq, e1, e2) ->
      BinaryOp (Neq, e1, e2)
    | BinaryOp (Neq, e1, e2) ->
      BinaryOp (Eq, e1, e2)
    | BinaryOp (Iff, e1, e2) ->
      BinaryOp
        ( Or
        , BinaryOp (And, UnaryOp (Not, e1), e2)
        , BinaryOp (And, e1, UnaryOp (Not, e2)) )
    | BinaryOp (Imply, e1, e2) ->
      BinaryOp (And, e1, aux e2)
    | BinaryOp (Subsume, _, _) ->
      UnaryOp (Not, e)
    | Quantified (Forall, vars, e) ->
      Quantified (Exists, vars, aux e)
    | Quantified (Exists, vars, e) ->
      Quantified (Forall, vars, aux e)
    | False ->
      UnaryOp (Not, False)
    | InsertedF _ ->
      UnaryOp (Not, e)
  in
  aux e

let strip_pred_attacker (e : expr) : expr =
  match e with Pred ("attacker", e) -> e | _ -> e

let strip_not (e : expr) : expr =
  match e with UnaryOp (Not, e) -> e | _ as e -> e

let strip_att (e : expr) : expr =
  match e with Pred ("attacker", e) -> e | _ as e -> e

let strip_quant (e : expr) : expr =
  match e with Quantified (_, _, e) -> e | _ -> e

let get_function_args (e : expr) : expr list =
  match e with Function (_, es) -> es | _ -> []

let remove_subsumptions (e : expr) : expr =
  let rec aux (e : expr) : expr =
    match e with
    | Variable _ ->
      e
    | Pred (p, arg) ->
      Pred (p, aux arg)
    | Function (f, args) ->
      Function (f, List.map aux args)
    | UnaryOp (op, e) ->
      UnaryOp (op, aux e)
    | BinaryOp (Subsume, e, _) ->
      e
    | BinaryOp (op, e1, e2) ->
      BinaryOp (op, aux e1, aux e2)
    | Quantified (q, vars, e) ->
      Quantified (q, vars, aux e)
    | False ->
      e
    | InsertedF _ ->
      e
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
    | Variable _ ->
      acc
    | Pred (_, e) ->
      aux acc e
    | Function (_, es) ->
      aux_list acc es
    | UnaryOp (_, e) ->
      aux acc e
    | BinaryOp (_, e1, e2) ->
      aux_list acc [e1; e2]
    | Quantified (_, _, e) ->
      aux acc e
    | False ->
      acc
    | InsertedF _ ->
      acc
  and aux_list (acc : int) (es : expr list) : int =
    List.fold_left (fun acc e -> aux acc e) acc es
  in
  aux 0 e

let similarity (e1 : expr) (e2 : expr) : float =
  let rec aux (e1 : expr) (e2 : expr) : int =
    match (e1, e2) with
    | Variable (Free, n1), Variable (Free, n2) ->
      if n1 = n2 then 2 else 0
    | Variable (Universal, _), v ->
      1 + length v
    | (_ as v), Variable (Universal, _) ->
      length v
    | Variable (Existential, _), _ ->
      raise Unexpected_existential_var
    | _, Variable (Existential, _) ->
      raise Unexpected_existential_var
    | Pred (n1, e1), Pred (n2, e2) ->
      if n1 = n2 then 2 + aux e1 e2 else 0
    | Function (n1, es1), Function (n2, es2) ->
      if n1 = n2 then 2 + aux_list es1 es2 else 0
    | UnaryOp (op1, e1), UnaryOp (op2, e2) ->
      if op1 = op2 then 2 + aux e1 e2 else 0
    | BinaryOp (op1, e1a, e1b), BinaryOp (op2, e2a, e2b) ->
      if op1 = op2 then 2 + aux_list [e1a; e1b] [e2a; e2b] else 0
    | Quantified (_, _, e1), Quantified (_, _, e2) ->
      aux e1 e2
    | False, False ->
      2
    | InsertedF n1, InsertedF n2 ->
      if n1 = n2 then 2 else 0
    | _, _ ->
      0
  and aux_list (es1 : expr list) (es2 : expr list) : int =
    List.fold_left2 (fun acc e1 e2 -> acc + aux e1 e2) 0 es1 es2
  in
  let total_matches = aux e1 e2 in
  float_of_int total_matches /. float_of_int (length e1 + length e2)

module PatternMatch = struct
  let pattern_matches ~(pattern : expr) (expr : expr) : bool =
    let rec aux (pattern : expr) (expr : expr) : bool =
      match (pattern, expr) with
      | Variable (Unsure, _), _ ->
        raise Unexpected_unsure_var
      | _, Variable (Unsure, _) ->
        raise Unexpected_unsure_var
      | Variable (Existential, _), _ ->
        raise Unexpected_existential_var
      | _, Variable (Existential, _) ->
        raise Unexpected_existential_var
      | Quantified (Exists, _, _), _ ->
        raise Unexpected_exists_quantifier
      | _, Quantified (Exists, _, _) ->
        raise Unexpected_exists_quantifier
      | (Variable (Free, _) as v1), (Variable (Free, _) as v2) ->
        v1 = v2
      | Variable (Universal, _), _ ->
        true
      | Pred (p1, e1), Pred (p2, e2) ->
        p1 = p2 && aux e1 e2
      | Function (f1, es1), Function (f2, es2) ->
        f1 = f2 && List.length es1 = List.length es2 && aux_list es1 es2
      | UnaryOp (op1, e1), UnaryOp (op2, e2) ->
        op1 = op2 && aux e1 e2
      | BinaryOp (op1, e1a, e1b), BinaryOp (op2, e2a, e2b) ->
        op1 = op2 && aux e1a e2a && aux e1b e2b
      | Quantified (Forall, _, e1), Quantified (Forall, _, e2) ->
        aux e1 e2
      | Quantified (Forall, _, e1), (_ as e2) ->
        aux e1 e2
      | False, False ->
        true
      | InsertedF l1, InsertedF l2 ->
        l1 = l2
      | _ ->
        false
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
      | Variable _ ->
        s
      | Pred (_, e) ->
        aux pattern e s
      | Function (_, es) ->
        aux_list pattern es s
      | UnaryOp (_, e) ->
        aux pattern e s
      | BinaryOp (_, e1, e2) ->
        aux_list pattern [e1; e2] s
      | Quantified (_, _, e) ->
        aux pattern e s
      | False ->
        s
      | InsertedF _ ->
        s
    and aux_list (pattern : expr) (es : expr list) (s : ExprSet.t) : ExprSet.t
      =
      List.fold_left (fun s e -> aux pattern e s) s es
    in
    ExprSet.elements (aux pattern expr s)

  let record_alias name1 name2 (aliases : VarSet.t list) : VarSet.t list =
    let rec aux recorded acc name1 name2 aliases =
      match (recorded, aliases) with
      | true, [] ->
        acc
      | false, [] ->
        (VarSet.empty |> VarSet.add name1 |> VarSet.add name2) :: acc
      | true, s :: ss ->
        aux true (s :: acc) name1 name2 ss
      | false, s :: ss ->
        let recorded, s =
          if VarSet.mem name1 s || VarSet.mem name2 s then
            (true, s |> VarSet.add name1 |> VarSet.add name2)
          else (false, s)
        in
        aux recorded (s :: acc) name1 name2 ss
    in
    aux false [] name1 name2 aliases

  let var_bindings_in_pattern_match ?(m : expr VarMap.t = VarMap.empty)
      ?(aliases : VarSet.t list = []) ~(pattern : expr) (expr : expr) :
    expr VarMap.t * VarSet.t list =
    let rec aux (pattern : expr) (expr : expr) (m : expr VarMap.t)
        (aliases : VarSet.t list) : expr VarMap.t * VarSet.t list =
      match (pattern, expr) with
      | Variable (Free, _), _ ->
        (m, aliases)
      | Variable (_, name1), (Variable (_, name2) as v) ->
        let aliases = record_alias name1 name2 aliases in
        (VarMap.add name1 v m, aliases)
      | Variable (Universal, name), (_ as v) ->
        (VarMap.add name v m, aliases)
      | Variable (Existential, _), _ ->
        raise Unexpected_existential_var
      | Pred (_, e1), Pred (_, e2) ->
        aux e1 e2 m aliases
      | Function (_, es1), Function (_, es2) ->
        aux_list es1 es2 m aliases
      | UnaryOp (_, e1), UnaryOp (_, e2) ->
        aux e1 e2 m aliases
      | BinaryOp (_, e1a, e1b), BinaryOp (_, e2a, e2b) ->
        aux_list [e1a; e1b] [e2a; e2b] m aliases
      | Quantified (_, _, e1), Quantified (_, _, e2) ->
        aux e1 e2 m aliases
      | False, False ->
        (m, aliases)
      | InsertedF _, InsertedF _ ->
        (m, aliases)
      | _ ->
        raise Unmatching_structure
    and aux_list (es1 : expr list) (es2 : expr list) (m : expr VarMap.t)
        (aliases : VarSet.t list) : expr VarMap.t * VarSet.t list =
      List.fold_left2
        (fun (m, aliases) e1 e2 -> aux e1 e2 m aliases)
        (m, aliases) es1 es2
    in
    if pattern_matches ~pattern expr then aux pattern expr m aliases
    else (m, [])

  (* let var_bindings_compatible ~(smaller : expr VarMap.t)
   *     ~(larger : expr VarMap.t) : bool =
   *   let keys = List.map (fun (k, _) -> k) (VarMap.bindings smaller) in
   *   List.fold_left
   *     (fun res k ->
   *        res
   *        &&
   *        match VarMap.find_opt k larger with
   *        | None ->
   *          true
   *        | Some c ->
   *          VarMap.find k smaller = c)
   *     true keys *)
end

module Rename : sig
  val rename_universal_var_name : string -> string -> expr -> expr

  val rename_universal_var_names : (string * string) list -> expr -> expr
end = struct
  let rename_universal_var_name (original : string) (replacement : string)
      (e : expr) : expr =
    let rec aux (original : string) (replacement : string) (e : expr) : expr =
      match e with
      | Variable (Universal, name) ->
        Variable (Universal, if name = original then replacement else name)
      | Variable _ as e ->
        e
      | Pred (name, e) ->
        Pred (name, aux original replacement e)
      | Function (name, es) ->
        Function (name, aux_list original replacement es)
      | UnaryOp (op, e) ->
        UnaryOp (op, aux original replacement e)
      | BinaryOp (op, e1, e2) ->
        BinaryOp
          (op, aux original replacement e1, aux original replacement e2)
      | Quantified (q, ids, e) ->
        Quantified (q, ids, aux original replacement e)
      | False ->
        False
      | InsertedF _ as e ->
        e
    and aux_list (original : string) (replacement : string) (es : expr list) :
      expr list =
      List.map (aux original replacement) es
    in
    aux original replacement e

  let rename_universal_var_names (l : (string * string) list) (e : expr) : expr
    =
    let rec aux (l : (string * string) list) (e : expr) : expr =
      match l with
      | [] ->
        e
      | (name, replacement) :: l ->
        aux l (rename_universal_var_name name replacement e)
    in
    aux l e
end

module Rewrite : sig
  val rewrite_w_var_binding_map : expr VarMap.t -> expr -> expr
end = struct
  let rewrite_w_var_binding_map (m : expr VarMap.t) expr =
    let rec aux m e =
      match e with
      | Variable (_, name) -> (
          match VarMap.find_opt name m with Some e -> e | None -> e )
      | Pred (name, e) ->
        Pred (name, aux m e)
      | Function (name, args) ->
        Function (name, aux_list m args)
      | UnaryOp (op, e) ->
        UnaryOp (op, aux m e)
      | BinaryOp (op, l, r) ->
        BinaryOp (op, aux m l, aux m r)
      | Quantified (q, vars, e) ->
        Quantified (q, vars, aux m e)
      | False ->
        e
      | InsertedF _ ->
        e
    and aux_list m es = List.map (aux m) es in
    aux m expr
end

module BruteForceBase = struct
  let all_combinations (es1 : 'a list) (es2 : 'b list) : ('a * 'b) list =
    let rec aux (acc : ('a * 'b) list) (es1 : 'a list) (es : 'b list) :
      ('a * 'b) list =
      match es1 with
      | [] ->
        acc
      | p :: ps ->
        let acc = List.map (fun e -> (p, e)) es @ acc in
        aux acc ps es
    in
    aux [] es1 es2
end

module BruteForceClauseSetPairExprMatches : sig
  val best_solution : expr list -> expr list -> expr ExprMap.t
end = struct
  let group_by_exprs (combinations : (expr * expr) list) : expr list ExprMap.t
    =
    let rec aux (m : expr list ExprMap.t) (combinations : (expr * expr) list) :
      expr list ExprMap.t =
      match combinations with
      | [] ->
        m
      | (p, e) :: cs ->
        let m =
          match ExprMap.find_opt p m with
          | None ->
            ExprMap.add p [e] m
          | Some l ->
            ExprMap.add p (e :: l) m
        in
        aux m cs
    in
    aux ExprMap.empty combinations

  let generate_possible_solutions (m : expr list ExprMap.t) :
    expr ExprMap.t list =
    let rec aux (keys : expr list) (m : expr list ExprMap.t)
        (cur : expr ExprMap.t) : expr ExprMap.t list =
      match keys with
      | [] ->
        [cur]
      | k :: ks ->
        let vals = ExprMap.find k m in
        List.concat
          (List.map
             (fun v ->
                let cur = ExprMap.add k v cur in
                aux ks m cur)
             vals)
    in
    let keys = List.map (fun (k, _) -> k) (ExprMap.bindings m) in
    aux keys m ExprMap.empty

  let filter_by_non_overlapping_exprs_expressions (l : expr ExprMap.t list) :
    expr ExprMap.t list =
    let no_overlaps (m : expr ExprMap.t) : bool =
      let rec aux (keys : expr list) (m : expr ExprMap.t)
          (exprs2_used : ExprSet.t) : bool =
        match keys with
        | [] ->
          true
        | pat :: ks ->
          let expr = ExprMap.find pat m in
          (not (ExprSet.mem expr exprs2_used))
          && aux ks m (ExprSet.add expr exprs2_used)
      in
      let keys = List.map (fun (k, _) -> k) (ExprMap.bindings m) in
      aux keys m ExprSet.empty
    in
    List.filter (fun m -> no_overlaps m) l

  (* let filter_by_compatible_var_bindings (solutions : expr ExprMap.t list) :
   *   expr ExprMap.t list =
   *   let open PatternMatch in
   *   let no_overlaps (m : expr ExprMap.t) : bool =
   *     let rec aux (keys : expr list) (var_bindings : expr VarMap.t)
   *         (m : expr ExprMap.t) : bool =
   *       match keys with
   *       | [] ->
   *         true
   *       | pat :: ks ->
   *         let expr = ExprMap.find pat m in
   *         let bindings = var_bindings_in_pattern_match ~pattern:pat expr in
   *         var_bindings_compatible ~smaller:bindings ~larger:var_bindings
   *         &&
   *         let var_bindings =
   *           var_bindings_in_pattern_match ~m:var_bindings ~pattern:pat expr
   *         in
   *         aux ks var_bindings m
   *     in
   *     let keys = List.map (fun (k, _) -> k) (ExprMap.bindings m) in
   *     aux keys VarMap.empty m
   *   in
   *   List.filter (fun m -> no_overlaps m) solutions *)

  let solution_score (m : expr ExprMap.t) : float =
    let rec aux (keys : expr list) (score_acc : float) (m : expr ExprMap.t) :
      float =
      match keys with
      | [] ->
        score_acc
      | pat :: ks ->
        let expr = ExprMap.find pat m in
        (* Js_utils.console_log (Printf.sprintf "similarity score of %s -- %s is %f" (expr_to_string pat) (expr_to_string expr) (similarity pat expr)); *)
        let score_acc = similarity pat expr +. score_acc in
        aux ks score_acc m
    in
    let keys = List.map (fun (k, _) -> k) (ExprMap.bindings m) in
    aux keys 0.0 m

  let sort_solutions_by_score_descending (solutions : expr ExprMap.t list) :
    expr ExprMap.t list =
    List.sort
      (fun m1 m2 -> compare (solution_score m2) (solution_score m1))
      solutions

  let compute_solutions_score_descending exprs1 exprs2 =
    BruteForceBase.all_combinations exprs1 exprs2
    |> group_by_exprs |> generate_possible_solutions
    |> filter_by_non_overlapping_exprs_expressions
    (* |> filter_by_compatible_var_bindings *)
    |> sort_solutions_by_score_descending

  let best_solution exprs1 exprs2 : expr ExprMap.t =
    let solutions = compute_solutions_score_descending exprs1 exprs2 in
    (* List.iteri (fun i m ->
     *     Js_utils.console_log (Printf.sprintf "Solution %d" i);
     *     ExprMap.iter (fun k v ->
     *         Js_utils.console_log (Printf.sprintf "k : %s" (expr_to_string k));
     *         Js_utils.console_log (Printf.sprintf "v : %s" (expr_to_string v));
     *       ) m;
     *   ) solutions; *)
    List.hd solutions
end

module BruteForceClauseSetPairVarBindings : sig
  val best_solution : expr list -> expr list -> expr VarMap.t * VarSet.t list
end = struct
  let best_solution exprs1 exprs2 =
    let m = BruteForceClauseSetPairExprMatches.best_solution exprs1 exprs2 in
    ExprMap.fold
      (fun pattern e (acc, aliases) ->
         PatternMatch.var_bindings_in_pattern_match ~m:acc ~aliases ~pattern e)
      m (VarMap.empty, [])
end

module BruteForceEquationVarBindings : sig
  val best_solution : eq:expr -> expr -> expr -> expr VarMap.t * VarSet.t list
end = struct
  let possible_var_bindings pattern expr =
    let universal_vars = get_vars ~bound:Universal pattern in
    PatternMatch.pattern_search ~pattern expr
    |> List.map (fun e ->
        PatternMatch.var_bindings_in_pattern_match ~pattern e)
    |> List.filter (fun (m, _aliases) ->
        List.for_all (fun k -> VarMap.mem k m) universal_vars)

  let gen_valid_combinations ~l_pattern ~r_pattern ~l_expr ~r_expr =
    let var_bindings_l_pat_on_l_e = possible_var_bindings l_pattern l_expr in
    let var_bindings_r_pat_on_r_e = possible_var_bindings r_pattern r_expr in
    BruteForceBase.all_combinations var_bindings_l_pat_on_l_e
      var_bindings_r_pat_on_r_e
    (* |> List.filter (fun ((m1, _), (m2, _)) ->
     *     VarMap.equal (fun a b -> compare a b = 0) m1 m2) *)
    |> List.map (fun (m, _) -> m)

  let score var_map expr1 expr2 =
    let expr1 = Rewrite.rewrite_w_var_binding_map var_map expr1 in
    let expr2 = Rewrite.rewrite_w_var_binding_map var_map expr2 in
    similarity expr1 expr2

  let compute_solutions_score_descending eq l_expr r_expr =
    match eq with
    | BinaryOp (Eq, l_pattern, r_pattern) ->
      let var_bindings_ll_rr =
        gen_valid_combinations ~l_pattern ~r_pattern ~l_expr ~r_expr
        |> List.map (fun (m, aliases) -> (score m l_expr r_expr, m, aliases))
        |> List.sort (fun (score1, _, _) (score2, _, _) ->
            compare score2 score1)
      in
      let var_bindings_lr_rl =
        gen_valid_combinations ~l_pattern ~r_pattern ~l_expr:r_expr
          ~r_expr:l_expr
        |> List.map (fun (m, aliases) -> (score m l_expr r_expr, m, aliases))
        |> List.sort (fun (score1, _, _) (score2, _, _) ->
            compare score2 score1)
      in
      List.merge
        (fun (score1, _, _) (score2, _, _) -> compare score2 score1)
        var_bindings_ll_rr var_bindings_lr_rl
      |> List.map (fun (_, m, aliases) -> (m, aliases))
    | _ ->
      failwith "Unexpected pattern"

  let best_solution ~eq l_expr r_expr =
    let solutions = compute_solutions_score_descending eq l_expr r_expr in
    (* List.iteri (fun i (m, aliases) ->
     *     Js_utils.console_log (Printf.sprintf "Solution %d" i);
     *     VarMap.iter (fun k v ->
     *         Js_utils.console_log (Printf.sprintf "k : %s" k);
     *         Js_utils.console_log (Printf.sprintf "v : %s" (expr_to_string v));
     *       ) m;
     *     List.iter
     *       (fun s ->
     *          let same = s |> VarSet.to_seq |> List.of_seq in
     *          Js_utils.console_log
     *            (Printf.sprintf "Aliases : %s" (String.concat ", " same));
     *       ) aliases;
     *   ) solutions; *)
    List.hd solutions
end

let universal_var_names (e : expr) : string list =
  let rec aux (e : expr) : string list =
    match e with
    | Variable (Universal, name) ->
      [name]
    | Variable _ ->
      []
    | Pred (_, e) ->
      aux e
    | Function (_, es) ->
      aux_list es
    | UnaryOp (_, e) ->
      aux e
    | BinaryOp (_, e1, e2) ->
      aux e1 @ aux e2
    | Quantified (_, _, e) ->
      aux e
    | False ->
      []
    | InsertedF _ ->
      []
  and aux_list (es : expr list) : string list =
    List.concat (List.map aux es)
  in
  List.sort_uniq compare (aux e)

let uniquify_universal_var_names_clause_sets (prefix : string)
    (ess : expr list list) : expr list list =
  let rec aux (gen_id : unit -> string) (acc : expr list list)
      (ess : expr list list) : expr list list =
    match ess with
    | [] ->
      List.rev acc
    | es :: ess ->
      let names =
        List.sort_uniq compare
          (List.concat (List.map universal_var_names es))
      in
      let name_map = List.map (fun n -> (n, gen_id ())) names in
      let res =
        List.map (fun e -> Rename.rename_universal_var_names name_map e) es
      in
      aux gen_id (res :: acc) ess
  in
  let gen_id = make_gen_string_id ~prefix in
  aux gen_id [] ess

let uniquify_universal_var_names_generic
    ~(replace_id : string -> string -> 'a -> 'a) ~(get_exprs : 'a -> expr list)
    (prefix : string) (xs : 'a list) : 'a list =
  let rec aux (gen_id : unit -> string)
      (replace_id : string -> string -> 'a -> 'a) (get_exprs : 'a -> expr list)
      (acc : 'a list) (xs : 'a list) : 'a list =
    match xs with
    | [] ->
      List.rev acc
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
             replace_id original replacement x)
          x name_map
      in
      aux gen_id replace_id get_exprs (res :: acc) xs
  in
  let gen_id = make_gen_string_id ~prefix in
  aux gen_id replace_id get_exprs [] xs

(* let var_bindings_in_generic ?(m : expr VarMap.t = VarMap.empty)
 *     ~(get_pairs : 'a -> (expr * expr) list) (x : 'a) : expr VarMap.t =
 *   let open PatternMatch in
 *   let pairs = get_pairs x in
 *   List.fold_left
 *     (fun m (k, v) ->
 *        m
 *        |> (fun m -> var_bindings_in_pattern_match ~m ~pattern:k v)
 *        |> fun m -> var_bindings_in_pattern_match ~m ~pattern:v k)
 *     m pairs *)

(* let var_bindings_in_pairs ?(m : expr VarMap.t = VarMap.empty)
 *     (pairs : (expr * expr) list) : expr VarMap.t =
 *   let open PatternMatch in
 *   List.fold_left
 *     (fun m (k, v) ->
 *        m
 *        |> (fun m -> var_bindings_in_pattern_match ~m ~pattern:k v)
 *        |> fun m -> var_bindings_in_pattern_match ~m ~pattern:v k)
 *     m pairs *)

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

let size_internal (_ : id) (_ : node) : int = 40

let node_shape_internal (_ : id) (_ : node) : Cytoscape.node_shape = Circle

let rec get_sub_expr_by_indices expr indicies =
  (* Js_utils.console_log (expr_to_string expr);
   * Js_utils.console_log (indicies |> List.map string_of_int |> String.concat ","); *)
  match indicies with
  | [] ->
    expr
  | x :: xs -> (
      match expr with
      | Variable (_, _) ->
        failwith "Unexpected end of expression tree"
      | Pred (_, e) ->
        get_sub_expr_by_indices e indicies
      | Function (name, args) ->
        if List.hd (String.split_on_char '_' name) = "pred" then
          get_sub_expr_by_indices (List.hd args) indicies
        else get_sub_expr_by_indices (List.nth args (pred x)) xs
      | UnaryOp (_, e) ->
        get_sub_expr_by_indices e indicies
      | BinaryOp (op, e1, e2) -> (
          match op with
          | Subsume ->
            get_sub_expr_by_indices e1 indicies
          | _ ->
            if x = 1 then get_sub_expr_by_indices e1 xs
            else if x = 2 then get_sub_expr_by_indices e2 xs
            else failwith (Printf.sprintf "Unexpected index : %d" x) )
      | Quantified (_, _, e) ->
        get_sub_expr_by_indices e indicies
      | False ->
        failwith "Unexpected end of expression tree"
      | InsertedF _ ->
        failwith "Unexpected end of expression tree" )

let uniquify_expr =
  let gen_id = make_gen_string_id ~prefix:"T" in
  fun (expr : expr) ->
    ( let var_names = universal_var_names expr in
      let replace_acc_list = List.map (fun v -> (v, gen_id ())) var_names in
      Rename.rename_universal_var_names replace_acc_list expr
      : expr )
