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

let mark_if_unsure (bound : bound) (e : expr) : expr =
  let rec aux (e : expr) : expr =
    match e with
    | Variable (Unsure, v) ->
      Variable (bound, v)
    | Variable (Free, v) ->
      Variable (Free, v)
    | Variable (Universal, v) ->
      Variable (Universal, v)
    | Variable (Existential, v) ->
      Variable (Existential, v)
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

(* let unwrap_subsume (e : expr) : expr =
 *   match e with
 *   | BinaryOp (Subsume, e, _) -> e
 *   | _                   as e -> e *)

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
    (* | BinaryOp (Or, e, UnaryOp (Not, Variable (_, v))) when has_prefix v "spl"
     *   ->
     *   e
     * | BinaryOp (Or, UnaryOp (Not, Variable (_, v)), e) when has_prefix v "spl"
     *   ->
     *   e *)
    | BinaryOp (Subsume, e, _) -> e
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
    | Variable (Universal, _), (_ as v) ->
      1 + length v
    | (_ as v), Variable (Universal, _) ->
      1 + length v
    | Variable (Existential, _), _ ->
      raise Unexpected_existential_var
    | _, Variable (Existential, _) ->
      raise Unexpected_existential_var
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
    | _ ->
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
        if v1 = v2 then true else false
      | Variable (Universal, _), _ ->
        true
      | Function (f1, es1), Function (f2, es2) ->
        if f1 = f2 && List.length es1 = List.length es2 then aux_list es1 es2
        else false
      | UnaryOp (op1, e1), UnaryOp (op2, e2) ->
        if op1 = op2 then aux e1 e2 else false
      | BinaryOp (op1, e1a, e1b), BinaryOp (op2, e2a, e2b) ->
        if op1 = op2 then aux e1a e2a && aux e1b e2b else false
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

  let var_bindings_in_pattern_match ?(m : expr VarMap.t = VarMap.empty)
      ~(pattern : expr) (expr : expr) : expr VarMap.t =
    let rec aux (pattern : expr) (expr : expr) (m : expr VarMap.t) :
      expr VarMap.t =
      match (pattern, expr) with
      | Variable (Free, _), _ ->
        m
      | Variable (Universal, name), (_ as v) ->
        VarMap.add name v m
      | Variable (Existential, _), _ ->
        raise Unexpected_existential_var
      | Function (_, es1), Function (_, es2) ->
        aux_list es1 es2 m
      | UnaryOp (_, e1), UnaryOp (_, e2) ->
        aux e1 e2 m
      | BinaryOp (_, e1a, e1b), BinaryOp (_, e2a, e2b) ->
        aux_list [e1a; e1b] [e2a; e2b] m
      | Quantified (_, _, e1), Quantified (_, _, e2) ->
        aux e1 e2 m
      | False, False ->
        m
      | InsertedF _, InsertedF _ ->
        m
      | _ ->
        raise Unmatching_structure
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
         | None ->
           true
         | Some c ->
           VarMap.find k smaller = c)
      true keys

  let fill_in_pattern ~(pattern : expr) (var_bindings : expr VarMap.t) : expr =
    let rec aux (pattern : expr) (var_bindings : expr VarMap.t) : expr =
      match pattern with
      | Variable (Unsure, _) ->
        raise Unexpected_unsure_var
      | Variable (Free, _) as e ->
        e
      | Variable (Existential, _) ->
        raise Unexpected_existential_var
      | Variable (Universal, name) ->
        VarMap.find name var_bindings
      | Pred (name, e) ->
        Pred (name, aux e var_bindings)
      | Function (name, es1) ->
        Function (name, aux_list es1 var_bindings)
      | UnaryOp (op, e) ->
        UnaryOp (op, aux e var_bindings)
      | BinaryOp (op, e1, e2) ->
        BinaryOp (op, aux e1 var_bindings, aux e2 var_bindings)
      | Quantified (q, ids, e) ->
        Quantified (q, ids, aux e var_bindings)
      | False as e ->
        e
      | InsertedF _ as e ->
        e
    and aux_list (patterns : expr list) (var_bindings : expr VarMap.t) :
      expr list =
      List.map (fun e -> aux e var_bindings) patterns
    in
    aux pattern var_bindings

  let all_combinations (exprs1 : expr list) (exprs2 : expr list) :
    (expr * expr) list =
    let rec aux (acc : (expr * expr) list) (exprs1 : expr list)
        (exprs : expr list) : (expr * expr) list =
      match exprs1 with
      | [] ->
        acc
      | p :: ps ->
        let acc = List.map (fun e -> (p, e)) exprs @ acc in
        aux acc ps exprs
    in
    aux [] exprs1 exprs2

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
   *   aux [] combinations *)

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
          (exprs1_used : ExprSet.t) (exprs2_used : ExprSet.t) : bool =
        match keys with
        | [] ->
          true
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

  let filter_by_compatible_var_bindings (solutions : expr ExprMap.t list) :
    expr ExprMap.t list =
    let no_overlaps (m : expr ExprMap.t) : bool =
      let rec aux (keys : expr list) (var_bindings : expr VarMap.t)
          (m : expr ExprMap.t) : bool =
        match keys with
        | [] ->
          true
        | pat :: ks ->
          let expr = ExprMap.find pat m in
          let bindings = var_bindings_in_pattern_match ~pattern:pat expr in
          if var_bindings_compatible ~smaller:bindings ~larger:var_bindings
          then
            let var_bindings =
              var_bindings_in_pattern_match ~m:var_bindings ~pattern:pat expr
            in
            aux ks var_bindings m
          else false
      in
      let keys = List.map (fun (k, _) -> k) (ExprMap.bindings m) in
      aux keys VarMap.empty m
    in
    List.filter (fun m -> no_overlaps m) solutions

  let solution_score (m : expr ExprMap.t) : float =
    let rec aux (keys : expr list) (score_acc : float) (m : expr ExprMap.t) :
      float =
      match keys with
      | [] ->
        score_acc
      | pat :: ks ->
        let expr = ExprMap.find pat m in
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
end

let rewrite (base : expr) ~(rewrite_rule_from : expr) ~(rewrite_rule_to : expr)
    ~(expr_from : expr) : expr =
  let open PatternMatch in
  let rec aux (base : expr) (expr_from : expr) (to_expr : expr) : expr =
    if base = expr_from then to_expr
    else
      match base with
      | Variable _ as e ->
        e
      | Pred (name, e) ->
        Pred (name, aux e expr_from to_expr)
      | Function (name, es) ->
        Function (name, aux_list es expr_from to_expr)
      | UnaryOp (op, e) ->
        UnaryOp (op, aux e expr_from to_expr)
      | BinaryOp (op, e1, e2) ->
        BinaryOp (op, aux e1 expr_from to_expr, aux e2 expr_from to_expr)
      | Quantified (q, ids, e) ->
        Quantified (q, ids, aux e expr_from to_expr)
      | False as e ->
        e
      | InsertedF _ as e ->
        e
  and aux_list (bases : expr list) (expr_from : expr) (to_expr : expr) :
    expr list =
    List.map (fun e -> aux e expr_from to_expr) bases
  in
  let var_bindings =
    var_bindings_in_pattern_match ~pattern:rewrite_rule_from expr_from
  in
  let to_expr = fill_in_pattern ~pattern:rewrite_rule_to var_bindings in
  aux base expr_from to_expr

let pattern_multi_match_map (exprs1 : expr list) (exprs2 : expr list) :
  expr ExprMap.t option =
  let open PatternMatch in
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
    | Variable _ as e ->
      e
    | Pred (name, e) ->
      Pred (name, aux original replacement e)
    | Function (name, es) ->
      Function (name, aux_list original replacement es)
    | UnaryOp (op, e) ->
      UnaryOp (op, aux original replacement e)
    | BinaryOp (op, e1, e2) ->
      BinaryOp (op, aux original replacement e1, aux original replacement e2)
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

let replace_universal_var_names (l : (string * string) list) (e : expr) : expr
  =
  let rec aux (l : (string * string) list) (e : expr) : expr =
    match l with
    | [] ->
      e
    | (name, replacement) :: l ->
      aux l (replace_universal_var_name name replacement e)
  in
  aux l e

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
    | [] ->
      List.rev acc
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
  let gen_id = make_gen_id prefix in
  aux gen_id replace_id get_exprs [] xs

let var_bindings_in_generic ?(m : expr VarMap.t = VarMap.empty)
    ~(get_pairs : 'a -> (expr * expr) list) (x : 'a) : expr VarMap.t =
  let open PatternMatch in
  let pairs = get_pairs x in
  List.fold_left
    (fun m (k, v) ->
       m
       |> (fun m -> var_bindings_in_pattern_match ~m ~pattern:k v)
       |> fun m -> var_bindings_in_pattern_match ~m ~pattern:v k)
    m pairs

let var_bindings_in_pairs ?(m : expr VarMap.t = VarMap.empty)
    (pairs : (expr * expr) list) : expr VarMap.t =
  let open PatternMatch in
  List.fold_left
    (fun m (k, v) ->
       m
       |> (fun m -> var_bindings_in_pattern_match ~m ~pattern:k v)
       |> fun m -> var_bindings_in_pattern_match ~m ~pattern:v k)
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

let rec get_sub_expr_by_indices expr indicies =
  Js_utils.console_log (expr_to_string expr);
  Js_utils.console_log (indicies |> List.map string_of_int |> String.concat ",");
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
