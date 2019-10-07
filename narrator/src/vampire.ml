open Graph
open Misc_utils
module Analyzed_expr_graph = Graph.Make (Vampire_analyzed_expr)

let expr_to_nodes (e : Vampire_analyzed_expr.expr) :
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
  let rec aux (parent : string option) (e : Vampire_analyzed_expr.expr) :
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
    | Pred (name, e) ->
      { id
      ; node = Some (Data {expr_str = name})
      ; parents = Some parents
      ; children = Some children
      ; group
      ; node_visible = Some true
      ; label_visible = Some true }
      :: aux (Some id) e
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

let expr_to_node_map (e : Vampire_analyzed_expr.expr) : Analyzed_expr_graph.t =
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

let classification_to_string (c : classification) : string =
  match c with
  | Unsure ->
    "unsure"
  | Axiom ->
    "axiom"
  | InitialKnowledge ->
    "initial knowledge"
  | Rewriting ->
    "rewriting"
  | Knowledge ->
    "knowledge"
  | Goal ->
    "goal"
  | NegatedGoal ->
    "negated goal"
  | Contradiction ->
    "contradiction"
  | ProtocolStep ->
    "protocol step"
  | InteractiveProtocolStep ->
    "interactive protocol step"
  | Alias ->
    "alias"

module Analyzed_graph_base = struct
  type data =
    { expr : Vampire_analyzed_expr.expr
    ; derive_descr : string
    ; classification : classification
    ; extra_info : Vampire_raw_line.extra_info option
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
      sprintf "%s. %s %s" _id
        (Vampire_analyzed_expr.expr_to_string node.expr)
        (StringLabels.capitalize_ascii
           (classification_to_string node.classification))
    (* sprintf "%s %s"
     *   (Vampire_analyzed_expr.expr_to_string node.expr)
     *   (StringLabels.capitalize_ascii
     *      (classification_to_string node.classification)) *)
    | Group ->
      sprintf "%s. Group" _id

  let color_internal (_id : id) (node : node) : string =
    match node with
    | Data node -> (
        match node.classification with
        | Unsure ->
          "#FFC300"
        | Axiom ->
          "#74C2F6"
        | InitialKnowledge ->
          "#64db7e"
        | Rewriting ->
          "#5C91E5"
        | Knowledge ->
          "#30873E"
        | Goal ->
          "#4C5967"
        | NegatedGoal ->
          "#4C5967"
        | Contradiction ->
          "#4C5967"
        | ProtocolStep ->
          "#F67476"
        | InteractiveProtocolStep ->
          "#E10E11"
        | Alias ->
          "#979890" )
    | Group ->
      "#ff0000"

  let size_internal (_id : id) (node : node) : int =
    match node with Data _ -> 40 | Group -> 80

  let node_shape_internal (_id : id) (_node : node) : Cytoscape.node_shape =
    Circle
end

module Analyzed_graph = Graph.Make (Analyzed_graph_base)

let line_to_node_record (line : Vampire_raw_line.line) :
  Analyzed_graph.node_record =
  let id, raw_expr, info = line in
  { id
  ; children = Some []
  ; parents = Some info.parents
  ; node =
      Some
        (Data
           { expr = Vampire_analyzed_expr.raw_expr_to_analyzed_expr raw_expr
           ; classification = Unsure
           ; derive_descr = info.descr
           ; extra_info = info.extra
           ; chain = (id, id, [id]) })
  ; group = None
  ; node_visible = Some true
  ; label_visible = Some true }

type node = Analyzed_graph.node

type node_graph = Analyzed_graph.t

type info_source =
  | Step of string
  | Axiom of Vampire_analyzed_expr.expr
  | Expr of Vampire_analyzed_expr.expr

type derive_explanation =
  | Nothing_to_explain
  | Dont_know_how
  | Rewrite of (Vampire_analyzed_expr.expr * Vampire_analyzed_expr.expr) list
  | Combine_knowledge of info_source list * Vampire_analyzed_expr.expr list
  | Gain_knowledge of
      info_source list
      * (Vampire_analyzed_expr.expr * Vampire_analyzed_expr.expr) list
      * (Vampire_analyzed_expr.expr * Vampire_analyzed_expr.expr) list

type grouped_derive_explanations =
  | Nothing_to_explain
  | Dont_know_how
  | Rewrites of Vampire_analyzed_expr.expr list list
  | Combine_knowledge of info_source list * Vampire_analyzed_expr.expr list
  | Gain_knowledge of info_source list * Vampire_analyzed_expr.expr list

(* let mark_free_variables (m : node_graph) : node_graph =
 *   let open Analyzed_graph in
 *   let mark_free_variable_possibly () (id : id) (node : node) (m : node_graph) =
 *     let data = unwrap_data node in
 *     let parents = find_parents id m in
 *     let data =
 *       { data with
 *         expr =
 *           ( if parents = [] then
 *               Vampire_analyzed_expr.mark_if_unsure Free data.expr
 *             else data.expr ) }
 *     in
 *     ((), Analyzed_graph.add_node Overwrite id (Data data) m)
 *   in
 *   let (), m =
 *     Analyzed_graph.linear_traverse ()
 *       (Full_traversal mark_free_variable_possibly) m
 *   in
 *   m *)

(* let mark_universal_variables (m : node_graph) : node_graph =
 *   let open Analyzed_graph in
 *   let mark_universal_variable_possibly () (id : id) (node : node)
 *       (m : node_graph) =
 *     let data = unwrap_data node in
 *     let data =
 *       { data with
 *         expr = Vampire_analyzed_expr.mark_if_unsure Universal data.expr }
 *     in
 *     ((), Analyzed_graph.add_node Overwrite id (Data data) m)
 *   in
 *   let (), m =
 *     Analyzed_graph.linear_traverse ()
 *       (Full_traversal mark_universal_variable_possibly) m
 *   in
 *   m *)

(* let propagate_variable_bound (m : node_graph) : node_graph =
 *   let open Analyzed_graph in
 *   let propagate_bound_to_child (m : node_graph) target_id child_id =
 *     let bound =
 *       Vampire_analyzed_expr.get_bound
 *         (unwrap_data (find_node target_id m)).expr
 *     in
 *     let node = unwrap_data (find_node child_id m) in
 *     let node =
 *       {node with expr = Vampire_analyzed_expr.update_bound node.expr bound}
 *     in
 *     Analyzed_graph.add_node Overwrite child_id (Data node) m
 *   in
 *   let propagate_bound_to_children () (id : id) (_node : node) (m : node_graph)
 *     =
 *     let children = find_children id m in
 *     ( ()
 *     , List.fold_left
 *         (fun m child_id -> propagate_bound_to_child m id child_id)
 *         m children )
 *   in
 *   let (), m =
 *     Analyzed_graph.linear_traverse ()
 *       (Full_traversal propagate_bound_to_children) m
 *   in
 *   m *)

let mark_variable_bound (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let (), m =
    linear_traverse ()
      (Full_traversal
         (fun () id node m ->
            let data = unwrap_data node in
            let new_expr = Vampire_analyzed_expr.mark_var_bound data.expr in
            let m =
              add_node Overwrite id (Data {data with expr = new_expr}) m
            in
            ((), m)))
      m
  in
  m

module Protocol_step = struct
  type direction =
    | Client_to_intruder
    | Intruder_to_client

  type in_out =
    | In
    | Out

  type t =
    { proc_name : string option
    ; in_out : in_out
    ; direction : direction
    ; step_num : int
    ; expr : Vampire_analyzed_expr.expr }

  let break_down_step_string (s : string) :
    string option * in_out option * int option =
    let rec aux (parts : string list) (proc_name_parts : string list)
        (in_out : in_out option) (n : int option) :
      string option * in_out option * int option =
      match parts with
      | [] ->
        ( ( match List.rev proc_name_parts with
              | [] ->
                None
              | l ->
                Some (String.concat "_" l) )
        , in_out
        , n )
      | ["out"; n] ->
        aux [] proc_name_parts (Some Out) (int_of_string_opt n)
      | ["in"; n] ->
        aux [] proc_name_parts (Some In) (int_of_string_opt n)
      | x :: xs ->
        if x = "tuple" then aux xs proc_name_parts in_out n
        else aux xs (x :: proc_name_parts) in_out n
    in
    aux (String.split_on_char '_' s) [] None None

  let node_to_steps (node : node) : t list =
    let expr_to_steps e =
      match Vampire_analyzed_expr.(e |> strip_att) with
      | Function (name, exprs) -> (
          match break_down_step_string name with
          | proc_name, Some in_out, Some step_num ->
            let expr =
              match exprs with
              | [e] ->
                e
              | es ->
                Function (Printf.sprintf "tuple_%d" (List.length es), es)
            in
            [ { proc_name
              ; in_out
              ; step_num
              ; direction = Client_to_intruder
              ; expr } ]
          | _ ->
            [] )
      | _ ->
        []
    in
    match node with
    | Group ->
      []
    | Data node -> (
        match node.classification with
        | ProtocolStep ->
          let open Vampire_analyzed_expr in
          (* Js_utils.console_log (Printf.sprintf "expr : %s" (Vampire_analyzed_expr.expr_to_string node.expr)); *)
          node.expr |> strip_quant |> expr_to_steps
        | InteractiveProtocolStep ->
          (* Js_utils.console_log (Printf.sprintf "expr : %s" (Vampire_analyzed_expr.expr_to_string node.expr)); *)
          let open Vampire_analyzed_expr in
          node.expr |> strip_quant |> split_on_impl
          |> (function None -> failwith "Unexpected None" | Some x -> x)
          |> fun (pre, e) ->
          (*Js_utils.console_log (Printf.sprintf "pre : %s, e : %s" (Vampire_analyzed_expr.expr_to_string pre) (Vampire_analyzed_expr.expr_to_string e));*)
          (pre |> split_on_and |> List.map expr_to_steps |> List.concat)
          @ expr_to_steps e
        | _ ->
          [] )
end

module Classify = struct
  let classify_negated_goal (m : node_graph) : node_graph =
    let open Analyzed_graph in
    let classify () (id : id) (node : node) (m : node_graph) :
      unit * node_graph =
      let data = unwrap_data node in
      match data.classification with
      | Unsure ->
        let classification =
          if data.derive_descr = "negated conjecture" then NegatedGoal
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
      | _ ->
        ((), m)
    in
    linear_traverse () (Full_traversal classify) m |> unwrap_tuple_1

  let classify_goal (m : node_graph) : node_graph =
    let open Analyzed_graph in
    let classify () (id : id) (node : node) (m : node_graph) :
      unit * node_graph =
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
      | _ ->
        ((), m)
    in
    linear_traverse () (Full_traversal classify) m |> unwrap_tuple_1

  let classify_protocol_step (m : node_graph) : node_graph =
    let open Analyzed_graph in
    let check_tag (tag : string) : bool =
      match Protocol_step.break_down_step_string tag with
      | _, Some _, Some _ ->
        true
      | _ ->
        false
    in
    let classify () (id : id) (node : node) (m : node_graph) :
      unit * node_graph =
      let open Vampire_analyzed_expr in
      let data = unwrap_data node in
      match data.classification with
      | Unsure -> (
          match find_parents id m with
          | [] ->
            let classification =
              match data.expr with
              | Pred ("attacker", Function (name, _))
              | Quantified (_, _, Pred ("attacker", Function (name, _))) -> (
                  match Protocol_step.break_down_step_string name with
                  | _, Some _, Some _ ->
                    ProtocolStep
                  | _ ->
                    data.classification )
              (* | Quantified (_, _, Pred ("attacker", [Function (name, _)]))
               *   -> (
               *       match Protocol_step.break_down_step_string name with
               *       | _, Some _, Some _ ->
               *         ProtocolStep
               *       | _ ->
               *         data.classification ) *)
              | BinaryOp (Imply, antecedent, consequent)
              | Quantified (_, _, BinaryOp (Imply, antecedent, consequent)) ->
                let premises =
                  Vampire_analyzed_expr.split_on_and antecedent
                in
                let is_step f =
                  match f with
                  | Pred ("attacker", Function (name, _)) -> (
                      match Protocol_step.break_down_step_string name with
                      | _, Some _, Some _ ->
                        true
                      | _ ->
                        false )
                  | _ ->
                    false
                in
                if List.exists is_step premises && is_step consequent then
                  InteractiveProtocolStep
                else data.classification
              | _ ->
                data.classification
            in
            let data = {data with classification} in
            ((), add_node Overwrite id (Data data) m)
          | _ ->
            ((), m) )
      | _ ->
        ((), m)
    in
    linear_traverse () (Full_traversal classify) m |> unwrap_tuple_1

  let classify_axiom (m : node_graph) : node_graph =
    let open Analyzed_graph in
    let classify () (id : id) (node : node) (m : node_graph) :
      unit * node_graph =
      let data = unwrap_data node in
      match data.classification with
      | Unsure -> (
          match find_parents id m with
          | [] ->
            let classification =
              match data.expr with
              | Quantified (Forall, _, BinaryOp (Eq, _, _)) ->
                (Axiom : classification)
              | Quantified (Forall, _, BinaryOp (Imply, _, _)) ->
                Axiom
              | _ ->
                data.classification
            in
            let data = {data with classification} in
            ((), add_node Overwrite id (Data data) m)
          | _ ->
            ((), m) )
      | _ ->
        ((), m)
    in
    linear_traverse () (Full_traversal classify) m |> unwrap_tuple_1

  let classify_rewriting (m : node_graph) : node_graph =
    let open Analyzed_graph in
    let classify () (id : id) (node : node) (m : node_graph) :
      unit * node_graph =
      let data = unwrap_data node in
      match data.classification with
      | Unsure ->
        let parents = find_nodes (find_parents id m) m in
        let all_parents_axiom_or_rewriting =
          List.for_all
            (fun x ->
               (unwrap_data x).classification = Axiom
               || (unwrap_data x).classification = Rewriting)
            parents
        in
        let classification =
          if parents <> [] && all_parents_axiom_or_rewriting then Rewriting
          else data.classification
        in
        let data = {data with classification} in
        ((), add_node Overwrite id (Data data) m)
      | _ ->
        ((), m)
    in
    linear_traverse () (Full_traversal classify) m |> unwrap_tuple_1

  let classify_initial_knowledge (m : node_graph) : node_graph =
    let open Analyzed_graph in
    let classify () (id : id) (node : node) (m : node_graph) :
      unit * node_graph =
      let data = unwrap_data node in
      match data.classification with
      | Unsure -> (
          match find_parents id m with
          | [] ->
            let classification =
              match data.expr with
              | Pred ("attacker", _) ->
                InitialKnowledge
              | _ ->
                data.classification
            in
            let data = {data with classification} in
            ((), add_node Overwrite id (Data data) m)
          | _ ->
            ((), m) )
      | _ ->
        ((), m)
    in
    linear_traverse () (Full_traversal classify) m |> unwrap_tuple_1

  let classify_contradiction (m : node_graph) : node_graph =
    let open Analyzed_graph in
    let classify () (id : id) (node : node) (m : node_graph) :
      unit * node_graph =
      let data = unwrap_data node in
      match data.classification with
      | Unsure ->
        let classification =
          match data.expr with
          | False ->
            Contradiction
          | _ ->
            data.classification
        in
        let data = {data with classification} in
        ((), add_node Overwrite id (Data data) m)
      | _ ->
        ((), m)
    in
    linear_traverse () (Full_traversal classify) m |> unwrap_tuple_1

  let classify_knowledge (m : node_graph) : node_graph =
    let open Analyzed_graph in
    let classify () (id : id) (node : node) (m : node_graph) :
      unit * node_graph =
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
               || (unwrap_data x).classification = Knowledge)
            parents
        in
        let classification =
          if any_parents_protocol_step_or_knowledge then Knowledge
          else data.classification
        in
        let data = {data with classification} in
        ((), add_node Overwrite id (Data data) m)
      | _ ->
        ((), m)
    in
    linear_traverse () (Full_traversal classify) m |> unwrap_tuple_1

  let classify_alias (m : node_graph) : node_graph =
    let open Analyzed_graph in
    let classify () (id : id) (node : node) (m : node_graph) :
      unit * node_graph =
      let data = unwrap_data node in
      match data.classification with
      | Unsure -> (
          match find_parents id m with
          | [] ->
            let classification =
              match data.expr with
              | BinaryOp (Iff, _, _) ->
                Alias
              | _ ->
                data.classification
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
                       (unwrap_data (find_node id m)).classification = Alias)
                    parent_ids
                in
                let alias = List.nth aliases 0 in
                (* look at the classifiction of the origninal node *)
                let children =
                  List.filter (fun x -> x <> id) (find_children alias m)
                in
                match children with
                | [] ->
                  data.classification
                | children ->
                  let original = find_node (List.nth children 0) m in
                  (unwrap_data original).classification
              else data.classification
            in
            let data = {data with classification} in
            ((), add_node Overwrite id (Data data) m) )
      | _ ->
        ((), m)
    in
    linear_traverse () (Full_traversal classify) m |> unwrap_tuple_1
end

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
            alias_count > 1)
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
       add_node Overwrite id n ~children ~parents m)
    m nodes

let rewrite_conclusion (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let collect_ids_to_remove (goal_id : id) (m : node_graph) : id list =
    let rec aux acc id m =
      let acc = id :: acc in
      match find_children id m with
      | [] ->
        acc
      | l ->
        List.fold_left (fun acc x -> aux acc x m) acc l
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
  | None ->
    m
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

let remove_goal (m : node_graph) : node_graph =
  let open Analyzed_graph in
  let remove_if_goal () (id : id) (node : node) (m : node_graph) =
    let children = find_children id m in
    let parents = find_parents id m in
    match children with
    | [] ->
      ((), m)
    | l ->
      let data = unwrap_data node in
      let is_negated_goal = data.classification = NegatedGoal in
      let children = find_nodes l m in
      let any_child_negated_goal =
        List.filter
          (fun (x : node) ->
             let data = unwrap_data x in
             data.classification = NegatedGoal)
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
    | [x] ->
      aux m x acc
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
    | [] ->
      m
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
    | _ ->
      ((), m)
  in
  linear_traverse () (Full_traversal mark_chain) m |> Misc_utils.unwrap_tuple_1

let node_map_to_unifier_map (m : node_graph) :
  string Vampire_analyzed_expr.ExprMap.t =
  let open Analyzed_graph in
  Js_utils.console_log "node_map_to_unifier_map";
  let extract_unifier expr_map _id node (m : node_graph) =
    match node with
    | Data data -> (
        match data.extra_info with
        | None ->
          expr_map
        | Some info ->
          let l_node = find_node info.l_node m in
          let r_node = find_node info.r_node m in
          let l_data =
            match l_node with
            | Data data ->
              data
            | Group ->
              failwith "Group not exepcted"
          in
          let r_data =
            match r_node with
            | Data data ->
              data
            | Group ->
              failwith "Group not exepcted"
          in
          let l_ast_indices = info.l_ast_indices in
          let r_ast_indices = info.r_ast_indices in
          let unifier_e1 =
            Vampire_analyzed_expr.get_sub_expr_by_indices l_data.expr
              l_ast_indices
          in
          let unifier_e2 =
            Vampire_analyzed_expr.get_sub_expr_by_indices r_data.expr
              r_ast_indices
          in
          Js_utils.console_log "l_data.expr :";
          Js_utils.console_log
            (Vampire_analyzed_expr.expr_to_string l_data.expr);
          Js_utils.console_log "r_data.expr :";
          Js_utils.console_log
            (Vampire_analyzed_expr.expr_to_string r_data.expr);
          Js_utils.console_log "unifier_e1 :";
          Js_utils.console_log
            (Vampire_analyzed_expr.expr_to_string unifier_e1);
          Js_utils.console_log "unifier_e2 :";
          Js_utils.console_log
            (Vampire_analyzed_expr.expr_to_string unifier_e2);
          expr_map )
    | Group ->
      expr_map
  in
  let expr_map = Vampire_analyzed_expr.ExprMap.empty in
  let expr_map, _ =
    linear_traverse expr_map (Full_traversal_pure extract_unifier) m
  in
  expr_map

module RewriteKnowledgeNodes = struct
  let knowledge_node_ids (m : node_graph) : string list =
    let open Analyzed_graph in
    let ids, _ =
      linear_traverse []
        (Full_traversal_pure
           (fun acc id node _m ->
              let data = unwrap_data node in
              match data.classification with Knowledge -> id :: acc | _ -> acc))
        m
    in
    ids

  let uniquify_knowledge_nodes (m : node_graph) : node_graph =
    let open Analyzed_graph in
    let gen_int = Misc_utils.make_gen_id () in
    let ids = knowledge_node_ids m in
    let (), m =
      linear_traverse ~ids ()
        (Full_traversal
           (fun () id node m ->
              Js_utils.console_log
                (Printf.sprintf "Updating knowledge node : %s" id);
              let data = unwrap_data node in
              Js_utils.console_log
                (Printf.sprintf "Old expr : %s"
                   (Vampire_analyzed_expr.expr_to_string data.expr));
              let var_names =
                Vampire_analyzed_expr.universal_var_names data.expr
              in
              let replace_acc_list =
                List.map
                  (fun v -> (v, Printf.sprintf "V%d" (gen_int ())))
                  var_names
              in
              let new_expr =
                Vampire_analyzed_expr.Rename.rename_universal_var_names
                  replace_acc_list data.expr
              in
              Js_utils.console_log
                (Printf.sprintf "New expr : %s"
                   (Vampire_analyzed_expr.expr_to_string new_expr));
              let m =
                add_node Overwrite id (Data {data with expr = new_expr}) m
              in
              ((), m)))
        m
    in
    m
end

let node_list_to_map (node_records : Analyzed_graph.node_record list) :
  node_graph =
  let open Classify in
  let classify (m : node_graph) : node_graph =
    m |> classify_negated_goal |> classify_goal |> classify_protocol_step
    |> classify_axiom |> classify_rewriting |> classify_initial_knowledge
    |> classify_contradiction |> classify_knowledge
  in
  Analyzed_graph.add_nodes_via_records Overwrite node_records
    Analyzed_graph.empty
  |> mark_variable_bound (*|> propagate_variable_bound *)
  (* |> mark_universal_variables*) |> classify
  |> classify_alias |> classify |> rewrite_conclusion |> redraw_alias_arrows
  |> RewriteKnowledgeNodes.uniquify_knowledge_nodes

let trace_sources (id : Analyzed_graph.id) (m : node_graph) : info_source list
  =
  let open Analyzed_graph in
  let check_tag (tag : string) : bool =
    match Protocol_step.break_down_step_string tag with
    | _, Some _, Some _ ->
      true
    | _ ->
      false
  in
  let reformat_tag (tag : string) : string =
    match Protocol_step.break_down_step_string tag with
    | Some p, Some In, Some n ->
      Printf.sprintf "%s.in.%d" p n
    | Some p, Some Out, Some n ->
      Printf.sprintf "%s.out.%d" p n
    | None, Some In, Some n ->
      Printf.sprintf "GLOBAL.in.%d" n
    | None, Some Out, Some n ->
      Printf.sprintf "GLOBAL.out.%d" n
    | _ ->
      failwith "Unexpected case"
  in
  let rec aux (id : id) (m : node_graph) : info_source list =
    let open Vampire_analyzed_expr in
    match find_parents id m with
    | [] -> (
        let data = unwrap_data (find_node id m) in
        match data.expr with
        | Pred ("attacker", Function (name, _)) -> (
            match Protocol_step.break_down_step_string name with
            | _, Some _, Some _ ->
              [Step (reformat_tag name)]
            | _ ->
              [Axiom data.expr] )
        | Quantified (_, _, Pred ("attacker", Function (name, _))) -> (
            match Protocol_step.break_down_step_string name with
            | _, Some _, Some _ ->
              [Step (reformat_tag name)]
            | _ ->
              [Axiom data.expr] )
        | Quantified
            ( _
            , _
            , BinaryOp
                (Imply, antecedent, Pred ("attacker", Function (name, _))) )
          -> (
              let premises = Vampire_analyzed_expr.split_on_and antecedent in
              let is_step f =
                match f with
                | Pred ("attacker", Function (name, _)) -> (
                    match Protocol_step.break_down_step_string name with
                    | _, Some _, Some _ ->
                      true
                    | _ ->
                      false )
                | _ ->
                  false
              in
              match Protocol_step.break_down_step_string name with
              | _, Some _, Some _ ->
                if List.exists is_step premises then [Step (reformat_tag name)]
                else [Axiom data.expr]
              | _ ->
                [Axiom data.expr] )
        | _ ->
          [Axiom data.expr] )
    | ps ->
      List.concat (List.map (fun p -> aux p m) ps)
  in
  List.sort_uniq compare (aux id m)

module Explain = struct
  let uniquify_universal_var_names_derive_explanations
      (explanations : derive_explanation list) : derive_explanation list =
    let replace_id (original : string) (replacement : string)
        (explanation : derive_explanation) : derive_explanation =
      let replace_id_for_pairs (original : string) (replacement : string)
          (pairs :
             (Vampire_analyzed_expr.expr * Vampire_analyzed_expr.expr) list) :
        (Vampire_analyzed_expr.expr * Vampire_analyzed_expr.expr) list =
        List.map
          (fun (k, v) ->
             ( Vampire_analyzed_expr.Rename.rename_universal_var_name original
                 replacement k
             , Vampire_analyzed_expr.Rename.rename_universal_var_name original
                 replacement v ))
          pairs
      in
      match explanation with
      | Nothing_to_explain ->
        explanation
      | Dont_know_how ->
        explanation
      | Rewrite pairs ->
        Rewrite (replace_id_for_pairs original replacement pairs)
      | Combine_knowledge (infos, es) ->
        Combine_knowledge
          ( List.map
              (fun info ->
                 match info with
                 | Expr e ->
                   Expr
                     (Vampire_analyzed_expr.Rename.rename_universal_var_name
                        original replacement e)
                 | _ ->
                   info)
              infos
          , List.map
              (Vampire_analyzed_expr.Rename.rename_universal_var_name
                 original replacement)
              es )
      | Gain_knowledge (infos, pairs1, pairs2) ->
        Gain_knowledge
          ( infos
          , replace_id_for_pairs original replacement pairs1
          , replace_id_for_pairs original replacement pairs2 )
    in
    let get_exprs (explanation : derive_explanation) :
      Vampire_analyzed_expr.expr list =
      let pairs_to_exprs
          (pairs :
             (Vampire_analyzed_expr.expr * Vampire_analyzed_expr.expr) list) :
        Vampire_analyzed_expr.expr list =
        List.fold_left (fun acc (k, v) -> k :: v :: acc) [] pairs
      in
      match explanation with
      | Nothing_to_explain ->
        []
      | Dont_know_how ->
        []
      | Rewrite pairs ->
        pairs_to_exprs pairs
      | Combine_knowledge (infos, es) ->
        List.map
          (fun info ->
             match info with Expr e -> e | _ -> failwith "Unexpected case")
          (List.filter
             (fun info ->
                match info with
                | Step _ ->
                  false
                | Axiom _ ->
                  false
                | Expr _ ->
                  true)
             infos)
        @ es
      (* | Combine_knowledge (_, _)              -> [] *)
      | Gain_knowledge (_, pairs1, pairs2) ->
        pairs_to_exprs pairs1 @ pairs_to_exprs pairs2
    in
    Vampire_analyzed_expr.uniquify_universal_var_names_generic ~replace_id
      ~get_exprs "X" explanations

  let var_bindings_in_explanations (explanations : derive_explanation list) :
    Vampire_analyzed_expr.expr Vampire_analyzed_expr.VarMap.t =
    let open Vampire_analyzed_expr in
    let get_pairs (explanation : derive_explanation) : (expr * expr) list =
      match explanation with
      | Nothing_to_explain ->
        []
      | Dont_know_how ->
        []
      | Rewrite pairs ->
        pairs
      | Combine_knowledge _ ->
        []
      | Gain_knowledge (_, pairs1, pairs2) ->
        pairs1 @ pairs2
    in
    List.fold_left
      (fun m e -> var_bindings_in_generic ~m ~get_pairs e)
      VarMap.empty explanations

  let info_source_to_string (x : info_source) : string =
    match x with
    | Step tag ->
      Printf.sprintf "step %s" tag
    | Axiom ax ->
      Printf.sprintf "axiom %s" (Vampire_analyzed_expr.expr_to_string ax)
    | Expr e ->
      Printf.sprintf "%s" (Vampire_analyzed_expr.expr_to_string e)

  let explain_construction_single (id : Analyzed_graph.id) (m : node_graph) :
    derive_explanation =
    let open Analyzed_graph in
    let open Vampire_analyzed_expr in
    let is_rewrite (e : expr) : bool =
      match e with BinaryOp (Eq, _, _) -> true | _ -> false
    in
    let base = unwrap_data (find_node id m) in
    match find_children id m with
    | [] ->
      Nothing_to_explain
    | [result_id] -> (
        let result = unwrap_data (find_node result_id m) in
        match List.filter (fun x -> x <> id) (find_parents result_id m) with
        | [] ->
          Nothing_to_explain
        | [agent_id] -> (
            (* explain single base, agent, and result *)
            let agent = unwrap_data (find_node agent_id m) in
            let base_expr = remove_subsumptions base.expr in
            let agent_expr = remove_subsumptions agent.expr in
            let result_expr = remove_subsumptions result.expr in
            (* let base_expr   = unwrap_subsume base.expr   in
             * let agent_expr  = unwrap_subsume agent.expr  in
             * let result_expr = unwrap_subsume result.expr in *)
            let base_expr =
              base_expr |> Vampire_analyzed_expr.negate |> strip_quant
            in
            let agent_expr =
              agent_expr |> Vampire_analyzed_expr.negate |> strip_quant
            in
            let result_expr =
              result_expr |> Vampire_analyzed_expr.negate |> strip_quant
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
                ( trace_sources agent_id m
                  @ List.map (fun x -> Expr x) r_exprs
                , [b_expr] )
            | b_exprs, [a_expr], r_exprs
              when is_rewrite a_expr
                && List.length b_exprs = List.length r_exprs ->
              let match_map =
                BruteForceClauseSetPairExprMatches.best_solution r_exprs
                  b_exprs
              in
              Js_utils.console_log
                (Printf.sprintf "match_map size : %d"
                   (List.length (ExprMap.bindings match_map)));
              Rewrite (ExprMap.bindings match_map)
            | b_exprs, a_exprs, r_exprs
              when List.length b_exprs
                   = List.length a_exprs + List.length r_exprs ->
              let match_map =
                BruteForceClauseSetPairExprMatches.best_solution
                  (a_exprs @ r_exprs) b_exprs
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
            | _ ->
              Dont_know_how )
        | _ ->
          Dont_know_how )
    | _ ->
      Dont_know_how

  let explain_construction_single_chained (id : Analyzed_graph.id)
      (m : node_graph) : derive_explanation list =
    let open Analyzed_graph in
    let open Vampire_analyzed_expr in
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
    let open Vampire_analyzed_expr in
    let same_group (e1 : derive_explanation) (e2 : derive_explanation) : bool =
      match (e1, e2) with
      | Nothing_to_explain, Nothing_to_explain ->
        true
      | Dont_know_how, Dont_know_how ->
        true
      | Rewrite _, Rewrite _ ->
        true
      | Combine_knowledge _, Combine_knowledge _ ->
        true
      | Gain_knowledge _, Gain_knowledge _ ->
        true
      | _ ->
        false
    in
    let group_into_list (explanations : derive_explanation list) :
      derive_explanation list list =
      let rec aux (acc : derive_explanation list list)
          (explanations : derive_explanation list) :
        derive_explanation list list =
        match explanations with
        | [] ->
          List.rev (List.map List.rev acc)
        | e :: es ->
          let acc : derive_explanation list list =
            match acc with
            | [] ->
              [[e]]
            | last_es :: acc -> (
                match last_es with
                | [] ->
                  [e] :: acc
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
        | [] ->
          List.map List.rev buckets
        | pairs :: rest ->
          let buckets =
            match buckets with
            | [] ->
              List.map (fun (k, v) -> [k; v]) pairs
            | buckets ->
              let pair_heads = List.map (fun (k, _) -> k) pairs in
              let bucket_heads = List.map List.hd buckets in
              let match_map =
                BruteForceClauseSetPairExprMatches.best_solution
                  bucket_heads pair_heads
              in
              List.map
                (fun l ->
                   match l with
                   | [] ->
                     []
                   | hd :: tl ->
                     let new_hd =
                       List.assoc (ExprMap.find hd match_map) pairs
                     in
                     new_hd :: hd :: tl)
                buckets
          in
          match_into_buckets buckets rest
      in
      let match_pairs_list : (expr * expr) list list =
        List.map
          (fun x ->
             match x with
             | Rewrite pairs ->
               pairs
             | _ ->
               failwith "Incorrect case")
          explanations
      in
      Rewrites (match_into_buckets [] match_pairs_list)
    in
    let convert_combine_knowledge (explanations : derive_explanation list) :
      grouped_derive_explanations list =
      List.map
        (fun (e : derive_explanation) ->
           ( match e with
             | Combine_knowledge (info_src, es) ->
               Combine_knowledge (info_src, es)
             | _ ->
               failwith "Incorrect case"
               : grouped_derive_explanations ))
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
             | _ ->
               failwith "Incorrect case"
               : grouped_derive_explanations ))
        explanations
    in
    let convert_to_grouped
        (grouped_explanations : derive_explanation list list) :
      grouped_derive_explanations list =
      let rec aux (acc : grouped_derive_explanations list)
          (grouped_explanations : derive_explanation list list) :
        grouped_derive_explanations list =
        match grouped_explanations with
        | [] ->
          List.rev acc
        | g :: gs ->
          let acc =
            match g with
            | [] ->
              acc
            | Nothing_to_explain :: _ ->
              Nothing_to_explain :: acc
            | Dont_know_how :: _ ->
              Dont_know_how :: acc
            | Rewrite _ :: _ ->
              convert_rewrite g :: acc
            | Combine_knowledge _ :: _ ->
              convert_combine_knowledge g @ acc
            | Gain_knowledge _ :: _ ->
              convert_gain_knowledge g @ acc
          in
          aux acc gs
      in
      aux [] grouped_explanations
    in
    let explanations =
      explanations |> uniquify_universal_var_names_derive_explanations
      |> List.filter (fun (x : derive_explanation) ->
          x <> Nothing_to_explain && x <> Dont_know_how)
    in
    let var_bindings = var_bindings_in_explanations explanations in
    List.iter
      (fun (k, v) ->
         Js_utils.console_log (Printf.sprintf "%s -> %s" k (expr_to_string v)))
      (VarMap.bindings var_bindings);
    let grouped_explanations = group_into_list explanations in
    convert_to_grouped grouped_explanations

  let explain_construction_chain (id : Analyzed_graph.id) (m : node_graph) :
    grouped_derive_explanations list =
    let open Analyzed_graph in
    let open Vampire_analyzed_expr in
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

  let derive_explanation_to_string (explanation : derive_explanation) : string
    =
    let open Vampire_analyzed_expr in
    match explanation with
    | Nothing_to_explain ->
      "N/A"
    | Dont_know_how ->
      "N/A"
    | Rewrite rewrites ->
      Printf.sprintf
        "Attacker rewrites\n%s\n                                          "
        (String.concat "\n\n"
           (List.map
              (fun (e_from, e_to) ->
                 Printf.sprintf "  %s\nto\n  %s" (expr_to_string e_from)
                   (expr_to_string e_to))
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
        (String.concat "\n"
           (List.map
              (fun (x, _) -> Printf.sprintf "  %s" (expr_to_string x))
              new_knowledge))

  let grouped_derive_explanations_to_string
      (explanation : grouped_derive_explanations) : string =
    let open Vampire_analyzed_expr in
    match explanation with
    | Nothing_to_explain ->
      "Nothing to explain"
    | Dont_know_how ->
      "Don't know how to explain"
    | Rewrites buckets ->
      Printf.sprintf "%s\n"
        (String.concat "\n\n"
           (List.map
              (fun b ->
                 Printf.sprintf "Attacker rewrites %s"
                   (String.concat " to\n"
                      (List.map Vampire_analyzed_expr.expr_to_string b)))
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
end

let node_to_string_debug (id : Analyzed_graph.id) (node : node)
    (m : node_graph) : string =
  let open Analyzed_graph in
  match node with
  | Group ->
    "Group node"
  | Data data ->
    let expr_str = Vampire_analyzed_expr.expr_to_string_debug data.expr in
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
         (Vampire_analyzed_expr.get_function_names data.expr))
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
          Printf.fprintf out "%s\n" (node_to_string_debug id node m)))
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
    fprintf out "%s <br>" (Vampire_analyzed_expr.expr_to_string data.expr);
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

let lines_to_node_map (lines : Vampire_raw_line.line option list) : node_graph
  =
  (* node_list_to_map
   *   (List.map line_to_node_record
   *      (List.map Misc_utils.unwrap_opt
   *         (List.filter (function Some _ -> true | None -> false) lines))) *)
  lines
  |> List.filter (function Some _ -> true | None -> false)
  |> List.map Option.get
  |> List.map line_to_node_record
  |> node_list_to_map

let process_string (input : string) : (node_graph, string) result =
  match Vampire_file_parser.parse_refutation_proof_string input with
  | Success x ->
    let m = x |> lines_to_node_map in
    let _ = node_map_to_unifier_map m in
    m
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
  | Failed (msg, _) ->
    Error msg

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
      | [] ->
        [List.rev (id :: cur_path)]
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
      | _ ->
        acc
    in
    let rec aux (acc : Protocol_step.t list) (last_id : id option)
        (path : id list) (m : node_graph) =
      match path with
      | [] ->
        List.rev acc
      | x :: xs ->
        (* check if any other path upward (i.e. a turn) to take *)
        let choices_upward =
          (* List.filter
           *   (fun x ->
           *      match last_id with
           *      | None ->
           *        true
           *      | Some last_id ->
           *        x <> last_id ) *)
          find_parents x m
        in
        (* collect steps reachable from the paths upward *)
        let acc =
          List.fold_left
            (fun acc parent ->
               let r, _ =
                 bfs_traverse parent acc Bottom_to_top
                   (Full_traversal_pure find_steps_at_top) m
               in
               r)
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
            || (unwrap_data n).classification = InteractiveProtocolStep)
         m)
  in
  List.iter
    (fun (_, node) ->
       let n = unwrap_data node in
       Js_utils.console_log
         (Printf.sprintf "step node : %s"
            (Vampire_analyzed_expr.expr_to_string n.expr)))
    step_nodes;
  let paths =
    List.concat
      (List.map
         (fun (id, _node) ->
            Js_utils.console_log
              (Printf.sprintf "expr : %s, paths : [%s]"
                 (Vampire_analyzed_expr.expr_to_string (unwrap_data _node).expr)
                 (String.concat ", "
                    (List.map
                       (fun l -> Printf.sprintf "[%s]" (String.concat ", " l))
                       (paths_to_root id m))));
            paths_to_root id m)
         step_nodes)
  in
  let steps =
    List.concat (List.map (fun path -> steps_reachable path m) paths)
  in
  List.iter
    (fun {proc_name; in_out; direction; step_num; expr} ->
       Js_utils.console_log
         (Printf.sprintf "test0 : %s, %d, %s"
            (match proc_name with None -> "" | Some s -> s)
            step_num
            (Vampire_analyzed_expr.expr_to_string expr)))
    steps;
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
                         x.step_num)
                    l)));
         Misc_utils.zip l acc)
      []
      (List.map (fun path -> steps_reachable path m) paths)
  in
  List.iter
    (fun {proc_name; in_out; direction; step_num; expr} ->
       Js_utils.console_log
         (Printf.sprintf "test100 : %s, %d, %s"
            (match proc_name with None -> "" | Some s -> s)
            step_num
            (Vampire_analyzed_expr.expr_to_string expr)))
    steps;
  let steps =
    List.fold_left
      (* if there are multiple occurances of a step, only keep the later ones *)
      (fun acc s -> if List.mem s acc then acc else s :: acc)
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

let attack_trace node_map =
  let open Protocol_step in
  let steps = collect_steps node_map in
  let max_proc_name_len_on_left =
    List.fold_left
      (fun cur_max s ->
         match (s.direction, s.proc_name) with
         | Client_to_intruder, Some s ->
           max cur_max (String.length s)
         | _ ->
           cur_max)
      0 steps
  in
  let max_proc_name_len_on_right =
    List.fold_left
      (fun cur_max s ->
         match (s.direction, s.proc_name) with
         | Intruder_to_client, Some s ->
           max cur_max (String.length s)
         | _ ->
           cur_max)
      0 steps
  in
  let intruder_name = "I" in
  let intruder_name_len = String.length intruder_name in
  let intruder_name_padding_on_left =
    if max_proc_name_len_on_left >= intruder_name_len then
      String.make (max_proc_name_len_on_left - intruder_name_len) ' '
    else ""
  in
  let intruder_name_padding_on_right =
    if max_proc_name_len_on_right >= intruder_name_len then
      String.make (max_proc_name_len_on_right - intruder_name_len) ' '
    else ""
  in
  String.concat "\n"
    (List.mapi
       (fun global_step_num s ->
          let global_step_num = global_step_num + 1 in
          let open Protocol_step in
          let proc_name =
            match s.proc_name with None -> "GLOBAL" | Some x -> x
          in
          let proc_name_len = String.length proc_name in
          let proc_name_padding_on_left =
            if max_proc_name_len_on_left >= proc_name_len then
              String.make (max_proc_name_len_on_left - proc_name_len) ' '
            else ""
          in
          let proc_name_padding_on_right =
            if max_proc_name_len_on_right >= proc_name_len then
              String.make (max_proc_name_len_on_right - proc_name_len) ' '
            else ""
          in
          let expr = Vampire_analyzed_expr.expr_to_string s.expr in
          match s.in_out with
          | Out ->
            Printf.sprintf "%d.    %s.%d%s    %s%s -> %s%s : %s\n"
              global_step_num proc_name s.step_num proc_name_padding_on_right
              proc_name_padding_on_left proc_name intruder_name
              intruder_name_padding_on_right expr
          | In ->
            Printf.sprintf "%d.    %s.%d%s    %s%s -> %s%s : %s\n"
              global_step_num proc_name s.step_num proc_name_padding_on_right
              intruder_name_padding_on_left intruder_name proc_name
              proc_name_padding_on_right expr)
       steps)

let resolve_vars_in_knowledge_nodes ~(base_id : string) ~(agent_id : string)
    ~(result_id : string) (m : node_graph) :
  Vampire_analyzed_expr.expr Vampire_analyzed_expr.VarMap.t =
  let open Analyzed_graph in
  let open Vampire_analyzed_expr in
  let base_data = find_node base_id m |> unwrap_data in
  let agent_data = find_node agent_id m |> unwrap_data in
  let result_data = find_node result_id m |> unwrap_data in
  assert (base_data.classification = Knowledge);
  assert (result_data.classification = Knowledge);
  let base_exprs =
    base_data.expr |> remove_subsumptions |> split_on_or |> List.map strip_not
  in
  let result_exprs =
    result_data.expr |> remove_subsumptions |> split_on_or
    |> List.map strip_not
  in
  match agent_data.extra_info with
  | Some extra_info ->
    VarMap.empty
  | None -> (
      match agent_data.expr |> remove_subsumptions with
      | BinaryOp (Eq, e1, e2) as eq ->
        (* equation *)
        let agent_exprs = [e1; e2] in
        let bindings =
          BruteForceEquationVarBindings.best_solution ~eq base_data.expr
            result_data.expr
        in
        Js_utils.console_log "resolve_vars_in_knowledge_nodes";
        VarMap.iter
          (fun k v ->
             Js_utils.console_log
               (Printf.sprintf "var : %s, e : %s" k
                  (Vampire_analyzed_expr.expr_to_string v)))
          bindings;
        VarMap.empty
      | agent_expr ->
        (* resolution *)
        let agent_exprs = agent_expr |> split_on_or |> List.map strip_not in
        let bindings =
          BruteForceClauseSetPairVarBindings.best_solution agent_exprs
            (base_exprs @ result_exprs)
        in
        Js_utils.console_log "resolve_vars_in_knowledge_nodes";
        VarMap.iter
          (fun k v ->
             Js_utils.console_log
               (Printf.sprintf "var : %s, e : %s" k
                  (Vampire_analyzed_expr.expr_to_string v)))
          bindings;
        VarMap.empty )
