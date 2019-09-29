(* open Cmdliner *)
open Js_of_ocaml
open Lwt

(* let narrator_js (src : string) *)

(* let narrator (src : string) (dst : string option) : 'a Term.ret =
 *   let ic = open_in src in
 *   let oc = match dst with
 *     | None   -> None
 *     | Some x -> Some (open_out x) in
 *   Core_kernel.protect
 *     ~f:(fun () ->
 *         try
 *           match Vampire.File_parser.parse_refutation_proof ic with
 *           | Success x ->
 *             x
 *             |> Vampire.lines_to_node_map
 *             |> Vampire.Analyzed_graph.(filter (fun x -> List.mem x.core.classification
 *                                                   [InitialKnowledge;
 *                                                    Knowledge;
 *                                                    NegatedGoal;
 *                                                    Contradiction]))
 *             (\* |> Analyzed_node.print_map_debug; *\)
 *             |> (match oc with
 *                 | None    -> Vampire.print_map_debug
 *                 | Some oc -> Vampire.write_map_DAG oc);
 *             `Ok ()
 *           | Failed (msg, _) -> `Error (false, msg)
 *         with
 *         | Exceptions.Unreachable -> `Error (false, "Unreachable code"))
 *     ~finally:(fun () ->
 *         close_in_noerr ic;
 *         match oc with
 *         | None -> ()
 *         | Some oc -> close_out_noerr oc
 *       )
 * 
 * let src =
 *   let doc = "Input file, supported formats : vampire refutation proof" in
 *   Arg.(required & pos 0 (some file) None & info [] ~docv:"SOURCE" ~doc)
 * 
 * let dst =
 *   let doc = "Output file, defatuls to SOURCE.narrator.debug or SOURCE.narrator.dag" in
 *   Arg.(value & pos 1 (some string) None & info [] ~docv:"DEST" ~doc)
 * 
 * let cmd =
 *   let doc = "Refutation proof interpreter" in
 *   let exits = Term.default_exits in
 *   (Term.(ret (const narrator $ src $ dst)),
 *    Term.info "narrator" ~exits ~doc) *)

(* let () = Term.(exit @@ eval cmd) *)

let attack_trace node_map =
  let open Vampire.Protocol_step in
  let steps = Vampire.collect_steps node_map in
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
          let open Vampire.Protocol_step in
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

let () =
  (* Set up the file loading code *)
  (* let pv_file_input             = Js.Unsafe.global##.document##getElementById (Js.string "pvFileInput") in *)
  (* let vampire_file_input        = Js.Unsafe.global##.document##getElementById (Js.string "vampireFileInput") in *)
  let single_formula_box_ID = "singleFormulaBox" in
  let chain_explanation_box_ID = "chainExplanationBox" in
  let single_explanation_box_ID = "singleExplanationBox" in
  let single_nodeAST_ID = "singleNodeAST" in
  let nodeAST1_ID = "nodeAST1" in
  let nodeAST2_ID = "nodeAST2" in
  let attack_trace_box_ID = "attackTraceBox" in
  let main_graph_display_ID = "mainGraphDisplay" in
  let main_text_display_ID = "mainTextDisplay" in
  (* let example_select_ID         = "exampleSelect" in *)
  let cy_single_nodeAST = Cytoscape.make single_nodeAST_ID in
  let cy_nodeAST1 = Cytoscape.make nodeAST1_ID in
  let cy_nodeAST2 = Cytoscape.make nodeAST2_ID in
  let cy_main = Cytoscape.make main_graph_display_ID in
  let dagre_main = ref None in
  let main_dag_node_height = 50 in
  let expr_AST_height = 25 in
  Js_utils.set_display ~id:single_formula_box_ID ~on:false;
  Js_utils.set_display ~id:single_nodeAST_ID ~on:false;
  Js_utils.set_display ~id:nodeAST1_ID ~on:false;
  Js_utils.set_display ~id:nodeAST2_ID ~on:false;
  Js_utils.set_display ~id:chain_explanation_box_ID ~on:false;
  Js_utils.set_display ~id:attack_trace_box_ID ~on:true;
  Js_utils.set_display ~id:main_graph_display_ID ~on:false;
  Js_utils.set_display ~id:main_text_display_ID ~on:true;
  let js_ctx = Js_context.make () in
  let rec vampire_file_reader () =
    let%lwt input = Lwt_condition.wait js_ctx.vampire_file_ready in
    ( match Vampire.process_string input with
      | Error e ->
        Js_utils.alert e
      | Ok node_map ->
        (* let node_map = Vampire.Analyzed_graph.remove_node 387 node_map in *)
        (* let debug_print = Js.Unsafe.global##.document##getElementById "debugPrint" in *)
        (* debug_print##.value := Js.string (Vampire.map_debug_string node_map); *)
        Js_utils.console_log (Vampire.map_debug_string node_map);
        dagre_main := Some (Dagre.make ());
        let node_map =
          Vampire.Analyzed_graph.update_label_visibility false node_map
        in
        Vampire.Analyzed_graph.plot !dagre_main cy_main
          ~height:main_dag_node_height node_map
        |> ignore;
        js_ctx.full_node_map <- Some (Vampire node_map);
        js_ctx.cur_node_map <- Some (Vampire node_map);
        let attack_trace_box =
          Js.Unsafe.global##.document##getElementById attack_trace_box_ID
        in
        let text = attack_trace node_map in
        attack_trace_box##.innerHTML := Js.string text;
        (* let base_node    = Vampire.Analyzed_graph.unwrap_data (Vampire.Analyzed_graph.find_node 67 node_map) in
         * let base_expr    = base_node.expr in
         * Js_utils.console_log (Printf.sprintf "base_expr : %s" (Vampire.Analyzed_expr.expr_to_string base_expr));
         * let rewrite_node = Vampire.Analyzed_graph.unwrap_data (Vampire.Analyzed_graph.find_node 115 node_map) in
         * let rewrite_expr = rewrite_node.expr in
         * Js_utils.console_log (Printf.sprintf "rewrite_expr : %s" (Vampire.Analyzed_expr.expr_to_string rewrite_expr));
         * let result_node  = Vampire.Analyzed_graph.unwrap_data (Vampire.Analyzed_graph.find_node 409 node_map) in
         * let result_expr  = result_node.expr in
         * Js_utils.console_log (Printf.sprintf "result_expr : %s" (Vampire.Analyzed_expr.expr_to_string result_expr));
         * let pat_match_map =
         *   Vampire.Analyzed_expr.pattern_multi_match_map
         *     ~patterns:(List.map Vampire.Analyzed_expr.strip_not (Vampire.Analyzed_expr.split_on_or rewrite_expr))
         *     (List.map Vampire.Analyzed_expr.strip_not (Vampire.Analyzed_expr.split_on_or base_expr @ Vampire.Analyzed_expr.split_on_or result_expr))
         * in
         * Vampire.Analyzed_expr.ExprMap.iter
         *   (fun k v ->
         *      Js_utils.console_log (Printf.sprintf "pat : %s, e : %s" (Vampire.Analyzed_expr.expr_to_string k) (Vampire.Analyzed_expr.expr_to_string v))
         *   )
         *   pat_match_map; *)
        () );
    vampire_file_reader ()
  in
  let rec pv_file_reader () =
    let%lwt input = Lwt_condition.wait js_ctx.pv_file_ready in
    ( match ProVerif.process_string input with
      | Error e ->
        Js_utils.alert e
      | Ok s ->
        js_ctx.pv_raw <- Some input;
        js_ctx.pv_processed <- Some s;
        let main_text_display =
          Js.Unsafe.global##.document##getElementById main_text_display_ID
        in
        main_text_display##.innerHTML := Js.string s;
        () );
    pv_file_reader ()
  in
  Lwt.async vampire_file_reader;
  Lwt.async pv_file_reader;
  (* let () = pv_file_input##addEventListener (Js.string "change")
   *     (Dom_html.handler
   *        (fun _ev ->
   *           begin
   *             Lwt_js.yield () >>= (fun () ->
   *                 let file = Js.Optdef.get (Js.array_get pv_file_input##.files 0) (fun () -> assert false) in
   *                 let file_reader = Js.Unsafe.global##.FileReader in
   *                 let file_reader = new%js file_reader in
   *                 file_reader##.onload :=
   *                   Dom_html.handler
   *                     (fun _ev ->
   *                        Lwt_condition.signal js_ctx.pv_file_ready (Js.to_string file_reader##.result);
   *                        let () = pv_file_input##.value := Js.string "" in
   *                        Js._true);
   *                 let () = file_reader##readAsText file in
   *                 Lwt.return_unit
   *               )
   *           end |> ignore;
   *           Js._true
   *        ))
   * in *)
  (* let () = vampire_file_input##addEventListener (Js.string "change")
   *     (Dom_html.handler
   *        (fun _ev ->
   *           begin
   *             Lwt_js.yield () >>= (fun () ->
   *                 let file = Js.Optdef.get (Js.array_get vampire_file_input##.files 0) (fun () -> assert false) in
   *                 let file_reader = Js.Unsafe.global##.FileReader in
   *                 let file_reader = new%js file_reader in
   *                 file_reader##.onload :=
   *                   Dom_html.handler
   *                     (fun _ev ->
   *                        Lwt_condition.signal js_ctx.vampire_file_ready (Js.to_string file_reader##.result);
   *                        let () = vampire_file_input##.value := Js.string "" in
   *                        Js._true);
   *                 let () = file_reader##readAsText file in
   *                 Lwt.return_unit
   *               )
   *           end |> ignore;
   *           Js._true
   *        ))
   * in *)
  let disable_border_prev_selected_node () : unit =
    match js_ctx.selected_node with
    | None ->
      ()
    | Some id ->
      Cytoscape.disable_node_border cy_main ~id
  in
  Cytoscape.on cy_main ~event:"boxstart" ~handler:(fun _ev ->
      Js_of_ocaml_lwt.Lwt_js.yield ()
      >>= (fun () ->
          js_ctx.box_selected_nodes <- [];
          return_unit)
      |> ignore);
  Cytoscape.on cy_main ~event:"box" ~selector:"node" ~handler:(fun ev ->
      Js_of_ocaml_lwt.Lwt_js.yield ()
      >>= (fun () ->
          let target_id = Js.to_string ev##.target_node##id in
          js_ctx.box_selected_nodes <- target_id :: js_ctx.box_selected_nodes;
          return_unit)
      |> ignore);
  Cytoscape.on cy_main ~event:"tap" ~handler:(fun ev ->
      if ev##.target_cy = ev##.cy then (
        disable_border_prev_selected_node ();
        js_ctx.selected_node <- None ));
  Cytoscape.on cy_main ~event:"tap" ~selector:"node" ~handler:(fun ev ->
      Js_utils.set_display ~id:single_formula_box_ID ~on:true;
      Js_utils.set_display ~id:single_nodeAST_ID ~on:true;
      Js_utils.set_display ~id:nodeAST1_ID ~on:false;
      Js_utils.set_display ~id:nodeAST2_ID ~on:false;
      Js_utils.set_display ~id:chain_explanation_box_ID ~on:false;
      Js_utils.set_display ~id:attack_trace_box_ID ~on:false;
      let target_id = Js.to_string ev##.target_node##id in
      disable_border_prev_selected_node ();
      js_ctx.selected_node <- Some target_id;
      Cytoscape.enable_node_border cy_main ~id:target_id;
      match js_ctx.cur_node_map with
      | None ->
        ()
      | Some (Vampire m) -> (
          let node = Vampire.Analyzed_graph.find_node target_id m in
          match node with
          | Data data ->
            let expr_str = Vampire_analyzed_expr.expr_to_string data.expr in
            let single_formula_box =
              Js.Unsafe.global##.document##getElementById
                single_formula_box_ID
            in
            single_formula_box##.innerHTML := Js.string expr_str;
            let em = Vampire.expr_to_node_map data.expr in
            Vampire.Analyzed_expr_graph.plot None cy_single_nodeAST
              ~height:expr_AST_height ~show_label:true em
            |> ignore;
            let single_explanation_box =
              Js.Unsafe.global##.document##getElementById
                single_explanation_box_ID
            in
            single_explanation_box##.innerHTML
            := Js.string
                (Vampire.derive_explanation_to_string
                   (Vampire.explain_construction_single target_id m))
          | Group ->
            () ));
  Cytoscape.on cy_main ~event:"tap" ~selector:"edge" ~handler:(fun ev ->
      Js_utils.set_display ~id:single_formula_box_ID ~on:false;
      Js_utils.set_display ~id:single_nodeAST_ID ~on:false;
      Js_utils.set_display ~id:nodeAST1_ID ~on:true;
      Js_utils.set_display ~id:nodeAST2_ID ~on:true;
      Js_utils.set_display ~id:chain_explanation_box_ID ~on:false;
      Js_utils.set_display ~id:attack_trace_box_ID ~on:false;
      disable_border_prev_selected_node ();
      js_ctx.selected_node <- None;
      let target = ev##.target_edge in
      let data = target##data in
      let source_id = Js.to_string data##.source in
      let target_id = Js.to_string data##.target in
      match js_ctx.cur_node_map with
      | None ->
        ()
      | Some (Vampire m) -> (
          let source = Vampire.Analyzed_graph.find_node source_id m in
          let target = Vampire.Analyzed_graph.find_node target_id m in
          match (source, target) with
          | Group, Group | _, Group | Group, _ ->
            ()
          | Data source_data, Data target_data ->
            let source_em = Vampire.expr_to_node_map source_data.expr in
            let target_em = Vampire.expr_to_node_map target_data.expr in
            let souce_diff, target_diff =
              Vampire.Analyzed_expr_graph.diff Top source_em target_em
            in
            Cytoscape.reset_style cy_nodeAST1;
            Cytoscape.reset_style cy_nodeAST2;
            Vampire.Analyzed_expr_graph.plot None cy_nodeAST1
              ~height:expr_AST_height ~show_label:true source_em
            |> ignore;
            Vampire.Analyzed_expr_graph.plot None cy_nodeAST2
              ~height:expr_AST_height ~show_label:true target_em
            |> ignore;
            Cytoscape.set_node_color cy_nodeAST1 ~color:"#d3d3d3";
            Cytoscape.set_node_color cy_nodeAST2 ~color:"#d3d3d3";
            Vampire.Analyzed_expr_graph.linear_traverse ()
              (Full_traversal_pure
                 (fun () id _node _m ->
                    Cytoscape.set_node_color cy_nodeAST1 ~id ~color:"#ff0000"))
              souce_diff
            |> ignore;
            Vampire.Analyzed_expr_graph.linear_traverse ()
              (Full_traversal_pure
                 (fun () id _node _m ->
                    Cytoscape.set_node_color cy_nodeAST2 ~id ~color:"#0000ff"))
              target_diff
            |> ignore ));
  Cytoscape.on cy_nodeAST1 ~event:"pan" ~handler:(fun _ev ->
      let pos = cy_nodeAST1##pan_get in
      cy_nodeAST2##pan pos);
  Cytoscape.on cy_nodeAST1 ~event:"zoom" ~handler:(fun _ev ->
      let zoom = cy_nodeAST1##zoom_get in
      cy_nodeAST2##zoom zoom);
  Cytoscape.on cy_nodeAST2 ~event:"zoom" ~handler:(fun _ev ->
      let zoom = cy_nodeAST2##zoom_get in
      cy_nodeAST1##zoom zoom);
  Cytoscape.on cy_nodeAST2 ~event:"pan" ~handler:(fun _ev ->
      let pos = cy_nodeAST2##pan_get in
      cy_nodeAST1##pan pos);
  let compress_button = Dom_html.getElementById_exn "compressButton" in
  compress_button##.onclick :=
    Dom_html.handler (fun _ev ->
        ( match js_ctx.cur_node_map with
          | None ->
            ()
          | Some (Vampire old_m) ->
            let open Vampire.Analyzed_graph in
            js_ctx.prev_node_map <- Some (Vampire old_m);
            let ids = js_ctx.box_selected_nodes in
            let new_m = Vampire.Analyzed_graph.(compress_list ids old_m) in
            js_ctx.cur_node_map <- Some (Vampire new_m);
            refresh_node_graphics ~height:main_dag_node_height
              ~label_affect_dag:false
              (Misc_utils.unwrap_opt !dagre_main)
              cy_main old_m new_m
            |> ignore;
            js_ctx.box_selected_nodes <- [] );
        Js._true);
  let decompress_button = Dom_html.getElementById_exn "decompressButton" in
  decompress_button##.onclick
  := Dom_html.handler (fun _ev ->
      ( match js_ctx.cur_node_map with
        | None ->
          ()
        | Some (Vampire old_m) -> (
            match js_ctx.selected_node with
            | None ->
              ()
            | Some id ->
              let open Vampire.Analyzed_graph in
              js_ctx.prev_node_map <- Some (Vampire old_m);
              let new_m =
                Vampire.Analyzed_graph.(decompress id Bottom_to_top old_m)
              in
              js_ctx.cur_node_map <- Some (Vampire new_m);
              refresh_node_graphics ~height:main_dag_node_height
                ~label_affect_dag:false
                (Misc_utils.unwrap_opt !dagre_main)
                cy_main old_m new_m
              |> ignore ) );
      Js._true);
  let recompress_button = Dom_html.getElementById_exn "recompressButton" in
  recompress_button##.onclick
  := Dom_html.handler (fun _ev ->
      ( match js_ctx.cur_node_map with
        | None ->
          ()
        | Some (Vampire old_m) -> (
            match js_ctx.selected_node with
            | None ->
              ()
            | Some id ->
              let open Vampire.Analyzed_graph in
              js_ctx.prev_node_map <- Some (Vampire old_m);
              let new_m = recompress id Bottom_to_top old_m in
              js_ctx.cur_node_map <- Some (Vampire new_m);
              refresh_node_graphics ~height:main_dag_node_height
                ~label_affect_dag:false
                (Misc_utils.unwrap_opt !dagre_main)
                cy_main old_m new_m
              |> ignore ) );
      Js._true);
  let toggle_label_button = Dom_html.getElementById_exn "toggleLabelButton" in
  toggle_label_button##.onclick
  := Dom_html.handler (fun _ev ->
      ( match js_ctx.cur_node_map with
        | None ->
          ()
        | Some (Vampire old_m) -> (
            match js_ctx.selected_node with
            | None ->
              ()
            | Some id ->
              let open Vampire.Analyzed_graph in
              js_ctx.prev_node_map <- Some (Vampire old_m);
              let v = get_label_visibility id old_m in
              let new_m = update_label_visibility ~ids:[id] (not v) old_m in
              js_ctx.cur_node_map <- Some (Vampire new_m);
              refresh_node_graphics ~height:main_dag_node_height
                ~label_affect_dag:true
                (Misc_utils.unwrap_opt !dagre_main)
                cy_main old_m new_m
              |> ignore ) );
      Js._true);
  let toggle_label_skip_layout_calc_button =
    Dom_html.getElementById_exn "toggleLabelSkipLayoutCalcButton"
  in
  toggle_label_skip_layout_calc_button##.onclick
  := Dom_html.handler (fun _ev ->
      ( match js_ctx.cur_node_map with
        | None ->
          ()
        | Some (Vampire old_m) -> (
            match js_ctx.selected_node with
            | None ->
              ()
            | Some id ->
              let open Vampire.Analyzed_graph in
              js_ctx.prev_node_map <- Some (Vampire old_m);
              let v = get_label_visibility id old_m in
              let new_m = update_label_visibility ~ids:[id] (not v) old_m in
              js_ctx.cur_node_map <- Some (Vampire new_m);
              refresh_node_graphics ~height:main_dag_node_height
                ~redo_layout:false
                (Misc_utils.unwrap_opt !dagre_main)
                cy_main old_m new_m
              |> ignore ) );
      Js._true);
  let explain_chain_button =
    Dom_html.getElementById_exn "explainChainButton"
  in
  explain_chain_button##.onclick
  := Dom_html.handler (fun _ev ->
      Js_utils.set_display ~id:single_formula_box_ID ~on:true;
      Js_utils.set_display ~id:single_nodeAST_ID ~on:false;
      Js_utils.set_display ~id:nodeAST1_ID ~on:false;
      Js_utils.set_display ~id:nodeAST2_ID ~on:false;
      Js_utils.set_display ~id:chain_explanation_box_ID ~on:true;
      Js_utils.set_display ~id:attack_trace_box_ID ~on:false;
      Js_utils.set_display ~id:main_graph_display_ID ~on:true;
      Js_utils.set_display ~id:main_text_display_ID ~on:false;
      ( match js_ctx.cur_node_map with
        | None ->
          ()
        | Some (Vampire old_m) -> (
            match js_ctx.selected_node with
            | None ->
              ()
            | Some id ->
              let open Vampire in
              (* let explanations    = explain_construction_chain id old_m in
               * let explanation_str = grouped_derive_explanations_list_to_string explanations in *)
              let explanations =
                List.filter
                  (fun (e : derive_explanation) ->
                     e <> Nothing_to_explain && e <> Dont_know_how)
                  (explain_construction_single_chained id old_m)
              in
              let explanation_str =
                String.concat "\n"
                  (List.map derive_explanation_to_string explanations)
              in
              let chain_explanation_box =
                Js.Unsafe.global##.document##getElementById
                  chain_explanation_box_ID
              in
              chain_explanation_box##.innerHTML := Js.string explanation_str )
      );
      Js._true);
  let zoom_in_button = Dom_html.getElementById_exn "zoomInButton" in
  zoom_in_button##.onclick :=
    Dom_html.handler (fun _ev ->
        Cytoscape.zoom_in_by cy_main 0.05;
        Js._true);
  let zoom_in_button = Dom_html.getElementById_exn "zoomOutButton" in
  zoom_in_button##.onclick :=
    Dom_html.handler (fun _ev ->
        Cytoscape.zoom_out_by cy_main 0.05;
        Js._true);
  let pv_raw_attack_trace_button =
    Dom_html.getElementById_exn "pvRawAttackTraceButton"
  in
  pv_raw_attack_trace_button##.onclick
  := Dom_html.handler (fun _ev ->
      Js_utils.set_display ~id:single_formula_box_ID ~on:true;
      Js_utils.set_display ~id:single_nodeAST_ID ~on:false;
      Js_utils.set_display ~id:nodeAST1_ID ~on:false;
      Js_utils.set_display ~id:nodeAST2_ID ~on:false;
      Js_utils.set_display ~id:chain_explanation_box_ID ~on:false;
      Js_utils.set_display ~id:attack_trace_box_ID ~on:true;
      Js_utils.set_display ~id:main_graph_display_ID ~on:false;
      Js_utils.set_display ~id:main_text_display_ID ~on:true;
      Js_utils.set_display ~id:single_explanation_box_ID ~on:false;
      ( match js_ctx.pv_raw with
        | None ->
          ()
        | Some text ->
          let main_text_display =
            Js.Unsafe.global##.document##getElementById main_text_display_ID
          in
          main_text_display##.innerHTML := Js.string text );
      ( match js_ctx.cur_node_map with
        | Some (Vampire node_map) ->
          let attack_trace_box =
            Js.Unsafe.global##.document##getElementById attack_trace_box_ID
          in
          let text = attack_trace node_map in
          attack_trace_box##.innerHTML := Js.string text
        | _ ->
          () );
      Js._true);
  let pv_processed_attack_trace_button =
    Dom_html.getElementById_exn "pvProcessedAttackTraceButton"
  in
  pv_processed_attack_trace_button##.onclick
  := Dom_html.handler (fun _ev ->
      Js_utils.set_display ~id:single_formula_box_ID ~on:true;
      Js_utils.set_display ~id:single_nodeAST_ID ~on:false;
      Js_utils.set_display ~id:nodeAST1_ID ~on:false;
      Js_utils.set_display ~id:nodeAST2_ID ~on:false;
      Js_utils.set_display ~id:chain_explanation_box_ID ~on:false;
      Js_utils.set_display ~id:attack_trace_box_ID ~on:true;
      Js_utils.set_display ~id:main_graph_display_ID ~on:false;
      Js_utils.set_display ~id:main_text_display_ID ~on:true;
      Js_utils.set_display ~id:single_explanation_box_ID ~on:false;
      ( match js_ctx.pv_processed with
        | None ->
          ()
        | Some text ->
          let main_text_display =
            Js.Unsafe.global##.document##getElementById main_text_display_ID
          in
          main_text_display##.innerHTML := Js.string text );
      ( match js_ctx.cur_node_map with
        | Some (Vampire node_map) ->
          let attack_trace_box =
            Js.Unsafe.global##.document##getElementById attack_trace_box_ID
          in
          let text = attack_trace node_map in
          attack_trace_box##.innerHTML := Js.string text
        | _ ->
          () );
      Js._true);
  let knowledge_graph_button =
    Dom_html.getElementById_exn "knowledgeGraphButton"
  in
  knowledge_graph_button##.onclick
  := Dom_html.handler (fun _ev ->
      Js_utils.set_display ~id:single_formula_box_ID ~on:true;
      Js_utils.set_display ~id:single_nodeAST_ID ~on:true;
      Js_utils.set_display ~id:nodeAST1_ID ~on:false;
      Js_utils.set_display ~id:nodeAST2_ID ~on:false;
      Js_utils.set_display ~id:chain_explanation_box_ID ~on:false;
      Js_utils.set_display ~id:attack_trace_box_ID ~on:false;
      Js_utils.set_display ~id:main_graph_display_ID ~on:true;
      Js_utils.set_display ~id:main_text_display_ID ~on:false;
      Js_utils.set_display ~id:single_explanation_box_ID ~on:true;
      Js._true);
  (* let load_example_button = Dom_html.getElementById_exn "loadExample" in
   * load_example_button##.onclick := Dom_html.handler
   *     (fun _ev ->
   *        begin
   *          let example_selected = Js.to_string (Js.Unsafe.global##.document##getElementById (Js.string example_select_ID))##.value in
   *          match example_selected with
   *          | "xor-otp" -> Lwt_condition.signal js_ctx.vampire_file_ready Examples.xor_otp_vampire; Lwt_condition.signal js_ctx.pv_file_ready Examples.xor_otp_pv
   *          | "ch07"    -> Lwt_condition.signal js_ctx.vampire_file_ready Examples.ch07_vampire;    Lwt_condition.signal js_ctx.pv_file_ready Examples.ch07_pv
   *          | "lak06"   -> Lwt_condition.signal js_ctx.vampire_file_ready Examples.lak06_vampire;   Lwt_condition.signal js_ctx.pv_file_ready Examples.lak06_pv
   *          | "sm08"    -> Lwt_condition.signal js_ctx.vampire_file_ready Examples.sm08_vampire;    Lwt_condition.signal js_ctx.pv_file_ready Examples.sm08_pv
   *          | "shamir"  -> Lwt_condition.signal js_ctx.vampire_file_ready Examples.shamir_vampire;  Lwt_condition.signal js_ctx.pv_file_ready Examples.shamir_pv
   *          | _         -> ()
   *        end;
   *        Js._true
   *     ); *)
  ( Cytoscape.draw_test_graph cy_single_nodeAST;
    Cytoscape.draw_test_graph cy_main;
    (* let button = Dom_html.getElementById_exn "testButton" in *)
    (* button##.onclick := Dom_html.handler
     *     (fun _ev ->
     *        Js_utils.alert "Called from OCaml";
     *        (\* let debug_print = Js.Unsafe.global##.document##getElementById "debugPrint" in *\)
     *        (\* debug_print##.value := Js.string "Hello"; *\)
     *        Js._true
     *     ); *)
    Lwt.return_unit )
  |> ignore;
  let pv_file = Js.to_string Js.Unsafe.global##.pvFile in
  let tptp_file = Js.to_string Js.Unsafe.global##.tptpFile in
  Js_utils.console_log pv_file;
  Js_utils.console_log tptp_file;
  Lwt_condition.signal js_ctx.pv_file_ready pv_file;
  Lwt_condition.signal js_ctx.vampire_file_ready tptp_file;
  ()
