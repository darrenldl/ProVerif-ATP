open Js_of_ocaml
open Lwt

let () =
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
        let text = Vampire.attack_trace node_map in
        attack_trace_box##.innerHTML := Js.string text;
        (* Vampire.resolve_vars_in_knowledge_nodes ~agent_id:"299" ~base_id:"343"
         *   ~result_id:"344" node_map
         * |> ignore; *)
        (* Vampire.resolve_vars_in_knowledge_nodes_w_agent ~agent_id:"446" ~base_id:"880"
         *   ~result_id:"32540" node_map
         * |> ignore;
         * Vampire.resolve_vars_in_knowledge_node_pair ~base_id:"880" ~result_id:"32540" node_map |> ignore; *)

        (* Vampire.resolve_vars_in_knowledge_nodes_w_agent ~agent_id:"407" ~base_id:"448"
         *   ~result_id:"880" node_map
         * |> ignore;
         * Vampire.resolve_vars_in_knowledge_node_pair ~base_id:"448" ~result_id:"880" node_map |> ignore; *)

        (* Vampire.resolve_vars_in_knowledge_nodes_w_agent ~agent_id:"323" ~base_id:"361"
         *   ~result_id:"448" node_map
         * |> ignore;
         * Vampire.resolve_vars_in_knowledge_node_pair ~base_id:"361" ~result_id:"448" node_map |> ignore; *)

        (* Vampire.resolve_vars_in_knowledge_nodes_w_agent ~agent_id:"309" ~base_id:"344"
         *   ~result_id:"446" node_map
         * |> ignore;
         * Vampire.resolve_vars_in_knowledge_node_pair ~base_id:"344" ~result_id:"446" node_map |> ignore; *)

        (* Vampire.resolve_vars_in_split ~base_id:"352" ~result_id:"361" node_map
         * |> ignore;
         * Vampire.resolve_vars_in_knowledge_node_pair ~base_id:"352" ~result_id:"361" node_map |> ignore; *)

        (* Vampire.resolve_vars_in_knowledge_nodes_w_agent ~agent_id:"299" ~base_id:"351"
         *   ~result_id:"352" node_map
         * |> ignore;
         * Vampire.resolve_vars_in_knowledge_node_pair ~base_id:"351" ~result_id:"352" node_map |> ignore; *)

        (* Vampire.resolve_vars_in_knowledge_nodes_w_agent ~agent_id:"299" ~base_id:"341"
         *   ~result_id:"351" node_map
         * |> ignore;
         * Vampire.resolve_vars_in_knowledge_node_pair ~base_id:"341" ~result_id:"351" node_map |> ignore; *)
        (* let base_node    = Vampire.Analyzed_graph.unwrap_data (Vampire.Analyzed_graph.find_node "446" node_map) in
         * let base_expr    = base_node.expr |> Vampire_analyzed_expr.remove_subsumptions in
         * Js_utils.console_log (Printf.sprintf "base_expr : %s" (Vampire_analyzed_expr.expr_to_string base_expr));
         * let rewrite_node = Vampire.Analyzed_graph.unwrap_data (Vampire.Analyzed_graph.find_node "880" node_map) in
         * let rewrite_expr = rewrite_node.expr |> Vampire_analyzed_expr.remove_subsumptions in
         * Js_utils.console_log (Printf.sprintf "rewrite_expr : %s" (Vampire_analyzed_expr.expr_to_string rewrite_expr));
         * let result_node  = Vampire.Analyzed_graph.unwrap_data (Vampire.Analyzed_graph.find_node "32540" node_map) in
         * let result_expr  = result_node.expr |> Vampire_analyzed_expr.remove_subsumptions in
         * Js_utils.console_log (Printf.sprintf "result_expr : %s" (Vampire_analyzed_expr.expr_to_string result_expr));
         * let pat_match_map =
         *   Vampire_analyzed_expr.pattern_multi_match
         *     (List.map Vampire_analyzed_expr.strip_not (Vampire_analyzed_expr.split_on_or rewrite_expr))
         *     (List.map Vampire_analyzed_expr.strip_not (Vampire_analyzed_expr.split_on_or base_expr @ Vampire_analyzed_expr.split_on_or result_expr))
         * in
         * Vampire_analyzed_expr.ExprMap.iter
         *   (fun k v ->
         *      Js_utils.console_log (Printf.sprintf "pat : %s, e : %s" (Vampire_analyzed_expr.expr_to_string k) (Vampire_analyzed_expr.expr_to_string v))
         *   )
         *   (Option.get pat_match_map); *)
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
                (Vampire.Explain.derive_explanation_to_string
                   (Vampire.Explain.explain_construction_single target_id m))
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
                  (Explain.explain_construction_single_chained id old_m)
              in
              let explanation_str =
                String.concat "\n"
                  (List.map Explain.derive_explanation_to_string explanations)
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
          let text = Vampire.attack_trace node_map in
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
          let text = Vampire.attack_trace node_map in
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
    Lwt.return_unit )
  |> ignore;
  let pv_file = Js.to_string Js.Unsafe.global##.pvFile in
  let tptp_file = Js.to_string Js.Unsafe.global##.tptpFile in
  Js_utils.console_log pv_file;
  Js_utils.console_log tptp_file;
  Lwt_condition.signal js_ctx.pv_file_ready pv_file;
  Lwt_condition.signal js_ctx.vampire_file_ready tptp_file;
  ()
