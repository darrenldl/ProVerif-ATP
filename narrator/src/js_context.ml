type node_graph = Vampire of Vampire.node_graph

type t =
  { pv_file_ready : string Lwt_condition.t
  ; vampire_file_ready : string Lwt_condition.t
  ; mutable selected_node : string option
  ; mutable box_selected_nodes : string list
  ; mutable full_node_map : node_graph option
  ; mutable prev_node_map : node_graph option
  ; mutable cur_node_map : node_graph option
  ; mutable pv_raw : string option
  ; mutable pv_processed : string option }

let make () : t =
  { pv_file_ready = Lwt_condition.create ()
  ; vampire_file_ready = Lwt_condition.create ()
  ; selected_node = None
  ; box_selected_nodes = []
  ; full_node_map = None
  ; prev_node_map = None
  ; cur_node_map = None
  ; pv_raw = None
  ; pv_processed = None }
