type write_mode =
  | Append
  | Overwrite

type bfs_traversal_direction =
  | Top_to_bottom
  | Bottom_to_top

type root_type =
  | Top
  | Bottom

module type Base = sig
  type id

  val first_id : id

  val next_id : id -> id

  type data

  type node =
    | Data of data
    | Group

  val label_internal : id -> node -> string

  val color_internal : id -> node -> string

  val size_internal : id -> node -> int

  val node_shape_internal : id -> node -> Cytoscape.node_shape

  val id_to_string : id -> string
end

module type S = sig
  include Base

  type t

  type snapshot_diff =
    { removed_nodes : id list
    ; changed_nodes : id list
    ; new_nodes : id list }

  type node_record =
    { id : id
    ; node : node option
    ; parents : id list option
    ; children : id list option
    ; group : id option
    ; node_visible : bool option
    ; label_visible : bool option }

  type partial_travel_next_step =
    | Continue
    | Stop

  type 'a traversal_function =
    | Full_traversal of ('a -> id -> node -> t -> 'a * t)
    | Partial_traversal of
        ('a -> id -> node -> t -> partial_travel_next_step * 'a * t)
    | Full_traversal_pure of ('a -> id -> node -> t -> 'a)
    | Partial_traversal_pure of
        ('a -> id -> node -> t -> partial_travel_next_step * 'a)

  val gen_id : t -> id

  val empty : t

  val unwrap_data : node -> data

  val add_node :
    write_mode
    -> id
    -> node
    -> ?parents:id list
    -> ?children:id list
    -> ?group:id
    -> t
    -> t

  val add_node_via_record : write_mode -> node_record -> t -> t

  val add_nodes_via_records : write_mode -> node_record list -> t -> t

  val find_node : id -> t -> node

  val find_node_opt : id -> t -> node option

  val find_nodes : id list -> t -> node list

  val find_nodes_assoc : id list -> t -> (id * node) list

  val remove_node : id -> t -> t

  val remove_nodes : id list -> t -> t

  val find_group : id -> t -> id

  val find_group_members : id -> t -> id list

  val find_children : id -> t -> id list

  val find_parents : id -> t -> id list

  val filter : (id -> node -> t -> bool) -> t -> t

  val filter_first_opt : (id -> node -> t -> bool) -> t -> id option

  val find_root : root_type -> t -> id

  val find_root_opt : root_type -> t -> id option

  val diff : root_type -> t -> t -> t * t

  val linear_traverse :
    ?ids:id list -> 'a -> 'a traversal_function -> t -> 'a * t

  val linear_traverse_rev :
    ?ids:id list -> 'a -> 'a traversal_function -> t -> 'a * t

  val bfs_traverse :
    id -> 'a -> bfs_traversal_direction -> 'a traversal_function -> t -> 'a * t

  val bfs_traverse_rev :
    id -> 'a -> bfs_traversal_direction -> 'a traversal_function -> t -> 'a * t

  val take_snapshot : id -> t -> t

  val find_snapshot : id -> t -> t

  val find_snapshot_opt : id -> t -> t option

  val compress_list : id list -> t -> t

  val compress_bfs :
    ?compress_leaf:bool -> bfs_traversal_direction -> id -> t -> t

  val recompress : id -> bfs_traversal_direction -> t -> t

  val decompress : id -> bfs_traversal_direction -> t -> t

  val to_assoc_list : t -> (id * node) list

  val to_node_list : t -> node list

  val update_label_visibility : ?ids:id list -> bool -> t -> t

  val get_label_visibility : id -> t -> bool

  val refresh_node_graphics :
    height:int
    -> ?redo_layout:bool
    -> ?label_affect_dag:bool
    -> Dagre.t Js_of_ocaml.Js.t
    -> Cytoscape.t Js_of_ocaml.Js.t
    -> t
    -> t
    -> t

  val plot :
    height:int
    -> ?show_label:bool
    -> ?label_affect_dag:bool
    -> Dagre.t Js_of_ocaml.Js.t option
    -> Cytoscape.t Js_of_ocaml.Js.t
    -> t
    -> t
end

module Make (B : Base) :
  S with type id = B.id with type data = B.data with type node = B.node
