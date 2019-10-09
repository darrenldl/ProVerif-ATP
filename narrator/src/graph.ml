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
  S with type id = B.id with type data = B.data with type node = B.node =
struct
  include B

  module IdMap = Map.Make (struct
      type t = id

      let compare = compare
    end)

  module IdSet = Set.Make (struct
      type t = id

      let compare = compare
    end)

  type group_type =
    | BFS
    | List

  type t =
    { node_store : node IdMap.t
    ; label_visibility : bool IdMap.t
    ; node_visibility : bool IdMap.t
    ; group_lookup : id IdMap.t
    ; (* lookup group that an id belongs to *)
      group_members_lookup : id list IdMap.t
    ; (* lookup members that a group contains *)
      group_type_lookup : group_type IdMap.t
    ; snapshots : t IdMap.t
    ; children_lookup : id list IdMap.t
    ; parents_lookup : id list IdMap.t }

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

  module Helpers : sig
    val map_with_ids : ids:id list -> ('a -> 'a) -> 'a IdMap.t -> 'a IdMap.t

    val add_single_to_bucket :
      bucket_id:id -> data:'a -> 'a list IdMap.t -> 'a list IdMap.t

    val add_list_to_bucket :
      bucket_id:id -> data:'a list -> 'a list IdMap.t -> 'a list IdMap.t

    val add_single_to_buckets :
      bucket_ids:id list -> data:'a -> 'a list IdMap.t -> 'a list IdMap.t

    val add_list_to_buckets :
      bucket_ids:id list -> data:'a list -> 'a list IdMap.t -> 'a list IdMap.t

    val remove_single_from_bucket :
      data:'a -> bucket_id:id -> 'a list IdMap.t -> 'a list IdMap.t

    val remove_list_from_bucket :
      data:'a list -> bucket_id:id -> 'a list IdMap.t -> 'a list IdMap.t

    val remove_single_from_buckets :
      data:'a -> ?bucket_ids:id list -> 'a list IdMap.t -> 'a list IdMap.t

    val remove_list_from_buckets :
      data:'a list -> ?bucket_ids:id list -> 'a list IdMap.t -> 'a list IdMap.t

    val id_list : 'a IdMap.t -> id list

    val id_set : 'a IdMap.t -> IdSet.t

    val gen_id : t -> id

    val is_visible : id -> t -> bool

    val look_up_respect_vis : id -> 'a IdMap.t -> t -> 'a

    val look_up_opt_respect_vis : id -> 'a IdMap.t -> t -> 'a option

    val filter_invisible_ids : id list -> t -> id list

    val add_to_map_if_missing : id -> 'a -> 'a IdMap.t -> 'a IdMap.t

    val raise_exn_if_missing : ?msg:string -> id -> 'a IdMap.t -> 'a IdMap.t

    val find_with_default : id -> 'a -> 'a IdMap.t -> 'a
  end = struct
    let map_with_ids ~(ids : id list) (f : 'a -> 'a) (m : 'a IdMap.t) :
      'a IdMap.t =
      let rec aux ids f m =
        match ids with
        | [] ->
          m
        | x :: xs -> (
            match IdMap.find_opt x m with
            | None ->
              aux xs f m
            | Some d ->
              aux xs f (IdMap.add x (f d) m) )
      in
      aux ids f m

    let add_single_to_bucket ~(bucket_id : id) ~(data : 'a)
        (m : 'a list IdMap.t) : 'a list IdMap.t =
      match IdMap.find_opt bucket_id m with
      | None ->
        IdMap.add bucket_id [data] m
      | Some l ->
        IdMap.add bucket_id (List.sort_uniq compare (data :: l)) m

    let add_list_to_bucket ~(bucket_id : id) ~(data : 'a list)
        (m : 'a list IdMap.t) : 'a list IdMap.t =
      match IdMap.find_opt bucket_id m with
      | None ->
        IdMap.add bucket_id (List.sort_uniq compare data) m
      | Some l ->
        IdMap.add bucket_id (List.sort_uniq compare (data @ l)) m

    let add_single_to_buckets ~(bucket_ids : id list) ~(data : 'a)
        (m : 'a list IdMap.t) : 'a list IdMap.t =
      let rec aux ids data m =
        match ids with
        | [] ->
          m
        | x :: xs ->
          aux xs data (add_single_to_bucket ~bucket_id:x ~data m)
      in
      aux bucket_ids data m

    let add_list_to_buckets ~(bucket_ids : id list) ~(data : 'a list)
        (m : 'a list IdMap.t) : 'a list IdMap.t =
      let rec aux ids data m =
        match ids with
        | [] ->
          m
        | x :: xs ->
          aux xs data (add_list_to_bucket ~bucket_id:x ~data m)
      in
      aux bucket_ids data m

    let remove_single_from_bucket ~(data : 'a) ~(bucket_id : id)
        (m : 'a list IdMap.t) : 'a list IdMap.t =
      let filter l = List.filter (fun x -> x <> data) l in
      match IdMap.find_opt bucket_id m with
      | None ->
        m
      | Some d ->
        IdMap.add bucket_id (filter d) m

    let remove_list_from_bucket ~(data : 'a list) ~(bucket_id : id)
        (m : 'a list IdMap.t) : 'a list IdMap.t =
      let filter l = List.filter (fun x -> not (List.mem x data)) l in
      match IdMap.find_opt bucket_id m with
      | None ->
        m
      | Some d ->
        IdMap.add bucket_id (filter d) m

    let remove_single_from_buckets ~(data : 'a) ?(bucket_ids : id list option)
        (m : 'a list IdMap.t) : 'a list IdMap.t =
      let filter l = List.filter (fun x -> x <> data) l in
      match bucket_ids with
      | None ->
        IdMap.map filter m
      | Some l ->
        map_with_ids ~ids:l filter m

    let remove_list_from_buckets ~(data : 'a list)
        ?(bucket_ids : id list option) (m : 'a list IdMap.t) : 'a list IdMap.t
      =
      let filter l = List.filter (fun x -> not (List.mem x data)) l in
      match bucket_ids with
      | None ->
        IdMap.map filter m
      | Some l ->
        map_with_ids ~ids:l filter m

    let id_list (m : 'a IdMap.t) : id list =
      let bindings = IdMap.bindings m in
      List.map (fun (id, _) -> id) bindings

    let id_set (m : 'a IdMap.t) : IdSet.t =
      let ids = id_list m in
      IdSet.of_list ids

    let gen_id (m : t) : id =
      match IdMap.max_binding_opt m.node_store with
      | None ->
        B.first_id
      | Some (id, _) ->
        B.next_id id

    let is_visible (id : id) (m : t) : bool = IdMap.find id m.node_visibility

    let add_to_map_if_missing (id : id) (v : 'a) (m : 'a IdMap.t) : 'a IdMap.t
      =
      match IdMap.find_opt id m with None -> IdMap.add id v m | Some _ -> m

    let raise_exn_if_missing ?(msg : string = "Entry is missing in map")
        (id : id) (m : 'a IdMap.t) : 'a IdMap.t =
      match IdMap.find_opt id m with None -> failwith msg | Some _ -> m

    let find_with_default (id : id) (default : 'a) (m : 'a IdMap.t) : 'a =
      match IdMap.find_opt id m with None -> default | Some x -> x

    let look_up_respect_vis (id : id) (m : 'a IdMap.t) (main : t) : 'a =
      let visible = find_with_default id true main.node_visibility in
      if visible then IdMap.find id m else failwith "Node is not visible"

    let look_up_opt_respect_vis (id : id) (m : 'a IdMap.t) (main : t) :
      'a option =
      let visible = find_with_default id true main.node_visibility in
      if visible then IdMap.find_opt id m else None

    let filter_invisible_ids (ids : id list) (m : t) : id list =
      let rec aux ids acc =
        match ids with
        | [] ->
          List.rev acc
        | x :: xs ->
          aux xs (if IdMap.find x m.node_visibility then x :: acc else acc)
      in
      aux ids []
  end

  let label (id : id) (node : node) (m : t) : string =
    let visible = IdMap.find id m.label_visibility in
    if visible then label_internal id node else ""

  let color (id : id) (node : node) (_m : t) : string = color_internal id node

  let size (id : id) (node : node) (_m : t) : int = size_internal id node

  let shape (id : id) (node : node) (_m : t) : Cytoscape.node_shape =
    node_shape_internal id node

  let gen_id = Helpers.gen_id

  let empty : t =
    { node_store = IdMap.empty
    ; label_visibility = IdMap.empty
    ; node_visibility = IdMap.empty
    ; group_lookup = IdMap.empty
    ; group_members_lookup = IdMap.empty
    ; group_type_lookup = IdMap.empty
    ; snapshots = IdMap.empty
    ; children_lookup = IdMap.empty
    ; parents_lookup = IdMap.empty }

  let unwrap_data (node : node) : data =
    match node with
    | Data data ->
      data
    | Group ->
      failwith "Expected data node"

  let append_parents_children_linkage ~(id : id) ~(parents : id list option)
      ~(children : id list option) (m : t) : t =
    let open Helpers in
    let {children_lookup; parents_lookup; _} = m in
    let children =
      match children with None -> [] | Some children -> children
    in
    let parents = match parents with None -> [] | Some parents -> parents in
    let children_lookup =
      children_lookup
      |> add_list_to_bucket ~bucket_id:id ~data:children
      |> add_single_to_buckets ~bucket_ids:parents ~data:id
    in
    let parents_lookup =
      parents_lookup
      |> add_list_to_bucket ~bucket_id:id ~data:parents
      |> add_single_to_buckets ~bucket_ids:children ~data:id
    in
    {m with children_lookup; parents_lookup}

  let remove_parents_children_linkage ?(remove_parents_linkage : bool = true)
      ?(remove_children_linkage : bool = true) ~(id : id) (m : t) : t =
    let open Helpers in
    let {children_lookup; parents_lookup; _} = m in
    let children =
      match IdMap.find_opt id children_lookup with None -> [] | Some l -> l
    in
    let parents =
      match IdMap.find_opt id parents_lookup with None -> [] | Some l -> l
    in
    let children_lookup, parents_lookup =
      if remove_parents_linkage then
        let c =
          children_lookup
          |> remove_single_from_buckets ~data:id ~bucket_ids:parents
        in
        let p = parents_lookup |> IdMap.remove id in
        (c, p)
      else (children_lookup, parents_lookup)
    in
    let children_lookup, parents_lookup =
      if remove_children_linkage then
        let c = children_lookup |> IdMap.remove id in
        let p =
          parents_lookup
          |> remove_single_from_buckets ~data:id ~bucket_ids:children
        in
        (c, p)
      else (children_lookup, parents_lookup)
    in
    {m with children_lookup; parents_lookup}

  let remove_node (id : id) (m : t) : t =
    let open Helpers in
    let {node_store; group_lookup; group_members_lookup; _} = m in
    let group = IdMap.find_opt id group_lookup in
    let node_store = IdMap.remove id node_store in
    let group_lookup = group_lookup |> IdMap.remove id in
    let group_members_lookup =
      match group with
      | None ->
        group_members_lookup
      | Some group ->
        group_members_lookup
        |> remove_single_from_bucket ~data:id ~bucket_id:group
    in
    remove_parents_children_linkage ~id
      {m with node_store; group_lookup; group_members_lookup}

  let remove_nodes (ids : id list) (m : t) : t =
    let rec aux ids m =
      match ids with [] -> m | x :: xs -> aux xs (remove_node x m)
    in
    aux ids m

  let add_node_via_record (write_mode : write_mode) (record : node_record)
      (m : t) : t =
    let open Helpers in
    let {id; node; parents; children; group; node_visible; label_visible} =
      record
    in
    let { node_store
        ; group_lookup
        ; group_members_lookup
        ; node_visibility
        ; label_visibility
        ; _ } =
      m
    in
    let node_store =
      match node with
      | None ->
        raise_exn_if_missing id node_store
          ~msg:"Node is missing in node store"
      | Some node ->
        IdMap.add id node node_store
    in
    let group_lookup =
      match group with
      | None ->
        group_lookup
      | Some group ->
        IdMap.add id group group_lookup
    in
    let node_visibility =
      match node_visible with
      | None ->
        add_to_map_if_missing id true node_visibility
      | Some v ->
        IdMap.add id v node_visibility
    in
    let label_visibility =
      match label_visible with
      | None ->
        add_to_map_if_missing id false label_visibility
      | Some v ->
        IdMap.add id v label_visibility
    in
    let group_members_lookup =
      match group with
      | None ->
        group_members_lookup
      | Some group ->
        add_single_to_bucket ~bucket_id:group ~data:id group_members_lookup
    in
    let m =
      { m with
        node_store
      ; group_lookup
      ; group_members_lookup
      ; node_visibility
      ; label_visibility }
    in
    match write_mode with
    | Append ->
      append_parents_children_linkage ~id ~parents ~children m
    | Overwrite ->
      let remove_parents_linkage =
        match parents with None -> false | Some _ -> true
      in
      let remove_children_linkage =
        match children with None -> false | Some _ -> true
      in
      m
      (* deal with removing existing links first *)
      |> remove_parents_children_linkage ~remove_parents_linkage
        ~remove_children_linkage ~id
      (* now deal with adding the new links *)
      |> append_parents_children_linkage ~id ~parents ~children

  let add_node (write_mode : write_mode) (id : id) (node : node)
      ?(parents : id list option) ?(children : id list option)
      ?(group : id option) (m : t) : t =
    let record =
      { id
      ; node = Some node
      ; parents
      ; children
      ; group
      ; node_visible = None
      ; label_visible = None }
    in
    add_node_via_record write_mode record m

  let add_nodes_via_records (write_mode : write_mode)
      (records : node_record list) (m : t) : t =
    let rec aux records m =
      match records with
      | [] ->
        m
      | x :: xs ->
        aux xs (add_node_via_record write_mode x m)
    in
    aux records m

  let find_node (id : id) (m : t) : node =
    Helpers.look_up_respect_vis id m.node_store m

  let find_node_opt (id : id) (m : t) : node option =
    Helpers.look_up_opt_respect_vis id m.node_store m

  let find_nodes (ids : id list) (m : t) : node list =
    List.map Misc_utils.unwrap_opt
      (List.filter
         (fun node -> node <> None)
         (List.map (fun id -> find_node_opt id m) ids))

  let find_nodes_assoc (ids : id list) (m : t) : (id * node) list =
    List.map Misc_utils.unwrap_opt
      (List.filter
         (fun x -> x <> None)
         (List.map
            (fun id ->
               match find_node_opt id m with
               | None ->
                 None
               | Some n ->
                 Some (id, n))
            ids))

  let find_group (id : id) (m : t) : id =
    Helpers.look_up_respect_vis id m.group_lookup m

  let find_group_members (group_id : id) (m : t) : id list =
    Helpers.filter_invisible_ids
      (Helpers.look_up_respect_vis group_id m.group_members_lookup m)
      m

  let find_children (id : id) (m : t) : id list =
    Helpers.filter_invisible_ids
      (Helpers.look_up_respect_vis id m.children_lookup m)
      m

  let find_parents (id : id) (m : t) : id list =
    Helpers.filter_invisible_ids
      (Helpers.look_up_respect_vis id m.parents_lookup m)
      m

  let edges_of_node (id : id) (m : t) : (id * id) list =
    let parents = find_parents id m in
    let children = find_children id m in
    let parents_edges =
      List.fold_left (fun acc x -> (x, id) :: acc) [] parents
    in
    let children_edges =
      List.fold_left (fun acc x -> (id, x) :: acc) [] children
    in
    parents_edges @ children_edges

  let linear_traverse_internal ~(respect_visibility : bool)
      ?(ids : id list option) (ctx : 'a) (f : 'a traversal_function) (m : t) :
    'a * t =
    let rec aux look_up_opt ids ctx f m =
      match ids with
      | [] ->
        (ctx, m)
      | x :: xs -> (
          match look_up_opt x m.node_store m with
          | None ->
            aux look_up_opt xs ctx f m
          | Some n ->
            let next_step, new_ctx, new_m =
              match f with
              | Full_traversal f ->
                let new_ctx, new_m = f ctx x n m in
                (Continue, new_ctx, new_m)
              | Partial_traversal f ->
                f ctx x n m
              | Full_traversal_pure f ->
                (Continue, f ctx x n m, m)
              | Partial_traversal_pure f ->
                let next_step, new_ctx = f ctx x n m in
                (next_step, new_ctx, m)
            in
            if next_step = Stop then (new_ctx, new_m)
            else aux look_up_opt xs new_ctx f new_m )
    in
    let look_up_opt =
      if respect_visibility then Helpers.look_up_opt_respect_vis
      else fun id m _main -> IdMap.find_opt id m
    in
    let ids =
      match ids with None -> Helpers.id_list m.node_store | Some ids -> ids
    in
    aux look_up_opt ids ctx f m

  let linear_traverse ?(ids : id list option) (ctx : 'a)
      (f : 'a traversal_function) (m : t) : 'a * t =
    match ids with
    | None ->
      linear_traverse_internal ~respect_visibility:true ctx f m
    | Some ids ->
      linear_traverse_internal ~respect_visibility:true ~ids ctx f m

  let linear_traverse_ignore_vis ?(ids : id list option) (ctx : 'a)
      (f : 'a traversal_function) (m : t) : 'a * t =
    match ids with
    | None ->
      linear_traverse_internal ~respect_visibility:false ctx f m
    | Some ids ->
      linear_traverse_internal ~respect_visibility:false ~ids ctx f m

  let linear_traverse_rev ?(ids : id list option) (ctx : 'a)
      (f : 'a traversal_function) (m : t) : 'a * t =
    match ids with
    | None ->
      linear_traverse ctx f m
    | Some ids ->
      let ids = List.rev ids in
      linear_traverse ~ids ctx f m

  let linear_traverse_rev_ignore_vis ?(ids : id list option) (ctx : 'a)
      (f : 'a traversal_function) (m : t) : 'a * t =
    match ids with
    | None ->
      linear_traverse_ignore_vis ctx f m
    | Some ids ->
      let ids = List.rev ids in
      linear_traverse_ignore_vis ~ids ctx f m

  let bfs_traverse_internal ~(respect_visibility : bool) (id : id) (ctx : 'a)
      (direction : bfs_traversal_direction) (f : 'a traversal_function) (m : t)
    : 'a * t =
    let rec add_to_queue ids queue visited =
      match ids with
      | [] ->
        ()
      | x :: xs ->
        if not (IdSet.mem x !visited) then (
          Queue.push x queue;
          visited := IdSet.add x !visited );
        add_to_queue xs queue visited
    in
    let look_up_opt =
      if respect_visibility then Helpers.look_up_opt_respect_vis
      else fun id m _main -> IdMap.find_opt id m
    in
    let queue = Queue.create () in
    let visited = ref IdSet.empty in
    let ctx = ref ctx in
    let m = ref m in
    Queue.push id queue;
    visited := IdSet.add id !visited;
    while Queue.length queue > 0 do
      let id = Queue.pop queue in
      match look_up_opt id !m.node_store !m with
      | None ->
        ()
      | Some cur ->
        (* executes operation *)
        let next_step, new_ctx, new_m =
          match f with
          | Full_traversal f ->
            let new_ctx, new_m = f !ctx id cur !m in
            (Continue, new_ctx, new_m)
          | Partial_traversal f ->
            f !ctx id cur !m
          | Full_traversal_pure f ->
            (Continue, f !ctx id cur !m, !m)
          | Partial_traversal_pure f ->
            let next_step, new_ctx = f !ctx id cur !m in
            (next_step, new_ctx, !m)
        in
        m := new_m;
        ctx := new_ctx;
        if next_step = Stop then Queue.clear queue
        else
          let ids =
            match direction with
            | Top_to_bottom ->
              IdMap.find id !m.children_lookup
            | Bottom_to_top ->
              IdMap.find id !m.parents_lookup
          in
          add_to_queue ids queue visited
    done;
    (!ctx, !m)

  let bfs_traverse (id : id) (ctx : 'a) (direction : bfs_traversal_direction)
      (f : 'a traversal_function) (m : t) : 'a * t =
    bfs_traverse_internal ~respect_visibility:true id ctx direction f m

  let bfs_traverse_ignore_vis (id : id) (ctx : 'a)
      (direction : bfs_traversal_direction) (f : 'a traversal_function) (m : t)
    : 'a * t =
    bfs_traverse_internal ~respect_visibility:false id ctx direction f m

  let bfs_traverse_rev (id : id) (ctx : 'a)
      (direction : bfs_traversal_direction) (f : 'a traversal_function) (m : t)
    : 'a * t =
    let record_ids acc id _node _m = id :: acc in
    let ids, m =
      bfs_traverse id [] direction (Full_traversal_pure record_ids) m
    in
    let ctx, m = linear_traverse ~ids ctx f m in
    (ctx, m)

  let bfs_traverse_rev_ignore_vis (id : id) (ctx : 'a)
      (direction : bfs_traversal_direction) (f : 'a traversal_function) (m : t)
    : 'a * t =
    let record_ids acc id _node _m = id :: acc in
    let ids, m =
      bfs_traverse_ignore_vis id [] direction (Full_traversal_pure record_ids)
        m
    in
    let ctx, m = linear_traverse_ignore_vis ~ids ctx f m in
    (ctx, m)

  let take_snapshot (snapshot_id : id) (m : t) : t =
    let {snapshots; _} = m in
    let snapshots = IdMap.add snapshot_id m snapshots in
    {m with snapshots}

  let find_snapshot (snapshot_id : id) (m : t) : t =
    IdMap.find snapshot_id m.snapshots

  let find_snapshot_opt (snapshot_id : id) (m : t) : t option =
    IdMap.find_opt snapshot_id m.snapshots

  let update_single_node_visibility (id : id) (visibility : bool) (m : t) : t =
    let {node_visibility; _} = m in
    let node_visibility = IdMap.add id visibility node_visibility in
    {m with node_visibility}

  let update_list_node_visibility (ids : id list) (visibility : bool) (m : t) :
    t =
    let rec aux ids visibility m =
      match ids with
      | [] ->
        m
      | x :: xs ->
        aux xs visibility (update_single_node_visibility x visibility m)
    in
    aux ids visibility m

  let restore_node_visibility ?(ids : id list option) ~(old_m : t) (m : t) : t
    =
    let rec aux ids old_m m =
      match ids with
      | [] ->
        m
      | x :: xs ->
        let visibility =
          Helpers.find_with_default x false old_m.node_visibility
        in
        aux xs old_m (update_single_node_visibility x visibility m)
    in
    let ids =
      match ids with None -> Helpers.id_list m.node_store | Some l -> l
    in
    aux ids old_m m

  let filter (pred : id -> node -> t -> bool) (m : t) : t =
    let {node_store; _} = m in
    let pred id node =
      if Helpers.is_visible id m then pred id node m else true
    in
    let new_node_store = IdMap.filter pred node_store in
    let old_ids = Helpers.id_set node_store in
    let new_ids = Helpers.id_set new_node_store in
    let removed_ids = IdSet.diff old_ids new_ids in
    remove_nodes (IdSet.elements removed_ids) m

  let filter_first_opt (pred : id -> node -> t -> bool) (m : t) : id option =
    let res, _ =
      linear_traverse None
        (Partial_traversal_pure
           (fun _acc id node m ->
              if pred id node m then (Stop, Some id) else (Continue, None)))
        m
    in
    res

  let find_root_opt (root_type : root_type) (m : t) : id option =
    let pred =
      match root_type with
      | Top ->
        fun id _node m -> find_parents id m = []
      | Bottom ->
        fun id _node m -> find_children id m = []
    in
    filter_first_opt pred m

  let find_root (root_type : root_type) (m : t) : id =
    match find_root_opt root_type m with
    | Some x ->
      x
    | None ->
      failwith "No root found"

  let diff (root_type : root_type) (m1 : t) (m2 : t) : t * t =
    let same (id1 : id) (n1 : node) (m1 : t) (id2 : id) (n2 : node) (m2 : t) :
      bool =
      let n1_children_ids = find_children id1 m1 in
      let n2_children_ids = find_children id2 m2 in
      let n1_children = find_nodes n1_children_ids m1 in
      let n2_children = find_nodes n2_children_ids m2 in
      label id1 n1 m1 = label id2 n2 m2
      && List.length n1_children = List.length n2_children
      &&
      let combined =
        List.combine
          (List.combine n1_children_ids n1_children)
          (List.combine n1_children_ids n2_children)
      in
      List.fold_left
        (fun res ((id1, n1), (id2, n2)) ->
           res && label id1 n1 m1 = label id2 n2 m2)
        true combined
    in
    let rec remove_common (id1 : id) (n1 : node) (m1 : t) (id2 : id)
        (n2 : node) (m2 : t) : t * t =
      if same id1 n1 m1 id2 n2 m2 then
        let n1_children_ids = find_children id1 m1 in
        let n2_children_ids = find_children id2 m2 in
        let m1 = remove_node id1 m1 in
        let m2 = remove_node id2 m2 in
        let n1_children = find_nodes n1_children_ids m1 in
        let n2_children = find_nodes n2_children_ids m2 in
        let combined =
          List.combine
            (List.combine n1_children_ids n1_children)
            (List.combine n1_children_ids n2_children)
        in
        List.fold_left
          (fun (m1, m2) ((id1, n1), (id2, n2)) ->
             remove_common id1 n1 m1 id2 n2 m2)
          (m1, m2) combined
      else (m1, m2)
    in
    let id1 =
      match find_root_opt root_type m1 with
      | None ->
        failwith "No root for n1"
      | Some x ->
        x
    in
    let id2 =
      match find_root_opt root_type m2 with
      | None ->
        failwith "No root for n2"
      | Some x ->
        x
    in
    let res =
      remove_common id1 (find_node id1 m1) m1 id2 (find_node id2 m2) m2
    in
    res

  let snapshot_diff ?(group_invisible_nodes_as_removed : bool = true)
      ~(check_content : bool) ~(check_label_visibility : bool)
      ~(check_node_visibility : bool) ~(check_group : bool)
      ~(check_group_members : bool) ~(check_children : bool)
      ~(check_parents : bool) ~(prev : t) (cur : t) : snapshot_diff =
    let prev_ids = Helpers.id_list prev.node_store in
    let cur_ids = Helpers.id_list cur.node_store in
    let prev_id_set = IdSet.of_list prev_ids in
    let cur_id_set = IdSet.of_list cur_ids in
    let common_id_set = IdSet.inter prev_id_set cur_id_set in
    let common_ids = IdSet.elements common_id_set in
    (* record removed ids *)
    let removed_id_set = IdSet.diff prev_id_set common_id_set in
    let removed_ids = IdSet.elements removed_id_set in
    (* record new ids *)
    let new_id_set = IdSet.diff cur_id_set common_id_set in
    let new_ids = IdSet.elements new_id_set in
    (* go through common ids to check for differences *)
    let changed_ids, _ =
      linear_traverse_ignore_vis ~ids:common_ids []
        (Full_traversal_pure
           (fun acc id prev_node _ ->
              let different =
                (check_content && prev_node <> IdMap.find id cur.node_store)
                || check_label_visibility
                   && IdMap.find id prev.label_visibility
                      <> IdMap.find id cur.label_visibility
                || check_node_visibility
                   && IdMap.find id prev.node_visibility
                      <> IdMap.find id cur.node_visibility
                || check_group
                   && IdMap.find_opt id prev.group_lookup
                      <> IdMap.find_opt id cur.group_lookup
                || check_group_members
                   && IdMap.find_opt id prev.group_members_lookup
                      <> IdMap.find_opt id cur.group_members_lookup
                || check_children
                   && IdMap.find id prev.children_lookup
                      <> IdMap.find id cur.children_lookup
                || check_parents
                   && IdMap.find id prev.parents_lookup
                      <> IdMap.find id cur.parents_lookup
              in
              if different then id :: acc else acc))
        prev
    in
    (* move new invisible nodes to changed_ids if needed *)
    let removed_ids, changed_ids =
      if group_invisible_nodes_as_removed then
        linear_traverse_ignore_vis ~ids:changed_ids (removed_ids, [])
          (Full_traversal_pure
             (fun (removed_ids, changed_ids) id _ cur ->
                let visible = IdMap.find id cur.node_visibility in
                if visible then (removed_ids, id :: changed_ids)
                else (id :: removed_ids, changed_ids)))
          cur
        |> Misc_utils.unwrap_tuple_0
      else (removed_ids, changed_ids)
    in
    { removed_nodes = removed_ids
    ; changed_nodes = changed_ids
    ; new_nodes = new_ids }

  let add_group_type (group_id : id) (group_type : group_type) (m : t) : t =
    let {group_type_lookup; _} = m in
    let group_type_lookup = IdMap.add group_id group_type group_type_lookup in
    {m with group_type_lookup}

  let compress_internal (group_type : group_type) (ids : id list) (m : t) : t =
    let group_id = Helpers.gen_id m in
    (* quit if only one node or list is empty *)
    match ids with
    | [] | [_] ->
      m
    | _ ->
      let id_set = IdSet.of_list ids in
      (* add nodes to the new group *)
      let (), m =
        linear_traverse ~ids ()
          (Full_traversal
             (fun () id _node m ->
                let { group_lookup
                    ; group_members_lookup
                    ; children_lookup
                    ; parents_lookup
                    ; _ } =
                  m
                in
                let group_lookup = IdMap.add id group_id group_lookup in
                let group_members_lookup =
                  Helpers.add_single_to_bucket ~bucket_id:group_id ~data:id
                    group_members_lookup
                in
                (* let parents              = IdMap.find id parents_lookup in
                 * let children_lookup      =
                 *   Helpers.add_single_to_buckets ~bucket_ids:parents ~data:id children_lookup in *)
                ( ()
                , { m with
                    group_lookup
                  ; group_members_lookup
                  ; children_lookup
                  ; parents_lookup } )))
          m
      in
      (* collect parents and children *)
      let (parents, children), _ =
        linear_traverse ~ids ([], [])
          (Full_traversal_pure
             (fun (parents_acc, children_acc) id _node m ->
                let parents = find_parents id m in
                let children = find_children id m in
                let parents_acc =
                  List.filter (fun x -> not (IdSet.mem x id_set)) parents
                  :: parents_acc
                in
                let children_acc =
                  List.filter (fun x -> not (IdSet.mem x id_set)) children
                  :: children_acc
                in
                (parents_acc, children_acc)))
          m
      in
      let parents = List.concat parents in
      let children = List.concat children in
      m
      (* add group node *)
      |> add_node Append group_id Group ~parents ~children
      (* add group type *)
      |> add_group_type group_id group_type
      (* mark group members invisible *)
      |> update_list_node_visibility ids false
      (* mark group visible *)
      |> update_single_node_visibility group_id true

  let compress_list (ids : id list) (m : t) : t = compress_internal List ids m

  let compress_bfs ?(compress_leaf : bool = false)
      (direction : bfs_traversal_direction) (id : id) (m : t) : t =
    (* quit if the node itself is a leaf *)
    let is_leaf =
      match direction with
      | Bottom_to_top ->
        find_parents id m = []
      | Top_to_bottom ->
        find_children id m = []
    in
    if is_leaf then m
    else
      (* collect ids *)
      let ids, m =
        bfs_traverse id [] direction
          (Full_traversal
             (fun acc id _node m ->
                let is_group = IdMap.mem id m.group_members_lookup in
                let acc =
                  if is_group then id :: acc
                  else
                    let leaves =
                      match direction with
                      | Bottom_to_top ->
                        find_parents id m
                      | Top_to_bottom ->
                        find_children id m
                    in
                    match leaves with
                    | [] ->
                      if compress_leaf then id :: acc else acc
                    | _ ->
                      id :: acc
                in
                (acc, m)))
          m
      in
      let ids = id :: ids in
      compress_internal BFS ids m

  let recompress (id : id) (direction : bfs_traversal_direction) (m : t) : t =
    match IdMap.find_opt id m.group_lookup with
    | None ->
      m
    | Some group_id -> (
        match IdMap.find group_id m.group_type_lookup with
        | BFS ->
          (* make a snapshot first *)
          let m = take_snapshot group_id m in
          let group_members = IdMap.find group_id m.group_members_lookup in
          (* collect ids of all nodes in member trees *)
          let ids, m =
            linear_traverse ~ids:group_members []
              (Full_traversal_pure
                 (fun acc id _node m ->
                    let ids, _ =
                      bfs_traverse id [] direction
                        (Full_traversal_pure
                           (fun acc id _node m ->
                              if IdMap.mem id m.group_lookup then id :: acc
                              else acc))
                        m
                    in
                    ids :: acc))
              m
          in
          let ids = List.sort_uniq compare (List.concat ids) in
          m
          (* make group node visible *)
          |> update_single_node_visibility group_id true
          (* hide all nodes in member trees *)
          |> update_list_node_visibility ids false
        | List ->
          let group_members = IdMap.find group_id m.group_members_lookup in
          m
          (* make group node visible *)
          |> update_single_node_visibility group_id true
          (* hide all nodes in member trees *)
          |> update_list_node_visibility group_members false )

  let decompress (id : id) (direction : bfs_traversal_direction) (m : t) : t =
    match IdMap.find_opt id m.group_members_lookup with
    | None ->
      m
    | Some members -> (
        (* check if there was a snapshot taken *)
        match IdMap.find_opt id m.snapshots with
        | None ->
          m
          (* mark members visibile *)
          |> update_list_node_visibility members true
          (* mark group invisible *)
          |> update_single_node_visibility id false
        | Some old_m ->
          let group_members = IdMap.find id m.group_members_lookup in
          (* collect ids of all nodes in member trees *)
          let ids, m =
            linear_traverse_ignore_vis ~ids:group_members []
              (Full_traversal_pure
                 (fun acc id _node m ->
                    let ids, _ =
                      bfs_traverse_ignore_vis id [] direction
                        (Full_traversal_pure
                           (fun acc id _node m ->
                              if IdMap.mem id m.group_lookup then id :: acc
                              else acc))
                        m
                    in
                    ids :: acc))
              m
          in
          let ids = List.sort_uniq compare (List.concat ids) in
          m
          (* restore previous visibility of the group member trees *)
          |> restore_node_visibility ~ids ~old_m
          (* make group node invisible *)
          |> update_single_node_visibility id false )

  let to_assoc_list (m : t) : (id * node) list = IdMap.bindings m.node_store

  let to_node_list (m : t) : node list =
    List.map (fun (_, node) -> node) (IdMap.bindings m.node_store)

  let update_single_label_visibility (id : id) (visibility : bool) (m : t) : t
    =
    let {label_visibility; _} = m in
    let label_visibility = IdMap.add id visibility label_visibility in
    {m with label_visibility}

  let update_label_visibility ?(ids : id list option) (visibility : bool)
      (m : t) : t =
    let rec aux ids visibility m =
      match ids with
      | [] ->
        m
      | x :: xs ->
        aux xs visibility (update_single_label_visibility x visibility m)
    in
    let ids =
      match ids with None -> Helpers.id_list m.node_store | Some ids -> ids
    in
    aux ids visibility m

  let get_label_visibility (id : id) (m : t) : bool =
    IdMap.find id m.label_visibility

  let pos_table = Hashtbl.create 400

  let refresh_node_graphics ~(height : int) ?(redo_layout : bool = true)
      ?(label_affect_dag : bool = true) (dagre : Dagre.t Js_of_ocaml.Js.t)
      (cy : Cytoscape.t Js_of_ocaml.Js.t) (prev : t) (cur : t) : t =
    let remove_node () (id : id) (_node : node) (_cur : t) =
      let id_str = id_to_string id in
      if label_affect_dag then Dagre.remove_node dagre ~id:id_str;
      Cytoscape.remove_node cy ~id:id_str
    in
    let add_node_to_dagre () (id : id) (node : node) (cur : t) =
      let id_str = id_to_string id in
      let label = label id node cur in
      Dagre.set_node dagre ~height ~id:id_str ~label
    in
    let add_node_edges_to_dagre () (id : id) (_node : node) (cur : t) =
      let edges = edges_of_node id cur in
      List.iter
        (fun (id_src, id_dst) ->
           let id_src_str = id_to_string id_src in
           let id_dst_str = id_to_string id_dst in
           Dagre.set_edge dagre ~source:id_src_str ~target:id_dst_str)
        edges
    in
    let sync_dagre_xy_to_table () (id : id) (_node : node) (_m : t) : unit =
      let id_str = id_to_string id in
      let x, y = Dagre.get_node_xy dagre ~id:id_str in
      Hashtbl.add pos_table id (x, y)
    in
    let add_node_to_cy () (id : id) (_ : node) (_ : t) : unit =
      let id_str = id_to_string id in
      let x, y = Hashtbl.find pos_table id in
      Cytoscape.add_node cy ~id:id_str ~x ~y
    in
    let set_node_attributes_cy () (id : id) (node : node) (m : t) : unit =
      let id_str = id_to_string id in
      let label = label id node m in
      let color = color id node m in
      let size = size id node m in
      let shape = shape id node m in
      Cytoscape.set_node_label ~update_style:false cy ~id:id_str ~label;
      Cytoscape.set_node_color ~update_style:false cy ~id:id_str ~color;
      Cytoscape.set_node_size ~update_style:false cy ~id:id_str ~size;
      Cytoscape.set_node_shape ~update_style:false cy ~id:id_str ~shape
    in
    let add_edges_to_cy (edges : (id * id) list) : unit =
      List.iter
        (fun (id_src, id_dst) ->
           let id_src_str = id_to_string id_src in
           let id_dst_str = id_to_string id_dst in
           let id = Printf.sprintf "%s_%s" id_src_str id_dst_str in
           Cytoscape.add_edge cy ~id ~source:id_src_str ~target:id_dst_str)
        edges
    in
    let sync_node_xy_to_cy () (id : id) (_node : node) (_m : t) : unit =
      let id_str = id_to_string id in
      let x, y = Hashtbl.find pos_table id in
      Cytoscape.set_node_position cy ~id:id_str ~x ~y
    in
    let {removed_nodes; changed_nodes; new_nodes} =
      snapshot_diff ~check_content:false ~check_label_visibility:true
        ~check_node_visibility:true ~check_group:false
        ~check_group_members:false ~check_children:true ~check_parents:true
        ~prev cur
    in
    let all_cur_ids = Helpers.id_list cur.node_store in
    if redo_layout then (
      cur
      |> (fun m -> Cytoscape.start_batch cy; m)
      (* remove removed, changed nodes from Dagre and Cy *)
      |> linear_traverse_ignore_vis ~ids:removed_nodes ()
        (Full_traversal_pure remove_node)
      |> Misc_utils.unwrap_tuple_1
      |> linear_traverse_ignore_vis ~ids:changed_nodes ()
        (Full_traversal_pure remove_node)
      |> Misc_utils.unwrap_tuple_1
      |> (fun m ->
          if label_affect_dag then (
            m
            (* add changed, new nodes to Dagre *)
            |> linear_traverse ~ids:changed_nodes ()
              (Full_traversal_pure add_node_to_dagre)
            |> Misc_utils.unwrap_tuple_1
            |> linear_traverse ~ids:new_nodes ()
              (Full_traversal_pure add_node_to_dagre)
            |> Misc_utils.unwrap_tuple_1
            (* add edges of changed, new nodes to dagre *)
            |> linear_traverse ~ids:changed_nodes ()
              (Full_traversal_pure add_node_edges_to_dagre)
            |> Misc_utils.unwrap_tuple_1
            |> linear_traverse ~ids:new_nodes ()
              (Full_traversal_pure add_node_edges_to_dagre)
            |> Misc_utils.unwrap_tuple_1
            (* ask Dagre to compute the layout *)
            |> fun m -> Dagre.layout dagre; m )
          else m)
      (* sync x, y of all nodes from Dagre to map  *)
      |> linear_traverse ~ids:all_cur_ids ()
        (Full_traversal_pure sync_dagre_xy_to_table)
      |> Misc_utils.unwrap_tuple_1
      (* add changed, new nodes to Cy *)
      |> linear_traverse ~ids:changed_nodes ()
        (Full_traversal_pure add_node_to_cy)
      |> Misc_utils.unwrap_tuple_1
      |> linear_traverse ~ids:new_nodes () (Full_traversal_pure add_node_to_cy)
      |> Misc_utils.unwrap_tuple_1
      (* set node attributes in cy*)
      |> linear_traverse ~ids:changed_nodes ()
        (Full_traversal_pure set_node_attributes_cy)
      |> Misc_utils.unwrap_tuple_1
      |> linear_traverse ~ids:new_nodes ()
        (Full_traversal_pure set_node_attributes_cy)
      |> Misc_utils.unwrap_tuple_1
      (* add edges of changed, new nodes to Cy *)
      |> (fun m ->
          let edges =
            List.concat
              (List.map (fun id -> edges_of_node id m) changed_nodes)
            @ List.concat (List.map (fun id -> edges_of_node id m) new_nodes)
          in
          let edges = List.sort_uniq compare edges in
          add_edges_to_cy edges; m)
      (* |> linear_traverse            ~ids:changed_nodes () (Full_traversal_pure add_node_edges_to_cy) |> Misc_utils.unwrap_tuple_1 *)
      (* |> linear_traverse            ~ids:new_nodes     () (Full_traversal_pure add_node_edges_to_cy) |> Misc_utils.unwrap_tuple_1 *)

      (* update positions of all nodes in Cy *)
      |> linear_traverse ~ids:all_cur_ids ()
        (Full_traversal_pure sync_node_xy_to_cy)
      |> Misc_utils.unwrap_tuple_1
      |> fun m -> Cytoscape.end_batch cy; Cytoscape.style_update cy; m )
    else
      cur
      |> (fun m -> Cytoscape.start_batch cy; m)
      (* set node attributes in cy*)
      |> linear_traverse ~ids:changed_nodes ()
        (Full_traversal_pure set_node_attributes_cy)
      |> Misc_utils.unwrap_tuple_1
      |> linear_traverse ~ids:new_nodes ()
        (Full_traversal_pure set_node_attributes_cy)
      |> Misc_utils.unwrap_tuple_1
      |> fun m -> Cytoscape.end_batch cy; Cytoscape.style_update cy; m

  let plot ~(height : int) ?(show_label : bool option)
      ?(label_affect_dag : bool = true)
      (dagre : Dagre.t Js_of_ocaml.Js.t option)
      (cy : Cytoscape.t Js_of_ocaml.Js.t) (m : t) : t =
    let dagre =
      match dagre with None -> Dagre.make () | Some dagre -> dagre
    in
    let add_node_to_dagre () (id : id) (node : node) (m : t) : unit =
      let id_str = id_to_string id in
      let label = label id node m in
      Dagre.set_node dagre ~height ~id:id_str ~label
    in
    let add_edge_to_dagre () (id : id) (_node : node) (m : t) : unit =
      let id_str = id_to_string id in
      let children = find_children id m in
      List.iter
        (fun child_id ->
           let child_id = id_to_string child_id in
           Dagre.set_edge dagre ~source:id_str ~target:child_id)
        children
    in
    let sync_dagre_xy_to_node () (id : id) (_node : node) (_m : t) : unit =
      let id_str = id_to_string id in
      let x, y = Dagre.get_node_xy dagre ~id:id_str in
      Hashtbl.add pos_table id (x, y)
    in
    let add_node_to_cy () (id : id) (node : node) (m : t) : unit =
      let id_str = id_to_string id in
      let label = label id node m in
      let color = color id node m in
      let size = size id node m in
      let shape = shape id node m in
      let x, y = Hashtbl.find pos_table id in
      Cytoscape.add_node cy ~id:id_str ~x ~y;
      Cytoscape.set_node_label ~update_style:false cy ~id:id_str ~label;
      Cytoscape.set_node_color ~update_style:false cy ~id:id_str ~color;
      Cytoscape.set_node_size ~update_style:false cy ~id:id_str ~size;
      Cytoscape.set_node_shape ~update_style:false cy ~id:id_str ~shape
    in
    let add_edge_to_cy () (id : id) (_node : node) (m : t) : unit =
      let children = find_children id m in
      List.iter
        (fun child_id ->
           let child_id = id_to_string child_id in
           let source = id_to_string id in
           let target = child_id in
           let id = Printf.sprintf "%s_%s" (id_to_string id) child_id in
           Cytoscape.add_edge cy ~id ~source ~target)
        children
    in
    m
    |> (fun m -> Cytoscape.start_batch cy; m)
    |> (fun m ->
        match show_label with
        | None ->
          m
        | Some v ->
          update_label_visibility v m)
    |> (fun m -> Cytoscape.clear cy; m)
    |> (fun m ->
        if label_affect_dag then
          m
          |> linear_traverse () (Full_traversal_pure add_node_to_dagre)
          |> Misc_utils.unwrap_tuple_1
          |> linear_traverse () (Full_traversal_pure add_edge_to_dagre)
          |> Misc_utils.unwrap_tuple_1
          |> (fun m -> Dagre.layout dagre; m)
          |> linear_traverse () (Full_traversal_pure sync_dagre_xy_to_node)
          |> Misc_utils.unwrap_tuple_1
        else m)
    |> linear_traverse () (Full_traversal_pure add_node_to_cy)
    |> Misc_utils.unwrap_tuple_1
    |> linear_traverse () (Full_traversal_pure add_edge_to_cy)
    |> Misc_utils.unwrap_tuple_1
    |> fun m -> Cytoscape.end_batch cy; Cytoscape.style_update cy; m
end
