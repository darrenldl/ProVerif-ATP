open Lwt
open Js_of_ocaml

type node_shape =
  | Circle
  | Ellipse
  | Diamond
  | Rectangle

class type node_data =
  object
    method id : Js.js_string Js.t Js.readonly_prop
    (* method label : Js.js_string Js.t Js.readonly_prop *)
  end

class type position =
  object
    method x : int Js.readonly_prop

    method y : int Js.readonly_prop
  end

class type node =
  object
    method group : Js.js_string Js.t Js.readonly_prop

    method data : node_data Js.t Js.readonly_prop

    method position : position Js.t Js.prop

    method selected : bool Js.t Js.prop

    method selectable : bool Js.t Js.prop

    method locked : bool Js.t Js.prop

    method grabbable : bool Js.t Js.prop
  end

class type node_ret =
  object
    method id : Js.js_string Js.t Js.meth

    method data : node_data Js.t Js.meth

    method position_get : position Js.t Js.meth

    method position_set : position Js.t -> unit Js.meth
  end

class type edge_data =
  object
    method id : Js.js_string Js.t Js.readonly_prop

    method source : Js.js_string Js.t Js.readonly_prop

    method target : Js.js_string Js.t Js.readonly_prop
  end

class type edge =
  object
    method data : edge_data Js.t Js.readonly_prop
  end

class type edge_ret =
  object
    method id : Js.js_string Js.t Js.meth

    method data : edge_data Js.t Js.meth
  end

class type style =
  object
    method resetToDefault : style Js.t Js.meth

    method fromString : Js.js_string Js.t -> style Js.t Js.meth

    method selector : Js.js_string Js.t -> style Js.t Js.meth

    method style : Js.js_string Js.t -> Js.js_string Js.t -> style Js.t Js.meth

    method update : unit Js.meth
  end

class type t =
  object
    method add_node : node Js.t -> unit Js.meth

    method add_edge : edge Js.t -> unit Js.meth

    (* method style    : style Js.t -> unit Js.meth *)
    method destroy : unit Js.meth

    method remove_node : Js.js_string Js.t -> unit Js.meth

    method remove_edge : Js.js_string Js.t -> unit Js.meth

    method on :
         Js.js_string Js.t
      -> Js.js_string Js.t
      -> (event Js.t -> unit)
      -> unit Js.meth

    method on_noselect :
      Js.js_string Js.t -> (event Js.t -> unit) -> unit Js.meth

    method getElementById_node : Js.js_string Js.t -> node_ret Js.t Js.meth

    method getElementById_edge : Js.js_string Js.t -> edge_ret Js.t Js.meth

    method style : style Js.t Js.meth

    method pan_get : position Js.t Js.meth

    method pan : position Js.t -> unit Js.meth

    method zoom_get : float Js.meth

    method zoom : float -> unit Js.meth

    method startBatch : unit Js.meth

    method endBatch : unit Js.meth
  end

and event =
  object
    method cy : t Js.t Js.prop

    method _type : Js.js_string Js.t Js.prop

    method target_cy : t Js.t Js.prop

    method target_node : node_ret Js.t Js.prop

    method target_edge : edge_ret Js.t Js.prop
    (* method position        : position     Js.t Js.prop *)
  end

let default_style =
  {|
    node {
      /* label       : data(label); */
      text-valign : center;
      font-family: monospace;
      font-size   : 15;
      /* text-outline-color: #d3d3d3; */
      text-outline-color: #000000;
      text-outline-width: 0px;
      color: #000000;
      border-color: #000000;
    }
    edge {
      curve-style: bezier;
      target-arrow-shape: triangle;
      arrow-scale: 2;
    }
  |}

let make (container_id : string) : t Js.t =
  let container =
    Js.Unsafe.global##.document##getElementById (Js.string container_id)
  in
  let config =
    object%js
      val container = container

      val style = Js.string default_style
    end
  in
  let cy = Js.Unsafe.global##cytoscape config in
  cy

let zoom (cy : t Js.t) (level : float) : unit = cy##zoom level

let zoom_get (cy : t Js.t) : float = cy##zoom_get

let zoom_in_by (cy : t Js.t) (level : float) : unit =
  let level_old = zoom_get cy in
  zoom cy (level_old +. level)

let zoom_out_by (cy : t Js.t) (level : float) : unit =
  let level_old = zoom_get cy in
  zoom cy (level_old -. level)

let add_node (cy : t Js.t) ~(id : string) ~ (* ~(label : string) *)
                                          (x : int) ~(y : int) : unit =
  let data =
    object%js
      val id = Js.string id (* val label = Js.string label *)
    end
  in
  let position =
    object%js
      val x = x

      val y = y
    end
  in
  let node =
    object%js
      val group = Js.string "nodes"

      val data = data

      val mutable position = position

      val mutable selected = Js._false

      val mutable selectable = Js._true

      val mutable locked = Js._false

      val mutable grabbable = Js._true
    end
  in
  cy##add_node node

let get_node (cy : t Js.t) ~(id : string) : node_ret Js.t =
  cy##getElementById_node (Js.string id)

let remove_node (cy : t Js.t) ~(id : string) : unit =
  cy##remove_node (Js.string (Printf.sprintf "node[id = \"%s\"]" id))

let add_edge (cy : t Js.t) ~(id : string) ~(source : string) ~(target : string)
    : unit =
  let data =
    object%js
      val id = Js.string id

      val source = Js.string source

      val target = Js.string target
    end
  in
  let edge =
    object%js
      val data = data
    end
  in
  cy##add_edge edge

let get_edge (cy : t Js.t) ~(id : string) : edge_ret Js.t =
  cy##getElementById_edge (Js.string id)

let remove_edge (cy : t Js.t) ~(id : string) : unit =
  cy##remove_edge (Js.string (Printf.sprintf "edge[id = \"%s\"]" id))

let clear (cy : t Js.t) : unit = cy##remove_node (Js.string "node")

let on ?(selector : string option) (cy : t Js.t) ~(event : string)
    ~(handler : event Js.t -> unit) : unit =
  let handler : event Js.t -> unit =
   fun ev ->
    Lwt_js.yield () >>= (fun () -> handler ev; Lwt.return_unit) |> ignore
  in
  match selector with
  | None ->
      cy##on_noselect (Js.string event) handler
  | Some selector ->
      cy##on (Js.string event) (Js.string selector) handler

let style_update (cy : t Js.t) : unit = cy##style##update

let set_node_label ?(update_style : bool = true) (cy : t Js.t) ~(id : string)
    ~(label : string) : unit =
  (cy##style##selector (Js.string (Printf.sprintf "node[id=\"%s\"]" id)))##style
    (Js.string "label") (Js.string label)
  |> ignore;
  if update_style then style_update cy else ()

let set_node_color ?(update_style : bool = true) ?(id : string option)
    (cy : t Js.t) ~(color : string) : unit =
  ( match id with
  | None ->
      (cy##style##selector (Js.string "node"))##style
        (Js.string "background-color")
        (Js.string color)
  | Some id ->
      (cy##style##selector (Js.string (Printf.sprintf "node[id=\"%s\"]" id)))##style
        (Js.string "background-color")
        (Js.string color) )
  |> ignore;
  if update_style then style_update cy else ()

let set_node_size ?(update_style : bool = true) (cy : t Js.t) ~(id : string)
    ~(size : int) : unit =
  let size = Js.string (string_of_int size) in
  ((cy##style##selector (Js.string (Printf.sprintf "node[id=\"%s\"]" id)))##style
     (Js.string "width") size)##style
    (Js.string "height") size
  |> ignore;
  if update_style then style_update cy else ()

let set_node_position (cy : t Js.t) ~(id : string) ~(x : int) ~(y : int) : unit
    =
  let position =
    object%js
      val x = x

      val y = y
    end
  in
  (get_node cy ~id)##position_set position

let set_node_shape ?(update_style : bool = true) (cy : t Js.t) ~(id : string)
    ~(shape : node_shape) : unit =
  let shape =
    Js.string
      ( match shape with
      | Circle ->
          "ellipse"
      | Ellipse ->
          "ellipse"
      | Diamond ->
          "diamond"
      | Rectangle ->
          "rectangle" )
  in
  (cy##style##selector (Js.string (Printf.sprintf "node[id=\"%s\"]" id)))##style
    (Js.string "shape") shape
  |> ignore;
  if update_style then style_update cy else ()

let enable_node_border ?(update_style : bool = true) (cy : t Js.t)
    ~(id : string) : unit =
  let width = Js.string (string_of_int 4) in
  (cy##style##selector (Js.string (Printf.sprintf "node[id=\"%s\"]" id)))##style
    (Js.string "border-width") width
  |> ignore;
  if update_style then style_update cy else ()

let disable_node_border ?(update_style : bool = true) (cy : t Js.t)
    ~(id : string) : unit =
  let width = Js.string (string_of_int 0) in
  (cy##style##selector (Js.string (Printf.sprintf "node[id=\"%s\"]" id)))##style
    (Js.string "border-width") width
  |> ignore;
  if update_style then style_update cy else ()

let start_batch (cy : t Js.t) : unit = cy##startBatch

let end_batch (cy : t Js.t) : unit = cy##endBatch

let reset_style (cy : t Js.t) : unit =
  (cy##style##fromString (Js.string default_style))##update

let draw_test_graph (cy : t Js.t) : unit =
  add_node cy ~id:"n0" ~x:0 ~y:0;
  add_node cy ~id:"n1" ~x:100 ~y:100;
  add_node cy ~id:"n2" ~x:100 ~y:100;
  add_node cy ~id:"n3" ~x:200 ~y:200;
  add_node cy ~id:"n4" ~x:200 ~y:300;
  add_node cy ~id:"n5" ~x:200 ~y:400;
  add_edge cy ~id:"n0_n0" ~source:"n0" ~target:"n0";
  add_edge cy ~id:"n0_n1" ~source:"n0" ~target:"n1";
  add_edge cy ~id:"n2_n3" ~source:"n2" ~target:"n3";
  add_edge cy ~id:"n3_n4" ~source:"n3" ~target:"n4";
  add_edge cy ~id:"n4_n5" ~source:"n4" ~target:"n5";
  set_node_color cy ~id:"n0" ~color:"red";
  reset_style cy;
  set_node_color cy ~id:"n0" ~color:"red"
