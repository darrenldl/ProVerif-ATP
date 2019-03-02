open Js_of_ocaml

class type node = object
  method label  : Js.js_string Js.t Js.readonly_prop
  method width  : int               Js.readonly_prop
  method height : int               Js.readonly_prop
  method x      : int               Js.prop
  method y      : int               Js.prop
end

class type t = object
  method setNode    : Js.js_string Js.t -> node Js.t -> unit Js.meth
  method removeNode : Js.js_string Js.t -> unit Js.meth
  method setEdge    : Js.js_string Js.t -> Js.js_string Js.t -> unit Js.meth
  method removeEdge : Js.js_string Js.t -> Js.js_string Js.t -> unit Js.meth
  method node       : Js.js_string Js.t -> node Js.t Js.meth
end

let make () : t Js.t =
  let graph_global = Js.Unsafe.global##.dagre##.graphlib##.Graph in
  let graph        = new%js graph_global in
  let ()           = graph##setGraph (object%js end) in
  let ()           = graph##setDefaultEdgeLabel (fun () -> object%js end) in
  graph

let set_node
    ?(height : int = 100)
    (graph   : t Js.t)
    ~(id     : string)
    ~(label  : string)
  : unit =
  let width  = (1 + (String.length label)) * 10 in
  (* let width  = 1 in *)
  let node = object%js
      val label     = Js.string label
      val width     = width
      val height    = height
      val mutable x = 0
      val mutable y = 0
    end
  in
  graph##setNode (Js.string id) node

let remove_node
    (graph : t Js.t)
    ~(id   : string)
  : unit =
  graph##removeNode (Js.string id)

let set_edge
    (graph   : t Js.t)
    ~(source : string)
    ~(target : string)
  : unit =
  graph##setEdge (Js.string source) (Js.string target)

let remove_edge
    (graph   : t Js.t)
    ~(source : string)
    ~(target : string)
  : unit =
  graph##removeEdge (Js.string source) (Js.string target)

let get_node_xy
    (graph : t Js.t)
    ~(id   : string)
  : int * int =
  let node = graph##node (Js.string id) in
  (node##.x, node##.y)

let layout
    (graph : t Js.t)
  : unit =
  let dagre_global = Js.Unsafe.global##.dagre in
  dagre_global##layout graph
