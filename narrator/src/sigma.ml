open Js_of_ocaml

class type node =
  object
    method id : Js.js_string Js.t Js.readonly_prop

    method label : Js.js_string Js.t Js.readonly_prop

    method x : int Js.readonly_prop

    method y : int Js.readonly_prop

    method size : int Js.readonly_prop

    method color : Js.js_string Js.t Js.readonly_prop
  end

class type edge =
  object
    method id : Js.js_string Js.t Js.readonly_prop

    method source : Js.js_string Js.t Js.readonly_prop

    method target : Js.js_string Js.t Js.readonly_prop
  end

class type graph =
  object
    method addNode : node Js.t -> unit Js.meth

    method addEdge : edge Js.t -> unit Js.meth

    method clear : unit Js.meth
  end

class type t =
  object
    method graph : graph Js.t Js.prop

    method refresh : unit Js.meth
  end

let make (container_id : string) : t Js.t =
  let sigma_global = Js.Unsafe.global##.sigma in
  sigma_global##.settings##.labelThreshold := 1;
  new%js sigma_global (Js.string container_id)

let add_node (sigma : t Js.t) ~(id : string) ~(label : string) ~(x : int)
    ~(y : int) ~(size : int) ~(color : string) : unit =
  let node =
    object%js (self)
      val id = Js.string id

      val label = Js.string label

      val x = x

      val y = y

      val size = size

      val color = Js.string color
    end
  in
  sigma##.graph##addNode node

let add_edge (sigma : t Js.t) ~(id : string) ~(source : string)
    ~(target : string) : unit =
  let edge =
    object%js (self)
      val id = Js.string id

      val source = Js.string source

      val target = Js.string target
    end
  in
  sigma##.graph##addEdge edge

let refresh (sigma : t Js.t) : unit = sigma##refresh

let clear (sigma : t Js.t) : unit = sigma##.graph##clear

let draw_test_graph (sigma : t Js.t) : unit =
  clear sigma;
  add_node sigma ~id:"n0" ~label:"test 1" ~x:0 ~y:0 ~size:10 ~color:"#00f";
  add_node sigma ~id:"n1" ~label:"test 1" ~x:1 ~y:1 ~size:10 ~color:"#00f";
  add_node sigma ~id:"n2" ~label:"test 1" ~x:1 ~y:1 ~size:10 ~color:"#00f";
  add_node sigma ~id:"n3" ~label:"test 1" ~x:2 ~y:2 ~size:10 ~color:"#00f";
  add_node sigma ~id:"n4" ~label:"test 1" ~x:2 ~y:3 ~size:10 ~color:"#00f";
  add_node sigma ~id:"n5" ~label:"test 1" ~x:2 ~y:4 ~size:10 ~color:"#00f";
  add_edge sigma ~id:"n0_n0" ~source:"n0" ~target:"n0";
  add_edge sigma ~id:"n0_n1" ~source:"n0" ~target:"n1";
  add_edge sigma ~id:"n2_n3" ~source:"n2" ~target:"n3";
  add_edge sigma ~id:"n3_n4" ~source:"n3" ~target:"n4";
  add_edge sigma ~id:"n4_n5" ~source:"n4" ~target:"n5";
  refresh sigma
