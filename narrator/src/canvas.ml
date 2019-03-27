type ('a, 'b) t =
  { sigma : 'a Sigma.t
  ; dag : 'a Dag.t }

let make (container_id : string) : ('a, 'b) t =
  {sigma = Sigma.make container_id; dag = Dag.make ()}

let add_node (canvas : ('a, 'b) t) ~(id : string) ~(label : string) : unit =
  Dag.set_node canvas.dag ~id ~label
