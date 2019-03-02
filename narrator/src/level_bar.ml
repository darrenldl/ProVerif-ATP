type handler = Dom_html.event Js.t -> bool Js.t

type t = {
  mutable levels : (int * string * handler) list;
  html_element   : Dom_html.element Js.t;
}

let make (container_id : string) : t =
  let html_element = Dom_html.getElementById_exn container_id in
  { levels       = [];
    html_element;
  }

let update_html (bar : t) : unit =
  List.map
    (fun (id, label, handler) -> Printf.sprintf "<button>%s</button>")

let add_level
    (bar      : t)
    ~(id      : int)
    ~(label   : string)
    ~(handler : handler)
  : unit =
  bar.levels <- (id, label, handler) :: bar.levels
