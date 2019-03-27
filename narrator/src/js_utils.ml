let alert (msg : string) : unit =
  Js_of_ocaml.Js.Unsafe.global##alert (Js_of_ocaml.Js.string msg)

let set_display ~(id : string) ~(on : bool) : unit =
  let obj =
    Js_of_ocaml.Js.Unsafe.global##.document##getElementById
      (Js_of_ocaml.Js.string id)
  in
  obj##.style##.display := Js_of_ocaml.Js.string (if on then "" else "none")

let console_log (msg : string) : unit =
  Js_of_ocaml.Js.Unsafe.global##.console##log (Js_of_ocaml.Js.string msg)
