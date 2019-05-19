open Core_kernel

let string_filter (input : string) (ignore : string) : string =
  let pred c : bool = not (String.contains ignore c) in
  String.filter input ~f:pred

let join_with_comma (input : string list) : string =
  String.concat ~sep:"," input

let unwrap_opt (x : 'a option) : 'a =
  match x with Some x -> x | None -> failwith "Unexpected pattern"

let make_gen_id () : unit -> int =
  let counter = ref 0 in
  fun () ->
    let res = !counter in
    counter := !counter + 1;
    res

let unwrap_tuple_0 ((a, _) : 'a * 'b) : 'a = a

let unwrap_tuple_1 ((_, b) : 'a * 'b) : 'b = b

let compare_rev (x : 'a) (y : 'a) : int = -compare x y

let rec zip (l1 : 'a list) (l2 : 'a list) : 'a list =
  match (l1, l2) with
  | [], [] ->
      []
  | l, [] | [], l ->
      l
  | hd1 :: tl1, hd2 :: tl2 when hd1 = hd2 ->
      hd1 :: zip tl1 tl2
  | hd1 :: tl1, hd2 :: tl2 when not (Stdlib.List.mem hd1 tl2) ->
      hd1 :: zip tl1 (hd2 :: tl2)
  | hd1 :: tl1, hd2 :: tl2 when not (Stdlib.List.mem hd2 tl1) ->
      hd2 :: zip (hd1 :: tl1) tl2
  | hd1 :: tl1, hd2 :: tl2 ->
      hd1 :: zip tl1 (hd2 :: tl2)

let group_list (same_group : 'a -> 'a -> bool) (l : 'a list) : 'a list list =
  let rec aux (same_group : 'a -> 'a -> bool) (acc : 'a list list)
      (l : 'a list) =
    match l with
    | [] ->
        List.rev (Stdlib.List.map List.rev acc)
    | x :: xs ->
        let acc =
          match acc with
          | (y :: ys) :: accs when same_group x y ->
              (x :: y :: ys) :: accs
          | _ ->
              [x] :: acc
        in
        aux same_group acc xs
  in
  aux same_group [] l

let has_prefix (s : string) prefix =
  let prefix_len = String.length prefix in
  let s_len = String.length s in
  s_len >= prefix_len && Stdlib.String.sub s 0 prefix_len = prefix
