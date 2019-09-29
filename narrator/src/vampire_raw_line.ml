open MParser
open Parser_components
open Printf

type extra_info =
  { l_node : string
  ; r_node : string
  ; l_ast_indices : int list
  ; r_ast_indices : int list }

type info =
  { descr : string
  ; parents : string list
  ; extra : extra_info option }

type line = string * Vampire_raw_expr.expr * info

let node_no : string stateless_p =
  many1_chars digit >>= fun x -> char '.' >> return x

let non_digit_p = many_chars (letter <|> space)

(* let int_p =
 *   many1_chars digit |>> int_of_string *)

let age_weight_selected_p =
  char '(' >> sep_by (many1_chars digit) (char ':') >> char ')'

let parent_brack : (string * string list) stateless_p =
  spaces >> char '[' >> non_digit_p
  >>= fun descr ->
  sep_by (many1_chars digit) (char ',')
  >>= fun x -> char ']' >> return (Core_kernel.String.strip descr, x)

let info_p : info stateless_p =
  spaces >> char '[' >> non_digit_p
  >>= fun descr ->
  let descr = Core_kernel.String.strip descr in
  ( if descr = "superposition" then
      many1_chars digit
      >>= fun e1 -> char ',' >> many1_chars digit >>= fun e2 -> return [e1; e2]
    else sep_by (many1_chars digit) (char ',') )
  >>= fun parents ->
  char ']'
  >> return {descr; parents; extra = None}
     <|> ( char ',' >> spaces >> many1_chars digit
           >>= fun l_node ->
           spaces >> string "into" >> spaces >> many1_chars digit
           >>= fun r_node ->
           char ',' >> spaces >> string "unify on" >> spaces >> string "(0)."
           >> sep_by (many1_chars digit) (char '.')
           >>= fun l_ast_indices ->
           spaces >> string "in" >> spaces >> many1_chars digit >> spaces
           >> string "and" >> spaces >> string "(0)."
           >> sep_by (many1_chars digit) (char '.')
           >>= fun r_ast_indices ->
           spaces >> string "in" >> spaces >> many1_chars digit >> char ']'
           >>
           let l_ast_indices = l_ast_indices |> List.map int_of_string in
           let r_ast_indices = r_ast_indices |> List.map int_of_string in
           return
             { descr
             ; parents
             ; extra = Some {l_node; r_node; l_ast_indices; r_ast_indices} } )

let line_p : line option stateless_p =
  choice
    [ attempt
        ( node_no
          >>= fun node_no ->
          spaces >> Vampire_raw_expr.Parser.expr_p
          >>= fun expr ->
          spaces
          >> optional age_weight_selected_p
          >> info_p
          >>= fun info -> many newline >> return (Some (node_no, expr, info)) )
    ; attempt (newline >> return None)
    ; attempt (spaces >> newline >> return None)
    ; attempt (char '%' >> many_until any_char newline >> return None)
    ; attempt (string "//" >> many_until any_char newline >> return None)
    ; attempt (string "----" >> many_until any_char eof >> return None) ]

let line_to_string (line : line option) : string =
  match line with
  | None ->
    "Blank line"
  | Some (node_no, expr, info) ->
    sprintf "%s. %s (%s) [%s]" node_no
      (Vampire_raw_expr.expr_to_string expr)
      info.descr
      (Misc_utils.join_with_comma info.parents)
