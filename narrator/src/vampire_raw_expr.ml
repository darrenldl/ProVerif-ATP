open Parser_components
open MParser
open Misc_utils
open Printf
open Expr_components

type expr =
  | Variable of identifier
  | Pred of string * expr
  | Function of string * expr list
  | UnaryOp of unary_op * expr
  | BinaryOp of binary_op * expr * expr
  | Quantified of quantifier * identifier list * expr
  | False
  | InsertedF of int list

let rec expr_to_string (e : expr) : string =
  match e with
  | Variable ident ->
    ident
  | Pred (name, arg) ->
    sprintf "%s(%s)" name (expr_to_string arg)
  | Function (name, params) ->
    sprintf "%s(%s)" name (join_with_comma (List.map expr_to_string params))
  | UnaryOp (op, expr) ->
    sprintf "%s%s" (unary_op_to_string op)
      ( match expr with
        | Variable _ as e ->
          expr_to_string e
        | Function _ as e ->
          expr_to_string e
        | UnaryOp _ as e ->
          expr_to_string e
        | _ as e ->
          sprintf "(%s)" (expr_to_string e) )
  | BinaryOp (op, l, r) ->
    sprintf "%s %s %s"
      ( match l with
        | Variable _ as e ->
          expr_to_string e
        | Function _ as e ->
          expr_to_string e
        | UnaryOp _ as e ->
          expr_to_string e
        | _ as e ->
          sprintf "(%s)" (expr_to_string e) )
      (binary_op_to_string op)
      ( match r with
        | Variable _ as e ->
          expr_to_string e
        | Function _ as e ->
          expr_to_string e
        | UnaryOp _ as e ->
          expr_to_string e
        | _ as e ->
          sprintf "(%s)" (expr_to_string e) )
  | Quantified (q, idents, e) ->
    sprintf "%s [%s] : %s" (quantifier_to_string q) (join_with_comma idents)
      (expr_to_string e)
  | False ->
    "$false"
  | InsertedF l ->
    String.concat "" (List.map string_of_int l)

module Parser : sig
  val expr_p : expr stateless_p
end = struct
  let parens (p : expr stateless_p) : expr stateless_p =
    skip_char '(' >> p >>= fun x -> skip_char ')' >> return x

  let prefix (sym : string) (op : unary_op) : (expr, unit) operator =
    Prefix
      (attempt
         ( spaces >> skip_string sym >> spaces
           >> return (fun x -> UnaryOp (op, x)) ))

  let infix (sym : string) (op : binary_op) : (expr, unit) operator =
    Infix
      ( attempt
          ( spaces >> skip_string sym >> spaces
            >> return (fun a b -> BinaryOp (op, a, b)) )
      , Assoc_left )

  let operators =
    [ [prefix "~" Not]
    ; [infix "&" And]
    ; [infix "|" Or]
    ; [infix "=>" Imply; infix "<=>" Iff]
    ; [infix "=" Eq]
    ; [infix "!=" Neq]
    ; [infix "<-" Subsume] ]

  let false_p = ignore_space (string "$false" >> return False)

  let solver_inserted_p =
    ignore_space
      ( char '{'
        >> sep_by (ignore_space (many1_chars digit)) (char ',')
        >>= fun l -> char '}' >> return (InsertedF (List.map int_of_string l)) )
    <|> ignore_space
      (many1_chars digit >>= fun x -> return (InsertedF [int_of_string x]))

  let rec atom_p s =
    (ignore_space (ident_p >>= fun ident -> return (Variable ident))) s

  and func_p s =
    (ignore_space
       ( ident_p
         >>= fun ident ->
         char '('
         >> sep_by1 expr_p (char ',')
         >>= fun params -> char ')' >> return (Function (ident, params)) ))
      s

  and quant_p s =
    ( choice [char '!' >> return Forall; char '?' >> return Exists]
      >>= fun quantifier ->
      spaces >> char '['
      >> sep_by ident_p (char ',')
      >>= fun idents ->
      char ']' >> spaces >> char ':' >> spaces >> expr_p
      >>= fun expr -> return (Quantified (quantifier, idents, expr)) )
      s

  and sub_expr_p s =
    choice
      [ attempt quant_p
      ; attempt func_p
      ; attempt (parens expr_p)
      ; attempt atom_p
      ; attempt false_p
      ; attempt solver_inserted_p ]
      s

  and expr_p s = expression operators sub_expr_p s
end
