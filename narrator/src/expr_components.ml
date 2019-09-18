type quantifier = Exists | Forall
(* type quantifier = Tptp_ast.fof_quantifier *)

type boundedness =
  | Unsure
  | Free
  | Existential
  | Universal

type identifier = string

(* type unary_op = Not *)

type unary_op = Tptp_ast.unary_op

(* type binary_op =
 *   | And
 *   | Or
 *   | Eq
 *   | Iff
 *   | Imply
 *   | Left_imply
 *   | Xor
 *   | Not_or
 *   | Not_and *)

(* type binary_op = Tptp_ast.binary_op *)

type binary_op = And | Or | Imply | Eq | Neq | Iff | Subsume

let quantifier_to_string = function
  | Forall -> "!"
  | Exists -> "?"

(* let quantifier_to_string = Tptp_ast.quantifier_to_string *)

(* let unary_op_to_string = function
 *   | Not -> "~" *)

let unary_op_to_string = Tptp_ast.unary_op_to_string

let binary_op_to_string = function
  | And  -> "&"
  | Or   -> "|"
  | Eq   -> "="
  | Iff  -> "<=>"
  | Imply -> "=>"
  | Neq -> "!="
  | Subsume -> "<~>"

(* let binary_op_to_string = function
 *   | And  -> "&"
 *   | Or   -> "|"
 *   | Eq   -> "="
 *   | Iff  -> "<=>"
 *   | Imply -> "=>"
 *   | Left_imply -> "<="
 *   | Xor -> "<~>"
 *   | Not_or -> "~|"
 *   | Not_and -> "~&" *)

(* let binary_op_to_string = Tptp_ast.binary_op_to_string *)
