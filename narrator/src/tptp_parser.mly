%{
  open Tptp_ast

  let remove_prefix prefix s =
    let prefix_len = String.length prefix in
    let s_len = String.length s in
    if s_len < prefix_len then
      s
    else
      if String.sub s 0 prefix_len = prefix then
        String.sub s prefix_len (s_len - prefix_len)
      else
        s

  let name_clean_up s =
    s
    |> remove_prefix "name_"
    |> remove_prefix "constr_"
    |> remove_prefix "pred_"
%}

%token EOF

(* Keywords *)
%token FOF
(*%token CNF
%token THF
%token TFF *)
%token INCLUDE

(* Punctuation *)
%token LEFT_PAREN
%token RIGHT_PAREN
%token COMMA
%token DOT
%token LEFT_BRACK
%token RIGHT_BRACK
%token COLON

(* Operators *)
%token FORALL
%token EXISTS
%token NOT
%token AND
%token VLINE
%token IFF
%token IMPLY
%token LEFT_IMPLY
%token XOR
%token NOTVLINE
%token NOTAND
%token STAR
%token PLUS

(* Predicates *)
%token EQ
%token NEQ
%token TRUE
%token FALSE

%token <string> SINGLE_QUOTED
%token <string> DISTINCT_OBJECT

%token <string> DOLLAR_WORD
%token <string> DOLLAR_DOLLAR_WORD
%token <string> UPPER_WORD
%token <string> LOWER_WORD

(* %token ARROW
%token LESS_SIGN *)

(*
%nonassoc IFF
%nonassoc IMPLY
%nonassoc LEFT_IMPLY
%nonassoc XOR
%nonassoc NOTVLINE
%nonassoc NOTAND
*)

%token <string> INTEGER
%token <string> REAL
%token <string> RATIONAL

%start <Tptp_ast.decl list> parse_decls

%%

parse_decls:
  | l = list(decl); EOF { l }

decl:
  | f = annotated_formula                                                     { Annotated_formula f }
  | INCLUDE; LEFT_PAREN; name = file_name; l = formula_selection; RIGHT_PAREN { Include (name, l) }

file_name:
  | s = SINGLE_QUOTED { s }

formula_selection:
  | { [] }
  | COMMA; LEFT_BRACK; l = name_list; RIGHT_BRACK { l }

name_list:
  | l = separated_list(COMMA, name) { l }

annotated_formula:
  | f = fof_annotated { Fof_annotated f }

fof_annotated:
  | FOF; LEFT_PAREN; name = name; COMMA; role = formula_role; COMMA; formula = fof_formula; ann = annotations; RIGHT_PAREN; DOT
  {
    { name;
      role;
      formula;
      annotations = ann;
    }
  }

formula_role:
  | x = LOWER_WORD { string_to_formula_role x }

fof_formula:
  | f = fof_logic_formula { f }

fof_logic_formula:
  | f = fof_binary_formula
  | f = fof_unary_formula
  | f = fof_unitary_formula
    { f }

fof_binary_formula:
  | f = fof_binary_nonassoc
  | f = fof_binary_assoc
    { f }

fof_binary_nonassoc:
  | l = fof_unit_formula; c = nonassoc_connective; r = fof_unit_formula
    { FOF_F_binary (c, l, r) }

nonassoc_connective:
  | IFF        { Iff }
  | IMPLY      { Imply }
  | LEFT_IMPLY { Left_imply }
  | XOR        { Xor }
  | NOTVLINE   { Not_or }
  | NOTAND     { Not_and }

fof_binary_assoc:
  | f = fof_or_formula
  | f = fof_and_formula
    { f }

fof_or_formula:
  | l = fof_unit_formula; VLINE; r = fof_unit_formula
  | l = fof_or_formula;   VLINE; r = fof_unit_formula { FOF_F_binary (Or, l, r) }

fof_and_formula:
  | l = fof_unit_formula; AND; r = fof_unit_formula
  | l = fof_and_formula;  AND; r = fof_unit_formula   { FOF_F_binary (And, l, r) }

fof_unary_formula:
  | c = unary_connective; f = fof_unit_formula        { FOF_F_unary (c, f) }
  | f = fof_infix_unary                               { f }

unary_connective:
  | NOT { Not }

fof_infix_unary:
  | l = fof_term; infix_inequality; r = fof_term      { FOF_F_unary (Not, FOF_F_binary (Eq, FOF_F_atomic l, FOF_F_atomic r)) }

fof_unit_formula:
  | f = fof_unitary_formula
  | f = fof_unary_formula
    { f }

fof_unitary_formula:
  | f = fof_quantified_formula
  | f = fof_atomic_formula
  | LEFT_PAREN; f = fof_logic_formula; RIGHT_PAREN
    { f }

fof_quantified_formula:
  | q = fof_quantifier; LEFT_BRACK; vs = fof_variable_list; RIGHT_BRACK; COLON; f = fof_unit_formula { FOF_F_quantified (q, vs, f) }

fof_quantifier:
  | FORALL { `Forall }
  | EXISTS { `Exists }

fof_variable_list:
  | l = separated_list(COMMA, variable) { l }

fof_atomic_formula:
  | f = fof_plain_atomic_formula
  | f = fof_defined_atomic_formula
  | f = fof_system_atomic_formula
    { f }

fof_plain_atomic_formula:
  | f = fof_plain_term
    { FOF_F_atomic f }

fof_defined_atomic_formula:
  | f = fof_defined_plain_formula
  | f = fof_defined_infix_formula
    { f }

fof_defined_plain_formula:
  | f = fof_defined_plain_term
    { FOF_F_atomic f }

fof_defined_infix_formula:
  | l = fof_term; p = defined_infix_pred; r = fof_term
    { FOF_F_binary (p, FOF_F_atomic l, FOF_F_atomic r) }

fof_system_atomic_formula:
  | t = fof_system_term { FOF_F_atomic t }

defined_infix_pred:
  | infix_equality { Eq }

infix_equality:
  | EQ  { }

infix_inequality:
  | NEQ { }

fof_term:
  | s = variable          { FOF_T_var s }
  | f = fof_function_term { f }

fof_function_term:
  | t = fof_plain_term
  | t = fof_defined_term
  | t = fof_system_term
    { t }

fof_plain_term:
  | c = constant { FOF_T_const (name_clean_up c) }
  | f = tptp_functor; LEFT_PAREN; args = fof_arguments; RIGHT_PAREN { FOF_T_fun_app (name_clean_up f, args) }

fof_defined_term:
  | t = defined_term { FOF_T_var t }
  | t = fof_defined_atomic_term { t }

fof_defined_atomic_term:
  | t = fof_defined_plain_term { t }

fof_defined_plain_term:
  | t = defined_constant { FOF_T_const (name_clean_up t) }
  | f = defined_functor; LEFT_PAREN; args = fof_arguments; RIGHT_PAREN { FOF_T_fun_app (name_clean_up f, args) }

variable:
  | s = UPPER_WORD { s }

defined_constant:
  | s = defined_functor { s }

defined_functor:
  | s = atomic_defined_word { s }

defined_term:
  | n = number { n }
  | d = DISTINCT_OBJECT { d }

fof_arguments:
  | l = separated_list(COMMA, fof_term) { l }

fof_system_term:
  | c = system_constant                                               { FOF_T_const c }
  | f = system_functor; LEFT_PAREN; args = fof_arguments; RIGHT_PAREN { FOF_T_fun_app (f, args) }

system_constant:
  | s = system_functor { s }

system_functor:
  | s = atomic_system_word { s }

constant:
  | s = tptp_functor { s }

tptp_functor:
  | s = atomic_word { s }

annotations:
  | { None }
  | COMMA; src = general_term { Some src }

general_term:
  | d = general_data { GT_single d }
  | d1 = general_data; COLON; d2 = general_data { GT_pair (d1, d2) }
  | l = general_list { GT_list l }

general_list:
  | LEFT_BRACK; l = separated_list(COMMA, general_term); RIGHT_BRACK { l }

general_data:
  | s = atomic_word                                                                   { GD_word s }
  | f = atomic_word; LEFT_PAREN; l = separated_list(COMMA, general_term); RIGHT_PAREN { GD_fun (f, l) }
  | s = UPPER_WORD                                                                    { GD_var s }
  | n = number                                                                        { GD_num n }
  | d = DISTINCT_OBJECT                                                               { GD_dist_obj d }

name:
  | s = atomic_word { name_clean_up s }
  | i = INTEGER { i }

atomic_word:
  | s = LOWER_WORD    { s }
  | s = SINGLE_QUOTED { s }

atomic_defined_word:
  | s = DOLLAR_WORD { s }

atomic_system_word:
  | s = DOLLAR_DOLLAR_WORD { s }

number:
  | x = INTEGER
  | x = RATIONAL
  | x = REAL
    { x }

(* number:
  | i = INTEGER  { Int (int_of_string i) }
  | r = RATIONAL { Scanf.sscanf r "%d/%d" (fun a b -> Rational (a, b)) }
  | r = REAL     { Real (float_of_string r) } *)
