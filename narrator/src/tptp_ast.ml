exception ErrorWithMsg of string

type number =
  | Int of int
  | Rational of int * int
  | Real of float

type decl =
  | Annotated_formula of annotated_formula
  | Include of string * string list

and annotated_formula = Fof_annotated of fof_annotated

and fof_annotated =
  { name : string
  ; role : formula_role
  ; formula : fof_formula
  ; annotations : general_term option }

and general_term =
  | GT_single of general_data
  | GT_pair of general_data * general_data
  | GT_list of general_list

and general_data =
  | GD_word of string
  | GD_fun of string * general_term list
  | GD_var of string
  | GD_num of string
  | GD_dist_obj of string

and general_list = general_term list

and formula_role =
  | FR_axiom
  | FR_hypothesis
  | FR_definition
  | FR_assumption
  | FR_lemma
  | FR_theorem
  | FR_corollary
  | FR_conjecture
  | FR_negated_conjecture
  | FR_plain
  | FR_type
  | FR_fi_domain
  | FR_fi_functors
  | FR_fi_predicates
  | FR_unknown

and fof_formula =
  | FOF_F_binary of binary_op * fof_formula * fof_formula
  | FOF_F_unary of unary_op * fof_formula
  | FOF_F_quantified of fof_quantifier * string list * fof_formula
  | FOF_F_atomic of fof_term

and fof_term =
  | FOF_T_var of string
  | FOF_T_const of string
  | FOF_T_fun_app of string * fof_term list

and binary_op =
  | And
  | Or
  | Eq
  | Iff
  | Imply
  | Left_imply
  | Xor
  | Not_or
  | Not_and

and unary_op = Not

and fof_quantifier =
  [ `Forall
  | `Exists ]

and infix_op = Neq

let rec output_input oc v =
  match v with
  | Include (name, fs) ->
      Printf.fprintf oc "include %s : %s" name (String.concat ", " fs)
  | Annotated_formula f ->
      output_formula oc f

and output_formula oc f =
  match f with
  | Fof_annotated f ->
      Printf.fprintf oc "fof(%a)" output_fof_annotated f

and output_fof_annotated oc f =
  let {name; _} = f in
  Printf.fprintf oc "%s" name

let string_to_formula_role s =
  match s with
  | "axiom" ->
      FR_axiom
  | "hypothesis" ->
      FR_hypothesis
  | "definition" ->
      FR_definition
  | "assumption" ->
      FR_assumption
  | "lemma" ->
      FR_lemma
  | "theorem" ->
      FR_theorem
  | "corollary" ->
      FR_corollary
  | "conjecture" ->
      FR_conjecture
  | "negated_conjecture" ->
      FR_negated_conjecture
  | "plain" ->
      FR_plain
  | "type" ->
      FR_type
  | "fi_domain" ->
      FR_fi_domain
  | "fi_functors" ->
      FR_fi_functors
  | "fi_predicates" ->
      FR_fi_predicates
  | "unknown" ->
      FR_unknown
  | _ ->
      raise (ErrorWithMsg ("invalid formula role " ^ s))

let formula_role_to_string r =
  match r with
  | FR_axiom ->
      "axiom"
  | FR_hypothesis ->
      "hypothesis"
  | FR_definition ->
      "definition"
  | FR_assumption ->
      "assumption"
  | FR_lemma ->
      "lemma"
  | FR_theorem ->
      "theorem"
  | FR_corollary ->
      "corollary"
  | FR_conjecture ->
      "conjecture"
  | FR_negated_conjecture ->
      "negated_conjecture"
  | FR_plain ->
      "plain"
  | FR_type ->
      "type"
  | FR_fi_domain ->
      "fi_domain"
  | FR_fi_functors ->
      "fi_functors"
  | FR_fi_predicates ->
      "fi_predicates"
  | FR_unknown ->
      "unknown"

let rec decl_to_string d =
  match d with
  | Include (file, formulas) ->
      Printf.sprintf "include %s : %s." file (String.concat ", " formulas)
  | Annotated_formula f ->
      annotated_formula_to_string f

and annotated_formula_to_string f =
  match f with
  | Fof_annotated f ->
      Printf.sprintf "fof%s" (fof_annotated_to_string f)

and fof_annotated_to_string f =
  let {name; role; formula; annotations} = f in
  Printf.sprintf "(%s, %s, %s%s)" name
    (formula_role_to_string role)
    (fof_formula_to_string formula)
    ( match annotations with
    | None ->
        ""
    | Some a ->
        ", " ^ general_term_to_string a )

and fof_formula_to_string f =
  match f with
  | FOF_F_binary (op, l, r) ->
      Printf.sprintf "(%s %s %s)" (fof_formula_to_string l)
        (binary_op_to_string op) (fof_formula_to_string r)
  | FOF_F_unary (op, f) ->
      Printf.sprintf "%s %s" (unary_op_to_string op) (fof_formula_to_string f)
  | FOF_F_quantified (q, vars, f) ->
      Printf.sprintf "%s [%s] : %s" (quantifier_to_string q)
        (String.concat ", " vars) (fof_formula_to_string f)
  | FOF_F_atomic t ->
      fof_term_to_string t

and fof_term_to_string t =
  match t with
  | FOF_T_var s ->
      s
  | FOF_T_const s ->
      s
  | FOF_T_fun_app (f, args) ->
      Printf.sprintf "%s(%s)" f
        (String.concat ", " (List.map fof_term_to_string args))

and general_term_to_string t =
  match t with
  | GT_single d ->
      general_data_to_string d
  | GT_pair (d1, d2) ->
      Printf.sprintf "%s : %s"
        (general_data_to_string d1)
        (general_data_to_string d2)
  | GT_list l ->
      Printf.sprintf "[%s]"
        (String.concat ", " (List.map general_term_to_string l))

and general_data_to_string d =
  match d with
  | GD_word s ->
      s
  | GD_fun (f, args) ->
      Printf.sprintf "%s(%s)" f
        (String.concat ", " (List.map general_term_to_string args))
  | GD_var s ->
      s
  | GD_num s ->
      s
  | GD_dist_obj s ->
      s

and binary_op_to_string op =
  match op with
  | And ->
      "&"
  | Or ->
      "|"
  | Eq ->
      "="
  | Iff ->
      "<=>"
  | Imply ->
      "=>"
  | Left_imply ->
      "<="
  | Xor ->
      "<~>"
  | Not_or ->
      "~|"
  | Not_and ->
      "~&"

and unary_op_to_string op = match op with Not -> "~"

and quantifier_to_string q = match q with `Forall -> "!" | `Exists -> "?"
