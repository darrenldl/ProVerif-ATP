open MParser

let refutation_proof_p =
  many Vampire_raw_line.line_p >>= fun x -> eof >> return x

let parse_refutation_proof_channel (ic : in_channel) :
  Vampire_raw_line.line option list MParser.result =
  parse_channel refutation_proof_p ic ()

let parse_refutation_proof_string (input : string) :
  Vampire_raw_line.line option list MParser.result =
  parse_string refutation_proof_p input ()
