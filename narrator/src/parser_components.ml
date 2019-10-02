open MParser

type 'a stateless_p = ('a, unit) parser

let ignore_space (p : 'a stateless_p) : 'a stateless_p =
  spaces >> p >>= fun x -> spaces >> return x

let ident_char : char stateless_p = choice [letter; digit; char '_']

let rec ident_p s = choice [attempt begin_with_letter] s

and begin_with_letter s =
  ( letter
    >>= fun x ->
    many ident_char
    >>= fun y -> return (Core_kernel.String.of_char_list (x :: y)) )
    s
