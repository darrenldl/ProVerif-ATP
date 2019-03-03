# TPTP export module

The TPTP export module is largely copied from the original SPASS export module.

The major difference would be axioms expressing pairwise inequality of variables/constants are added in this module (we did not port this back into the SPASS export module as we no longer use the SPASS export module after completion of TPTP module).

We discovered that the inequality between free variables/constants (which is assumed generally in the encoding) is not expressed in the TPTP output. This prevents discovery of certain attacks when certain output messages are predicated by an inequality check, such as the key server encoding used in `NSLPK-agree-A-to-B.pv` (the design of which is copied from ProVerif's examples)

```ocaml
let key_register_server =
  in(c, (host : bitstring, pk : bitstring));
  if host <> A && host <> B then (
    insert keys(host, pk)
  ).
```

More specifically, even if we provide a constant `E`, Vampire would not be able to use it as the host component of a message to satisfy the `key_register_server`'s requirement.

The implementation is very straightforward. Suppose we have free variables/constants a, b, c, we just add

- `a != b`

- `a != c`

- `b != c`

## Implementation

- Above is implemented in
  - `Tptpout.get_free_or_const_names` (for gathering the list of names)

  - `Tptpout.output_eqs_about_names_being_neq` (for iterating over the names and exporting inequalities of above form)
