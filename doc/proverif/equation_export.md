# Equation export

In the original version of ProVerif, equations specified using the equation construct, such as

```ocaml
equation forall m:bitstring, k:bitstring;
  dec(enc(m, k), k) = m.
```

are not present in the exported SPASS file.

We discovered, however, that the quations are readily available in the `Types.t_horn_state` struct, which is part of result produced by `Pitransl.transl` (see `pitransl.mli` for type signature). The `Types.t_horn_state` struct is named `horn_state` in `main.ml` and one of the struct passed to Spass export module.

So overall, it was a matter of adding the missing functions for exporting equations stored in `horn_state` to SPASS format. The functions added are

- `Spassout.output_eq`

  - Function for exporting a single equation

- `Spassout.output_eqs_and_rules` 

  - This replaces `Spassout.output_rules` in the original version, and outputs both equations as well as rules

The equation exporting functionality was added to SPASS module first for testing, and was added to TPTP module later as well.
