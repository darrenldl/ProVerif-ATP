# ProVerif pretty printer

The need of a pretty printer originated from the addition of the various abstract syntax tree (AST) modifications, where we wish to be able to verify whether the AST modifications were conducted as intended for debugging and adjustment. By having a standardised format, we can see the AST modifications made by simply using tools like `diff`, rather than going through the files manually.

The standardised format is also useful for sharing or collaborating protocol specifications as changes can be seen very easily by reexporting the copy of a file.

There are currently two flags which control the exporting behaviour

- `-log-pv-only` causes ProVerif to export the file after parsing (and before AST modifications take place) then exit, regardless of mode (export or solve)

- `-log-pv` causes ProVerif to export the copy of AST actually used for the translation to Horn clauses. This means if it's in export mode, it'll export the modified version of the AST.

The output name is currently fixed to `protocol.pv.export`, where `protocol.pv` is the input file. The exported copy prior to AST modification is named `protocol.pv.reprinted` in the `examples/` folder at the repository's root, the exported copy after AST modification is named `protocol.pv.processed`.

The following shows the diff output of `CH07-tag-auth.pv.reprinted` and `CH07-tag-auth.pv.processed`

```bash
$ diff CH07-tag-auth.pv.reprinted CH07-tag-auth.pv.processed
0a1,12
> const CONST_0 : bitstring.
> const CONST_1 : bitstring.
> const CONST_2 : bitstring.
> const CONST_3 : bitstring.
> const CONST_4 : bitstring.
> 
> pred eq(bitstring, bitstring).
> 
> clauses
>   forall x : bitstring;
>     eq(x, x).
> 
32a45,48
> const R_STEP_1 : bitstring.
> const R_STEP_2 : bitstring.
> const R_STEP_3 : bitstring.
> 
35c51
<   out(c, (QUERY, r1));
---
>   out(c, ((QUERY, r1), R_STEP_1));
43,44c59,60
<   out(c, right);
<   out(c, objective);
---
>   out(c, (right, R_STEP_2));
>   out(c, (objective, R_STEP_3));
46a63,66
> const sess_1_STEP_1 : bitstring.
> const sess_1_STEP_2 : bitstring.
> const sess_1_STEP_3 : bitstring.
> 
49c69
<   out(c, r1_s1);
---
>   out(c, (r1_s1, sess_1_STEP_1));
55,56c75,76
<   out(c, (r2_s1, left_s1));
<   out(c, right_s1);
---
>   out(c, ((r2_s1, left_s1), sess_1_STEP_2));
>   out(c, (right_s1, sess_1_STEP_3));
```

## Implementation

The pretty printer module is implemented in `pitprettyprint.ml` and `pitprettyprint.mli`

The main functions are

- `Pitprettyprint.tdecls_to_string`

- `Pitprettyprint.tproc_to_string_with_indent`

The module is largely copied from Narrator's implementation, but adapted to use ProVerif's internal type representation of the abstract syntax tree (Narrator uses its own type representation of the tree)
