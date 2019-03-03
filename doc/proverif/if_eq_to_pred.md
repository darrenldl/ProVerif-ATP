# Replace if with equality checks with predicate

This very similar to the transformation for [let bindings with equality checks](let_eq_to_pred.md).

The transformation is as follows

```ocaml
if E = f(...) then
  ...
```

becomes

```ocaml
if eq(E, f(...)) then
  ...
```

where `eq` is defined as

```ocaml
clauses forall x:bitstring;
  eq(x, x).
```

## Implementation

Above is implemented in

- `Pitsyntax.replace_if_eq_with_if_eq_pred`

## Reason for dropping

Right now the above transformation is not used and is commented out.

We discovered that above transformation causes certain protocols to become unsolvable by Vampire, presumably due to the extra complexity (we did not investigate this further).

Thus we leave the decision to the user in this case.

If above transformation is explicitly required, you can use the following

```ocaml
let (=E) = f(...) in
  ...
```

instead of

```ocaml
if E = f(...) in
  ...
```

Transformation procedure for [let bindings with equality checks](let_eq_to_pred.md) will replace above with

```ocaml
if eq(E, f(...)) in
  ...
```

We did not investigate if there is a general way to tell when is safe to replace instances of `if E = f(...) then ... `with`if eq(E, f(...)) then ...`.
