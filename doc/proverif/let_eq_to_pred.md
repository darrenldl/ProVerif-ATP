# Replace let binding with equality checks with predicate

We discussed the need of this transformation at [here](equation_check.md) briefly.

To reiterate, we lose part of the process when we do the following

```ocaml
let A =
  ... (* part 1 *)
  let (..., =CONST1, ...) = f(...) in
  ... (* part 2 *)
```

Specifically, part 2 of the process A would be missing in the exported SPASS/TPTP file.

We note that this happens even after the [let binding flattening transformation](let_binding_flatten.md). We first show the output after the first transformation in the following example.

```ocaml
let (=CONST1, x : bitstring) = f(a) in
  X (* true branch - let binding succeeds *)
else
  Y (* false branch - let binding fails *)
```

becomes

```ocaml
let (=CONST1) = tuple_2_get_0(f(a)) in (
  let y = tuple_2_get_1(f(a)) in
    X
  else
    Y
) else
  Y
```

Our speculation is that ProVerif tries to unify the constant `CONST1` with a function application, and causes failed export in absense of equation checking.

We resolve this by replacing the use of `=` with use of a equality predicate, so the above becomes

```ocaml
if eq(CONST1, tuple_2_get_0(f(a)) then (
  let y = tuple_2_get_1(f(a)) in
    X
  else
    Y
) else
  Y
```

where `eq` is defined as

```ocaml
clauses forall x:bitstring;
  eq(x, x).
```

## Runnable example


