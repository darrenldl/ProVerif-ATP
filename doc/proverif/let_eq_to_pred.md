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

## Implementation

Above is implemented in

- `Pitsyntax.add_eq_pred_decl` for defining the predicate eq

- `Pitsyntax.replace_let_eq_pat_match_with_if_eq` for the transformation described above

## Runnable example

We included a runnable example in the `examples/` directory named `let_eq_to_pred.pv`. The file's formatting may look odd as it was reformatted by reexporting using the `-log-pv-only` flag, but this allows easier comparison with the modified version by using tools like `diff`.

Content of `let_eq_to_pred.pv`

```ocaml
free c : channel.

const A1 : bitstring.
const A2 : bitstring.
const B1 : bitstring.
const B2 : bitstring.
const E1 : bitstring.
const E2 : bitstring.

fun split(bitstring) : bitstring.
fun concat(bitstring, bitstring) : bitstring.

equation
  forall x : bitstring, y : bitstring; 
    split(concat(x, y)) = (x, y).

fun d(bitstring, bitstring) : bitstring [data].

query 
  attacker((A1, A2, B1, B2)).

let A =
  in(c, msg : bitstring);
  let (=E1, (y : bitstring, =E2)) = split(msg) in (
    out(c, A1);
    0
  ) else (
    out(c, A2);
    0
  ).

let B =
  in(c, msg : bitstring);
  let d(=E1, d(y : bitstring, =E2)) = msg in (
    out(c, B1);
    0
  ) else (
    out(c, B2);
    0
  ).

process
  (
    A
  )
  | (
    B
  )
```

Content of `let_eq_to_pred.pv.export` , produced by `proverif -in pitype -out tptp -log-pv -o let_eq_to_pred.p let_eq_to_pred.pv`

```ocaml
const CONST_0 : bitstring.
const CONST_1 : bitstring.
const CONST_2 : bitstring.
const CONST_3 : bitstring.
const CONST_4 : bitstring.

pred eq(bitstring, bitstring).

clauses
  forall x : bitstring;
    eq(x, x).

fun d(bitstring, bitstring) : bitstring [data].
fun tuple_2_get_0(bitstring) : bitstring.

equation
  forall x0 : bitstring, x1 : bitstring; 
    tuple_2_get_0((x0, x1)) = x0.

fun tuple_2_get_1(bitstring) : bitstring.

equation
  forall x0 : bitstring, x1 : bitstring; 
    tuple_2_get_1((x0, x1)) = x1.

fun d_2_get_0(bitstring) : bitstring.

equation
  forall x0 : bitstring, x1 : bitstring; 
    d_2_get_0(d(x0, x1)) = x0.

fun d_2_get_1(bitstring) : bitstring.

equation
  forall x0 : bitstring, x1 : bitstring; 
    d_2_get_1(d(x0, x1)) = x1.

free c : channel.

const A1 : bitstring.
const A2 : bitstring.
const B1 : bitstring.
const B2 : bitstring.
const E1 : bitstring.
const E2 : bitstring.

fun split(bitstring) : bitstring.
fun concat(bitstring, bitstring) : bitstring.

equation
  forall x : bitstring, y : bitstring; 
    split(concat(x, y)) = (x, y).

query 
  attacker((A1, A2, B1, B2)).

let A =
  in(c, msg : bitstring);

  if eq(E1, tuple_2_get_0(split(msg))) then (
    let y : bitstring = tuple_2_get_0(tuple_2_get_1(split(msg))) in (

      if eq(E2, tuple_2_get_1(tuple_2_get_1(split(msg)))) then (
        out(c, A1);
        0
      ) else (
        out(c, A2);
        0
      )
    ) else (
      out(c, A2);
      0
    )
  ) else (
    out(c, A2);
    0
  ).

let B =
  in(c, msg : bitstring);

  if eq(E1, d_2_get_0(msg)) then (
    let y : bitstring = d_2_get_0(d_2_get_1(msg)) in (

      if eq(E2, d_2_get_1(d_2_get_1(msg))) then (
        out(c, B1);
        0
      ) else (
        out(c, B2);
        0
      )
    ) else (
      out(c, B2);
      0
    )
  ) else (
    out(c, B2);
    0
  ).

process
  (
    A
  )
  | (
    B
  )
```
