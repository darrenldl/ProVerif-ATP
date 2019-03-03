# Let binding flattening

We discussed the need of this transformation at [here](equation_check.md) briefly.

To reiterate, we lose part of the process when we do the following

```ocaml
let A =
  ... (* part 1 *)
  let (x0 : bitstring, x1 : bitstring, ..., xn : bitstring) = f(...)
  ... (* part 2 *)
```

Specifically, part 2 of the process A would be missing in the exported SPASS/TPTP file.

Our speculation is that ProVerif tries to unify the tuple with a function application, and causes failed export in absense of equation checking.

Our approach was to remove the need entirely by adding code which performs the following transformation. We only show a two level nested tuple here, but how the transformation extends to other patterns and usage of data constructors should be obvious.

```ocaml
let (x : bitstring, (y : bitstring, z : bitstring)) = f(a) in
  X (* true branch - let binding succeeds *)
else
  Y (* false branch - let binding fails *)
```

becomes

```ocaml
let x = tuple_2_get_0(f(a)) in (
  let y = tuple_2_get_0(tuple_2_get_1(f(a))) in (
    let z = tuple_2_get_1(tuple_2_get_1(f(a))) in
      X
    else
      Y
  ) else
    Y
) else
 Y
```

where the tuple accessors are defined as

```ocaml
fun tuple_2_get_0(bitstring) : bitstring.
equation forall x0:bitstring, x1:bitstring;
  tuple_2_get_0((x0, x1)) = x0.

fun tuple_2_get_1(bitstring) : bitstring.
equation forall x0:bitstring, x1:bitstring;
  tuple_2_get_1((x0, x1)) = x1.
```

## Implementation

Above is implemented in

- `Pitsyntax.flatten_let_bindings`

## Runnable example

We included a runnable example in the `examples/` directory named `let_binding_flatten.pv`. The file's formatting may look odd as it was reformatted by reexporting using the `-log-pv-only` flag, but this allows easier comparison with the modified version by using tools like `diff`.

The example contains usage of both nested tuple and nested data constructors.

Content of `let_binding_flatten.pv`

```ocaml
const A1 : bitstring.
const A2 : bitstring.
const B1 : bitstring.
const B2 : bitstring.

free c : channel.

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
  let (x : bitstring, (y : bitstring, z : bitstring)) = split(msg) in (
    out(c, A1);
    0
  ) else (
    out(c, A2);
    0
  ).

let B =
  in(c, msg : bitstring);
  let d(x : bitstring, d(y : bitstring, z : bitstring)) = msg in (
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

Content of `let_binding_flatten.pv.export` , produced by `proverif -in pitype -out tptp -log-pv -o let_binding_flatten.p let_binding.pv`

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

const A1 : bitstring.
const A2 : bitstring.
const B1 : bitstring.
const B2 : bitstring.

free c : channel.

fun split(bitstring) : bitstring.
fun concat(bitstring, bitstring) : bitstring.

equation
  forall x : bitstring, y : bitstring; 
    split(concat(x, y)) = (x, y).

query 
  attacker((A1, A2, B1, B2)).

let A =
  in(c, msg : bitstring);
  let x : bitstring = tuple_2_get_0(split(msg)) in (
    let y : bitstring = tuple_2_get_0(tuple_2_get_1(split(msg))) in (
      let z : bitstring = tuple_2_get_1(tuple_2_get_1(split(msg))) in (
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
  let x : bitstring = d_2_get_0(msg) in (
    let y : bitstring = d_2_get_0(d_2_get_1(msg)) in (
      let z : bitstring = d_2_get_1(d_2_get_1(msg)) in (
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
