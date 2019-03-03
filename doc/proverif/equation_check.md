# Disabling of equation checking

## Motivation

In the original version of ProVerif where equation checking takes place, equations containing associative-commutative properties such as XOR cannot be used.

While this makes sense as ProVerif's internal solver cannot handle those properties, we want to remove this unnecessary restriction when ProVerif is only used as a translator and leave all equations handling to the external automated theorem prover such as Vampire.

## Experiment and modification

In our experiments, we discovered value of type `Types.eq_info` is attached to each equation which changes the handling workflow in `TermsEq.buildblocks`. This value in the original version can be adjusted via attaching `linear` or `convergent` when specifying the equation, such as

```ocaml
equation forall x:bitstring, y:bitstring, z:bitstring;
  xor(x, xor(y, z)) = xor(xor(x, y), z) [convergent].
```

More specifically, `TermsEq.buildblocks` skips certain checks depending on the `eq_info` value.

We added an extra variant `EqNocheck` to the type `Types.eq_info` and modified `TermsEq.buildblocks` to skip all checks when `eq_info` of the equation is of this value.

The `eq_info` value is attached by `Pitsyntax.check_equations`, we modified the function to simply tag all equations as `EqNoCheck` when ProVerif is running in export mode

However, destructor checks in `Pitsyntax` can still cause issues, specifically the following destructor checking functions

- `Pitsyntax.f_eq_tuple`

- `Pitsyntax.f_any`

- `Pitsyntax.f_eq_tuple`

used by functions such as `Pitsyntax.check-eq_term`.

We modified the three destructor checking functions to skip checks when ProVerif is running in export mode

## Ramifications

Disabling the checks allow us to export equations such as XOR axioms successfully, however, unification failures in process terms would render part of the process missing after translation. We note that in the original ProVerif where equation checking takes place, unification failures of such do not impact the translation for cases ProVerif can handle.

The unification failures we noticed would cause such issue are as follows

- Unification between a tuple (or data constructor more generally) and a function term, such as the use of `(x : bitstring, y : bitstring) = split(msg)` in the following example

  - ```ocaml
    fun split(bitstring) : bitstring.
    fun concat(bitstring, bitstring) : bitstring.
    
    equation forall x:bitstring, y:bitstring;
      split(concat(x, y)) = (x, y).
    
    let A =
      in(c, msg : bitstring);
      let (x : bitstring, y : bitstring) = split(msg) in
      ... (* the rest of A would be missing in the TPTP export file *)
    ```

- Unification between a constant/free variable and a function term, such as the use of `E = checksign(msg, pkS)` in the following example

  - ```ocaml
    fun pkey(bitstring) : bitstring.
    
    fun sign(bitstring, bitstring) : bitstring.
    fun checksign(bitstring, bitstring) : bitstring.
    
    equation forall m:bitstring, k:bitstring;
      checksign(sign(m, k), pkey(k)).
    
    const E : bitstring.
    
    let A =
      in(c, msg : bitstring);
      if E = checksign(msg, pkS) then
      ... (* the rest of A would be missing in the TPTP export file *)
    ```

We do not claim the above list to be exhaustive.

We note that for certain cases, using the `reductor` construct instead of `fun` and `equation` would resolve successfully, but it is not always obvious when to use which, and it requires manual examination of the TPTP output then modify the encoding as needed, defeating the core objective of automation.

We overall worked around these issues using abstract syntax tree (AST) modificaitons which are done automatically. Due to time constraint, we did not investigate the possibility of modifiying any of the core procedures.

The AST modifications are detailed [here](ast_mod.md).
