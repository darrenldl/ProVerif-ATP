# Introduction of extra constants

This is a very straightforward transformation, it just adds five extra constants into the AST. We add this minor adjustment as we discovered Vampire does not instanciate variables, even with inclusion of axioms such as `fof(a, axiom, ?[X] : ...)`, where `..` is usage of a (infix) predicate involving `X`.

Just to be specific, the following lines are added to the top of the file, which can be observed in both `let_binding_flatten.pv.export` and `let_eq_to_pred.pv.export` in `examles/` directory.

```ocaml
const CONST_0 : bitstring.
const CONST_1 : bitstring.
const CONST_2 : bitstring.
const CONST_3 : bitstring.
const CONST_4 : bitstring.
```

There were not any specific reason for using five - we need at least one extra constant accessible to the attacker for some attacks to work, and five just seemed to be a sane choice with redundancy. We did not investigate if there's a general way to tell what's the minumum number of new constants/variables an attacker needs to instantiate in general for a given protocol for a successful attack.
