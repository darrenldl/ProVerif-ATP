# Introduction of extra constants

This is a very straightforward transformation, it just adds five extra constants into the AST. We add this minor adjustment as we discovered Vampire does not instanciate variables, even with inclusion of axioms such as `fof(a, axiom, ?[X] : ...)`, where `..` is usage of a (infix) predicate involving `X`.

There is no specific reason for using five - we need at least one extra constant accessible to the attacker for some attacks to work, and five just seemed to be a sane choice with redundancy.
