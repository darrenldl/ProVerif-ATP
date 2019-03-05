# Narrator interface guide

## Tagged ProVerif + attack trace mode

## Raw ProVerif + attack trace mode

## Knowledge graph mode

#### Classifications

![narrator_knowledge_colour](narrator_knowledge_colour.png)

- Unsure

  - This is the default classification. Some nodes may remain Unsure after a run of the classification.

  - There is always a chance that Narrator cannot classify successfully. The classification algorithm overall is a best effort solution that tries to mimic how a human would classify these roughly based on things like annotations provided by the ATP, how the formulas are linked together. While we try to reduece these cases, we note we do not have a complete algorithm for classifying the role of each formula in the context of attack derivation.

- Axiom

  - These are formulas which declare the basic properties of
