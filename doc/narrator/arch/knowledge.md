# Knowledge graph

Outside of graphical display, knowledge graph is the core data structure used as foundation in implementing attack trace extraction and explanation derivation. The construction of the full knowledge graph can be broken down into the following stages.

## Parsing

The translation from a refutation proof to the initial unclassified knowledge graph is very straightforward

ATP like Vampire attach a list of "source" formula IDs to each derived formula in the annotation section, these source IDs indicate formulas which the formula is derived from. If the source ID list is empty, then the formula is an axiom.

Example of axiom (no source IDs attached)

```ocaml
fof(f191,axiom,(
  ! [X0] : constr_ZERO = constr_xor(X0,X0)),
  file('CH07-tag-auth.p',unknown)).
```

Example of derived formula (`f191` is the source ID)

```ocaml
fof(f460,plain,(
  ( ! [X0] : (constr_ZERO = constr_xor(X0,X0)) )),
  inference(cnf_transformation,[],[f191])).
```

By interpreting these source IDs as "parents", we can draw a directed acyclic graph very easily

## Classification

After the previous stage, we have a graphical representation of relationship between the formulas, but since we are interpreting this as an attack, we want to know what role each formula plays in forming the attack. Narrator facilitiates this by classifying them automatically on a best-effort basis, this can be seen graphically by the colour coding of the nodes.

The classification algorithm uses a set of simple pattern based rules to infer the role of each formula. The rules shown below are applied from top to bottom.

- Classify negated goal

  - This classifies the negated objective done as part of resolution as `NegatedGoal`, and also all nodes underneath

- Classify goal

  - This classifies the original unnegated objective, normally a parent of the starting `NegatedGoal`

- Classify protocol step

  - This classifies both `ProtocolStep` and `InteractiveProtocolStep` by checking if the fomula contains any protocol step tag

- Classify axiom

  - This classifies equations and attack knowledge inference rules (in the form of implications) without parents as `Axiom`

- Classify rewriting rule

  - This classifies formulas as `Rewriting` if all of the parents are `Axiom` or `Rewriting`

- Classify initial knowledge

  - This classifies formulas representing public knowledge as `InitialKnowledge`

- Classify contradiction

  - This classifies the false symbol (`$false`) in the proof as `Contradiction`

- Classify knowledge

  - This classifies formulas as `Knowledge` if any of the parents is `ProtocolStep`, `InitialKnowledge` or `Knowledge`

- Classify alias

  - This classifies formulas of form `... <=> ...` as `Alias`. These formulas are introduced by Vampire's AVATAR architecture to utilise SAT/SMT solvers for improved capabilitiy.

- The rules above classify alias are run again once

## Rewrite conclusion

In a successful refutation, the conclusion is the false symbol (or contradiction)

While this is the standard style, this is unintuitive to interpet as a knowledge graph, as our expected conclusion is the successful attack

Narrator rewrites the conclusion of the knowledge graph while preserving the logical coherence
