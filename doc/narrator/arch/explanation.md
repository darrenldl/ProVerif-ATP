# Explanation mechanism

## Construction explanation

Explanation mechanism mainly aims to remove the manual labor of tracing source of knowledge by collecting and combining them in a human readable format. Currently only explanation of knowledge construction is implemented, the algorithm works as follows.

For each node to be explained, the node is considered as *"base"*. The algorithm currently only deals with *base* with exactly one child, and the child having exactly two parents (one being *base* itself). The child is called *"result"*, the other parent of the child is called *"agent"*. The naming comes from the intuition that in a (chemical) reaction, one would prepare a base material, then add agent and obtain some result. Each of *base*, *agent*, *result* may contain multiple expressions (formulas representing knowledge), which we'll simply name as *base exprs* and so on. With these terms defined, we have the following decision branches (first branch from top with satisfied condition is picked).

- If there are exactly one base expr, one agent expr, and one result expr, and the agent is a rewriting rule, then the step is concluded to be a rewriting step from result to base. (While this might seem backward, it's because knowledge are deconstructed in a refutation proof, so to explain construction, Narrator needs to go in the reverse order.)

- If there is exactly one base expr, then this is concluded to be a combine knowledge step

- If there is exactly one agent expr, and agent expr is a rewriting rule, and number of base exprs is same as the number of result exprs, then this is concluded to be a rewrite step with multiple simultaneous rewriting

- If number of base exprs is same as the number of agent exprs and result exprs combined, then this is concluded to be a gain knowledge step, where the agent only adds more information rather than modifying anything
