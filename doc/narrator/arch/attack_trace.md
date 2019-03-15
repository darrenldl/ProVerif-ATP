# Attack trace extraction

Attack trace extraction hinges on the dependency analysis between the protocol steps via the knowledge graph. The algorithm works as follows.

- Collect all nodes representing a step

  - This is done via the filtering function of the knowledge graph

- Collect paths to goal from each step node

  - For each step node, get the possible paths from that node to the goal (root at bottom)

- Collect steps reachable in each path

  - The algorithm traverses each path from top to bottom (following the directed arrow), and at each traversed node, collects steps reachable upward (going upward means going against the directed arrow). This collection is done using the BFS traversal functions of the knowledge graph, and also forms a (partial) ordering of the steps.

- Combination of ordering

  - The orderings are combined by "zipping" the list of steps together. For example, for `[A, B, C]`, `[B, C, D, Z]`, `[B, D, E]`, a potential combined result would be `[A, B, C, D, E, Z]`. Zipping also implies that for steps that do not have a defined order between them, the order is arbitrarily resolved when calculating the total order.

Originally a simple BFS traversal from bottom to top is done to collect the steps, this however doesn't always work when there are are multiple paths going upward, as some paths might be shorter. As a result, the above approach is used where different orderings are extracted from all paths then combined.
