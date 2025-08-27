# Graph Conjectures Collection

This directory groups a selection of conjectures from the WOWII database.
Each Lean file contains the formal statement together with placeholder proofs.
Below we list their informal formulations together with their current status in
the database (either `open` or `resolved`).

1. **Conjecture 1 (resolved).** If `G` is a simple connected graph, then the maximum
   number of leaves of a spanning tree `Ls(G)` satisfies
   `Ls(G) ≥ n(G) + 1 − 2·m(G)`, where `n(G)` is the number of vertices and
   `m(G)` is the size of a maximum matching.
2. **Conjecture 2 (open).** For a simple connected graph `G`,
   `Ls(G) ≥ 2·(l(G) − 1)`, where `l(G)` denotes the average independence
   number of the neighbourhoods of the vertices of `G`.
3. **Conjecture 3 (resolved).** If `G` is connected, then
   `Ls(G) ≥ gi(G) · max_temp(G)` where `gi(G)` is the independent domination
   number and `max_temp(G)` is the maximum of `deg(v)/(n(G) - deg(v))`.
4. **Conjecture 4 (resolved).** For a connected graph `G`, the number `Ls(G)` is at least
   `NG(G) − 1` where `NG(G)` is the minimum neighbourhood size of a non-edge.
5. **Conjecture 5 (resolved).** For a connected graph `G`, the value `Ls(G)` is at least
   the maximal size of a sphere of radius `radius(G)` around a centre of `G`.
6. **Conjecture 6 (resolved).** For a connected graph `G`,
   `Ls(G) ≥ 1 + n(G) − m(G) − a(G)` where `a(G)` is defined via independent
   sets.
7. **Conjecture 19 (open).** Let `b(G)` be the size of the largest induced bipartite
   subgraph. Then
   `b(G) ≥ FLOOR( average ecc(v) + maximum l(v) )`, where `ecc(v)` is the
   eccentricity and `l(v)` the independence number of the neighbourhood of `v`.
8. **Conjecture 34 (open).** For a connected graph `G`, let `path(G)` be the floor of
   the average distance. Then
   `path(G) ≥ ceil( distavg(G, center) + distavg(G, periphery) )`.
9. **Conjecture 40 (open).** If `G` is a nontrivial connected graph then the size of a
   largest induced forest `f(G)` satisfies
   `f(G) ≥ ceil((p(G) + b(G) + 1)/2)` where `p(G)` is the path cover number and
   `b(G)` the largest induced bipartite subgraph size.
10. **Conjecture 58 (open).** For a connected graph `G`,
    `f(G) ≥ ceil( b(G) / average l(v) )`.

This README is intended for temporary bookkeeping and we will delete once the development of the
WrittenOnTheWallII module is complete.
