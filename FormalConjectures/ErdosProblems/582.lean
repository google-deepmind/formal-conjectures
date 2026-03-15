/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 582

*Reference:* [erdosproblems.com/582](https://www.erdosproblems.com/582)

Does there exist a graph $G$ which contains no $K_4$, and yet any $2$-colouring
of the edges produces a monochromatic $K_3$?

The question was originally posed by Erdős and Hajnal [ErHa67]. Existence was
proved by Folkman [Fo70]. The smallest such graph defines the Folkman number
$f(3,3;4)$, with current best bounds $21 \leq f(3,3;4) \leq 786$ due to
Bikov–Nenov [BiNe20] and Lange–Radziszowski–Xu [LRX14], respectively.

See also Problem 924 for the generalization to arbitrary numbers of colors and
clique sizes.

[ErHa67] Erdős, P., Hajnal, A., *Research Problem 2.5*. J. Comb. Theory (1967).

[Fo70] Folkman, J., *Graphs with monochromatic complete subgraphs in every edge coloring*.
SIAM J. Appl. Math. 18 (1970), 19-24.

[BiNe20] Bikov, A., Nenov, N., *On the independence number of (3,3)-Ramsey graphs and the
Folkman number $F_e(3,3;4)$*. Australas. J. Combin. (2020), 35-50.

[LRX14] Lange, A. R., Radziszowski, S. P., Xu, X., *Use of MAX-CUT for Ramsey arrowing of
triangles*. J. Combin. Math. Combin. Comput. (2014), 61-71.
-/

namespace Erdos582

/--
There exists a $K_4$-free graph $G$ such that for any $2$-colouring of the edges,
there is a monochromatic $K_3$. Existence was proved by Folkman [Fo70].

We formalize this as: there exists $n$ and a simple graph $G$ on $\operatorname{Fin} n$ that
is $K_4$-free, such that for any subgraph $H \leq G$ (representing one color class
in a $2$-coloring of the edges), either $H$ or the complementary subgraph $G \setminus H$
contains a triangle.
-/
@[category research solved, AMS 5]
theorem erdos_582 : answer(True) ↔
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.CliqueFree 4 ∧
        ∀ (H : SimpleGraph (Fin n)), H ≤ G →
          ¬H.CliqueFree 3 ∨ ¬(G \ H).CliqueFree 3 := by
  sorry

end Erdos582
