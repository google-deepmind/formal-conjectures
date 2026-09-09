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

import FormalConjecturesUtil

/-!
# Erdős Problem 570

*References:*
- [erdosproblems.com/570](https://www.erdosproblems.com/570)
- [EFRS93] Erdős, P. and Faudree, R. J. and Rousseau, C. C. and Schelp, R. H., Ramsey size linear
  graphs. Combin. Probab. Comput. (1993), 389-399.
- [GoKl94] Goddard, W. and Kleitman, D. J., An upper bound for the Ramsey numbers $r(K_3,G)$.
  Discrete Math. (1994), 177-182.
- [Si91] Sidorenko, A. F., An upper bound on the Ramsey number $r(K_3,G)$ depending only on
  the size of the graph $G$. J. Graph Theory (1991), 15-17.
- [Ja99] Jayawardene, C. J., Ramsey numbers related to small cycles. University of Memphis (1999).
- [CFMPP26] Cambie, S., Freschi, A., Morawski, P., Petrova, K. and Pokrovskiy, A.,
  Ramsey number of a cycle versus a graph of a given size. arXiv:2601.10238 (2026).
-/

open Filter

namespace Erdos570

/--
Let $k\geq 3$. Is it true that, if $m$ is sufficiently large, for any graph $H$ on $m$ edges
without isolated vertices,
$$R(C_k,H) \leq 2m+\left\lfloor\frac{k-1}{2}\right\rfloor?$$

This was proved for even $k$ by Erdős, Faudree, Rousseau, and Schelp [EFRS93]. This was proved
for $k=3$ independently by Goddard and Kleitman [GoKl94] and Sidorenko [Si91]. This was proved
for $k=5$ by Jayawardene [Ja99]. Finally it was proved for all odd $k\geq 7$ by Cambie, Freschi,
Morawski, Petrova, and Pokrovskiy [CFMPP26].

This problem is #35 in Ramsey Theory in the graphs problem collection.
-/
@[category research solved, AMS 5]
theorem erdos_570 : answer(True) ↔
    ∀ (k : ℕ) (hk : 3 ≤ k),
      ∀ᶠ (m : ℕ) in atTop,
        ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
          (∀ v, 0 < H.degree v) →
          H.edgeSet.ncard = m →
          SimpleGraph.graphRamsey (SimpleGraph.cycleGraph k) H ≤ 2 * m + (k - 1) / 2 := by
  sorry

-- TODO: Add variants of the problem.

end Erdos570
