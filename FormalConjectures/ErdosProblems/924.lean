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
# Erdős Problem 924

*Reference:* [erdosproblems.com/924](https://www.erdosproblems.com/924)

Let $k \geq 2$ and $l \geq 3$. Is there a graph $G$ which contains no $K_{l+1}$ such that
every $k$-colouring of the edges of $G$ contains a monochromatic copy of $K_l$?

A question of Erdős and Hajnal [Er69b][Er75b]. Folkman [Fo70] proved this
when $k = 2$. The case for general $k$ was proved by Nešetřil and Rödl [NeRo76].

See #582 for the special case $k = 2$, $l = 3$ and #966 for an arithmetic analogue.

[Er69b] Erdős, P., _Problems and results in chromatic graph theory_. Proof Techniques in
Graph Theory (1969), 27–35.

[Er75b] Erdős, P., _Problems and results on finite and infinite graphs_. Recent Advances in
Graph Theory (1975), 183–192.

[Fo70] Folkman, J., _Graphs with monochromatic complete subgraphs in every edge coloring_.
SIAM J. Appl. Math. 18 (1970), 19–24.

[NeRo76] Nešetřil, J. and Rödl, V., _The Ramsey property for graphs with forbidden complete
subgraphs_. J. Combin. Theory Ser. B 20 (1976), 243–249.
-/

namespace Erdos924

/--
Erdős Problem #924 [Er69b][Er75b]:

For all $k \geq 2$ and $l \geq 3$, there exists a $K_{l+1}$-free graph $G$ such that every
$k$-colouring of the edges of $G$ contains a monochromatic $K_l$.

Proved by Nešetřil and Rödl [NeRo76].
-/
@[category research solved, AMS 5]
theorem erdos_924 : answer(True) ↔
    ∀ (k : ℕ) (l : ℕ), k ≥ 2 → l ≥ 3 →
      ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
        G.CliqueFree (l + 1) ∧
          ∀ (c : Fin n → Fin n → Fin k),
            (∀ i j, c i j = c j i) →
            ∃ (a : Fin k) (S : Finset (Fin n)),
              G.IsNClique l S ∧
              ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → c x y = a := by
  sorry

end Erdos924
