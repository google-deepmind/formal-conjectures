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
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Erdős Problem 552

*Reference:* [erdosproblems.com/552](https://www.erdosproblems.com/552)

Determine the Ramsey number $R(C_4, S_n)$, where $S_n = K_{1,n}$ is the star on
$n + 1$ vertices.

[BEFRS89] Burr, S. A., Erdős, P., Faudree, R. J., Rousseau, C. C., and Schelp, R. H.,
*Some complete bipartite graph-tree Ramsey numbers*,
Graph theory in memory of G. A. Dirac (Sandbjerg, 1985), 79–89, 1989.

[Pa75] Parsons, T. D., *Ramsey graphs and block designs. I*,
Trans. Amer. Math. Soc. (1975), 33–44.

[WSZR15] Wu, Y., Sun, Y., Zhang, R., and Radziszowski, S. P.,
*Ramsey numbers of C₄ versus wheels and stars*,
Graphs Combin. (2015), 2437–2446.

[ZCC17] Zhang, X., Chen, Y., and Cheng, T. C. E.,
*Some values of Ramsey numbers for C₄ versus stars*,
Finite Fields Appl. (2017), 73–85.

[ZCC17b] Zhang, X., Chen, Y., and Cheng, T. C. E.,
*Polarity graphs and Ramsey numbers for C₄ versus stars*,
Discrete Math. (2017), 655–660.
-/

open SimpleGraph

namespace Erdos552

/-- The off-diagonal Ramsey number $R(G_1, G_2)$: the minimum $N$ such that every
graph $H$ on $N$ vertices contains a copy of $G_1$ or its complement contains a
copy of $G_2$. -/
noncomputable def offDiagRamseyNumber {V₁ V₂ : Type*}
    (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) : ℕ :=
  sInf {N : ℕ | ∀ (H : SimpleGraph (Fin N)),
    G₁.IsContained H ∨ G₂.IsContained Hᶜ}

/-- The star graph $S_n = K_{1,n}$ on $n + 1$ vertices: vertex $0$ is the center,
adjacent to all other vertices. -/
def starGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj i j := (i.val = 0 ∧ j.val ≠ 0) ∨ (j.val = 0 ∧ i.val ≠ 0)
  symm _ _ h := h.elim Or.inr Or.inl
  loopless v h := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact h2 h1

/--
Erdős Problem 552 [BEFRS89]:

Is it true that, for any $c > 0$, there are infinitely many $n$ such that
$R(C_4, S_n) \leq n + \sqrt{n} - c$?

Here $C_4$ is the cycle on $4$ vertices and $S_n = K_{1,n}$ is the star on $n + 1$
vertices. "Infinitely many" is formalised as: for every $N$ there exists $n \geq N$
satisfying the bound.

The known bounds are:
$$n + \sqrt{n} - 6n^{11/40} \leq R(C_4, S_n) \leq n + \lceil\sqrt{n}\rceil + 1.$$
The lower bound is due to [BEFRS89] and the upper bound is due to Parsons [Pa75].
Erdős offered \$100 for a proof or disproof.
-/
@[category research open, AMS 5]
theorem erdos_552 : answer(sorry) ↔
    ∀ c : ℝ, c > 0 →
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
      (offDiagRamseyNumber (cycleGraph 4) (starGraph n) : ℝ) ≤
        ↑n + Real.sqrt ↑n - c := by
  sorry

end Erdos552
