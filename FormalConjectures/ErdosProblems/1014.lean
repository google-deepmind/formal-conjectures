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
# Erdős Problem 1014

Erdős conjectured that for fixed $k \geq 3$, the ratio of consecutive Ramsey numbers
$R(k, l+1) / R(k, l)$ tends to $1$ as $l \to \infty$.

*Reference:* [erdosproblems.com/1014](https://www.erdosproblems.com/1014)

[Er71] Erdős, P., _Topics in combinatorial analysis_, pp. 95-99, 1971.
-/

open SimpleGraph

namespace Erdos1014

/-- The Ramsey number $R(k, l)$: the minimum $N$ such that every simple graph on $N$
vertices contains either a $k$-clique or an independent set of size $l$
(equivalently, an $l$-clique in the complement). -/
noncomputable def ramseyR (k l : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree k ∨ ¬Gᶜ.CliqueFree l}

/--
Erdős Problem 1014 [Er71, p.99]:

For fixed $k \geq 3$,
$$\lim_{l \to \infty} R(k, l+1) / R(k, l) = 1,$$
where $R(k, l)$ is the Ramsey number.

Formulated as: for every $\varepsilon > 0$, there exists $L_0$ such that for all $l \geq L_0$,
$|R(k, l+1) / R(k, l) - 1| \leq \varepsilon$.
-/
@[category research open, AMS 5]
theorem erdos_1014 (k : ℕ) (hk : k ≥ 3) :
    ∀ ε : ℝ, ε > 0 →
    ∃ L₀ : ℕ, ∀ l : ℕ, l ≥ L₀ →
      |(ramseyR k (l + 1) : ℝ) / (ramseyR k l : ℝ) - 1| ≤ ε := by
  sorry

end Erdos1014
