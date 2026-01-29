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
# Erdős Problem 568

Let $G$ be a graph such that $R(G,T_n) \ll n$ for any tree $T_n$ on $n$ vertices and $R(G,K_n) \ll n^2$.
Is it true that, for any $H$ with $m$ edges and no isolated vertices,
$$ \hat{r}(G,H) \ll m? $$

In other words, is $G$ Ramsey size linear?

*Reference:* [erdosproblems.com/568](https://www.erdosproblems.com/568)

[EFRS93] Erdős, Faudree, Rousseau and Schelp, _Ramsey size linear graphs_.
Combin. Probab. Comput. (1993), 389-399.
-/

open SimpleGraph

/--
**Erdős Problem 568** [EFRS93]

Let $G$ be a graph such that $R(G, T_n) \le O(n)$ for any tree $T_n$ on $n$ vertices,
and $R(G, K_n) \le O(n^2)$.
Is it true that $G$ is Ramsey size linear ($\hat{r}(G, H) \le O(m)$)?
-/
@[category research open, AMS 05]
theorem erdos_568 : answer(sorry) ↔
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      -- Condition 1: R(G, Tn) << n for any tree Tn on n vertices
      (∃ c1 > (0 : ℝ), ∀ (n : ℕ) (T : SimpleGraph (Fin n)), T.IsTree →
        (Ramsey G T : ℝ) ≤ c1 * n) →
      -- Condition 2: R(G, Kn) << n^2
      (∃ c2 > (0 : ℝ), ∀ (n : ℕ),
        (Ramsey G (completeGraph (Fin n)) : ℝ) ≤ c2 * (n : ℝ)^2) →
      -- Conclusion: G is Ramsey size linear
      IsRamseySizeLinear G := by
  sorry
