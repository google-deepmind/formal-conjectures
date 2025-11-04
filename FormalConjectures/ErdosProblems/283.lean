/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 283

*References:*
- [erdosproblems.com/283](https://www.erdosproblems.com/283)
- [Gr63] Graham, R. L., A theorem on partitions. J. Austral. Math. Soc. (1963), 435-441.
-/

open Filter Polynomial Finset

namespace Erdos283

/--
Given a polynomial `p`, the predicate that if the leading coefficient is positive and
there exists no $d≥2$ with $d ∣ p(n)$ for all $n≥1$, then for all sufficiently large $m$,
there exist integers $1≤n_1<\dots < n_k$ such that $$1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$$
and $$m=p(n_1)+\cdots+p(n_k)$$?
-/
def Condition (p : ℤ[X]) : Prop :=
  p.leadingCoeff > 0 → ¬ (∃ d ≥ 2, ∀ n ≥ 1, d ∣ p.eval n) →
  ∀ᶠ m in atTop, ∃ k ≥ 1, ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
  1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
  m = ∑ i ∈ Finset.Icc 1 (Fin.last k),  p.eval (n i)

/--
Let $p\colon \mathbb{Z} \rightarrow \mathbb{Z}$ be a polynomial whose leading coefficient is
positive and such that there exists no $d≥2$ with $d ∣ p(n)$ for all $n≥1$. Is it true that,
for all sufficiently large $m$, there exist integers $1≤n_1<\dots < n_k$ such that
$$1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$$
and
$$m=p(n_1)+\cdots+p(n_k)$$?
-/
@[category research open, AMS 11]
theorem erdos_283 : (∀ p : ℤ[X], erdos_283_condition p) ↔ answer(sorry) := by
  sorry


/--
Graham [Gr63] has proved this when $p(x)=x$.
-/
@[category research solved, AMS 11]
theorem erdos_283.variants.graham : erdos_283_condition X := by
  sorry


-- TODO(firsching): formalize the rest of the additional material

end Erdos283
