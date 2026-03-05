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
# Erdős Problem 1119

*Reference:* [erdosproblems.com/1119](https://www.erdosproblems.com/1119)

Let $\mathfrak{m}$ be an infinite cardinal with
$\aleph_0 < \mathfrak{m} < \mathfrak{c}$. If a family of entire functions takes at most
$\mathfrak{m}$ distinct values at every point of $\mathbb{C}$, must the family contain at most
$\mathfrak{m}$ distinct functions? This generalizes Wetzel's problem and is independent of ZFC.

[Ha74] Hajnal, A., *Proof of a conjecture of S. Ruziewicz*, Fund. Math. 50 (1961/62), 123–128.

[KuSh17] Kumar, A. and Shelah, S., *On a question about families of entire functions*,
Fund. Math. 239 (2017), 279–288.

[ScWe24] Schilhan, J. and Weinert, T., *On Wetzel's problem and its relatives*, preprint (2024).
-/

open Cardinal Classical Set

namespace Erdos1119

/--
Erdős Problem 1119 (Independent of ZFC) [Ha74]:

Let $\mathfrak{m}$ be an infinite cardinal with
$\aleph_0 < \mathfrak{m} < \mathfrak{c} = 2^{\aleph_0}$. Let $\{f_\alpha\}$ be a family of
entire functions such that, for every $z_0 \in \mathbb{C}$, the set $\{f_\alpha(z_0)\}$ of
values has at most $\mathfrak{m}$ distinct elements. Must the family of distinct functions
have cardinality at most $\mathfrak{m}$?

This generalizes Wetzel's problem. Erdős proved that for the countable case
($\aleph_0$ values), the answer is yes if $\mathfrak{c} > \aleph_1$ and no if
$\mathfrak{c} = \aleph_1$.
Kumar–Shelah [KuSh17] showed the answer can be yes (with $\mathfrak{m} = \aleph_1$,
$\mathfrak{c} = \aleph_2$), while Schilhan–Weinert [ScWe24] showed it can be no.
-/
@[category research solved, AMS 3 30]
theorem erdos_1119 : answer(sorry) ↔
    ∀ (𝔪 : Cardinal), ℵ₀ < 𝔪 → 𝔪 < Cardinal.continuum →
    ∀ (ι : Type) (f : ι → ℂ → ℂ),
    (∀ i, Differentiable ℂ (f i)) →
    (∀ z : ℂ, Cardinal.mk ↥(range (fun i => f i z)) ≤ 𝔪) →
    Cardinal.mk ↥(range f) ≤ 𝔪 := by
  sorry

end Erdos1119
