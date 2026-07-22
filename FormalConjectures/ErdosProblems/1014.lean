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

import FormalConjectures.Wikipedia.RamseyNumbers
import FormalConjecturesUtil

/-!
# Erdős Problem 1014

*References:*
- [erdosproblems.com/1014](https://www.erdosproblems.com/1014)
- [Er71] Erdős, P., Some unsolved problems in graph theory and combinatorial analysis. Combinatorial
  Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [OpenAI26] *On the ratio of $R(k,\ell)$ and $R(k,\ell+1)$*, proof due to an internal model at
  OpenAI (2026).
  https://cdn.openai.com/pdf/6dc7175d-d9e7-4b8d-96b8-48fe5798cd5b/Ramsey.pdf
-/

open Filter

open scoped Topology

namespace Erdos1014

open RamseyNumbers

/--
Let $R(k,l)$ be the Ramsey number, so the minimal $n$ such that every graph on at least $n$
vertices contains either a $K_k$ or an independent set on $l$ vertices.

Prove, for fixed $k\geq 3$, that
\[\lim_{l\to \infty}\frac{R(k,l+1)}{R(k,l)}=1.\]

This has been
[solved](https://cdn.openai.com/pdf/6dc7175d-d9e7-4b8d-96b8-48fe5798cd5b/Ramsey.pdf)
by an internal model at OpenAI.
-/
@[category research solved, AMS 5]
theorem erdos_1014 : ∀ k : ℕ, 3 ≤ k →
    Tendsto (fun l : ℕ ↦ (R(k, l + 1) : ℝ) / (R(k, l) : ℝ)) atTop (𝓝 1) := by
  sorry

/--
That proof in fact shows that
\[R(k,l+1)\leq (1+O(l^{-c/k^2}))R(k,l)\]
for some constant $c>0$.
-/
@[category research solved, AMS 5]
theorem erdos_1014.variants.upper_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, ∀ᶠ l : ℕ in atTop,
      (R(k, l + 1) : ℝ) ≤ (1 + C * (l : ℝ) ^ (-c / (k : ℝ) ^ 2)) * (R(k, l) : ℝ) := by
  sorry

end Erdos1014
