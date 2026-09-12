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
# Erdős Problem 1027

*References:*
- [erdosproblems.com/1027](https://www.erdosproblems.com/1027)
-/

namespace Erdos1027

open Filter Asymptotics

/--
Let $c>0$, and let $n$ be sufficiently large depending on $c$. Suppose that $\mathcal{F}$ is a
family of at most $c2^n$ many finite sets of size $n$. Let $X=\cup_{A\in \mathcal{F}}A$. Must there
exist $\gg_c 2^{\lvert X\rvert}$ many sets $B\subset X$ which intersect every set in $\mathcal{F}$,
yet contain none of them?

This is true, and a proof was given in the comment section by Koishi Chan.
-/
@[category research solved, AMS 5]
theorem erdos_1027 :
    answer(True) ↔ ∀ c : ℝ, 0 < c → ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ n : ℕ in atTop, ∀ (m : ℕ) (H : Finset (Finset (Fin m))),
      H.IsUniform n → (H.card : ℝ) ≤ c * 2 ^ n →
        δ * 2 ^ (H.biUnion id).card ≤ (H.propertyBWitnesses.card : ℝ) := by
  sorry

end Erdos1027
