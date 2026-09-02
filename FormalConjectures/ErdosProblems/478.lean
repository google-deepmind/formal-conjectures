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
# Erdős Problem 478

*References:*
- [erdosproblems.com/478](https://www.erdosproblems.com/478)
- [ErGr80] Erdős, P. and Graham, R. L.,
  *Old and new problems and results in combinatorial number theory*.
  Monographies de L'Enseignement Mathématique (1980).
-/

namespace Erdos478

open Filter

/-- Let $p$ be prime and $A_p=\{k!\pmod p:1\leq k<p\}$. Is it true that
$\lvert A_p\rvert\sim(1-1/e)p$? -/
@[category research open, AMS 11]
theorem erdos_478 : answer(sorry) ↔ ∀ ε > 0, ∀ᶠ p : ℕ in atTop, p.Prime →
    abs (((((Finset.Icc 1 (p - 1)).image fun k ↦ k.factorial % p).card : ℝ) / (p : ℝ)) -
      (1 - (Real.exp 1)⁻¹)) < ε := by
  sorry

/- TODO: Formalize the source's known $\sqrt p$ lower bounds, Wilson-theorem upper bound, average
results, and the infinitude/congruence/computational questions concerning socialist primes. -/

end Erdos478
