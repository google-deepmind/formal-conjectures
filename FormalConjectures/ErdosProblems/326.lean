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

import FormalConjecturesUtil

/-!
# Erdős Problem 326

*References:*
- [erdosproblems.com/326](https://www.erdosproblems.com/326)
- [ErGr80] Erdős, P. and Graham, R. L., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathématique (1980), p. 47.
- [Ca57] Cassels, J. W. S., *Über Basen der natürlichen Zahlenreihe*.
  Abh. Math. Sem. Univ. Hamburg (1957), 247-257.
-/

open Filter

open scoped Topology

namespace Erdos326

/--
Does there exist $A = \{a_1 < a_2 < \cdots\} \subset \mathbb{N}$ which is a minimal basis of
order $2$ (i.e. every large integer is the sum of $2$ elements from $A$, and no proper subset of
$A$ has this property), such that
$$\lim_{k\to\infty} \frac{a_k}{k^2} = c$$
for some $c \neq 0$?

Erdős and Graham conjectured a negative answer to this question [ErGr80].

"Minimal basis of order $2$" is formalised as `Minimal` for the predicate
`Set.IsAsymptoticAddBasisOfOrder · 2` on sets of naturals ordered by inclusion.
-/
@[category research open, AMS 5 11]
theorem erdos_326 : answer(sorry) ↔ ∃ (a : ℕ → ℕ), StrictMono a ∧
    Minimal (fun A : Set ℕ ↦ A.IsAsymptoticAddBasisOfOrder 2) (Set.range a) ∧
      ∃ (c : ℝ), c ≠ 0 ∧ Tendsto (fun n ↦ (a n : ℝ) / n ^ 2) atTop (𝓝 c) := by
  sorry

/--
Erdős originally asked this for any basis (not necessarily minimal); such a basis was constructed
by Cassels [Ca57].
-/
-- Formalisation note: This is trivially true for `x = 0` by taking `a = id`. Cassels' proof
-- shows it for `0 < x` which is more interesting.
@[category research solved, AMS 5 11]
theorem erdos_326.variants.eq :
    ∃ (a : ℕ → ℕ) (_ : StrictMono a) (_ : Set.range a |>.IsAddBasisOfOrder 2) (x : ℝ) (_ : 0 < x),
      Tendsto (fun n ↦ (a n : ℝ) / n ^ 2) atTop (𝓝 x) := by
  sorry

end Erdos326
