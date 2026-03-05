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
# Erdős Problem 519

*Reference:* [erdosproblems.com/519](https://www.erdosproblems.com/519)

A problem of Turán, who proved that the maximum is $\gg 1/n$. This was solved
by Atkinson [At61b], who showed that $c = 1/6$ suffices. This has been improved
by Biró, first to $c = 1/2$ [Bi94], and later to an absolute constant $c > 1/2$
[Bi00].

[At61b] Atkinson, F.V., _On sums of powers of complex numbers_. Acta Math. Acad.
Sci. Hungar. 12 (1961), 185-188.

[Bi94] Biró, A., _On a problem of Turán concerning sums of powers of complex
numbers_. Acta Math. Hungar. 65 (1994), 209-216.

[Bi00] Biró, A., _An upper estimate in Turán's pure power sum problem_. Indag.
Math. (N.S.) 11 (2000), 499-508.
-/

namespace Erdos519

/--
Erdős Problem 519 (Turán's power sum problem) [At61b]:

There exists an absolute constant $c > 0$ such that for any $n \geq 1$ and any complex
numbers $z_1, \ldots, z_n$ with $z_1 = 1$,
$$\max_{1 \leq k \leq n} \left| \sum_i z_i^k \right| > c.$$
-/
@[category research solved, AMS 30]
theorem erdos_519 : answer(True) ↔
    ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (hn : 0 < n) (z : Fin n → ℂ),
      z ⟨0, hn⟩ = 1 →
      ∃ k : Fin n, c < ‖∑ i : Fin n, z i ^ (k.val + 1)‖ := by
  sorry

end Erdos519
