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
# Erdős Problem 973

*Reference:* [erdosproblems.com/973](https://www.erdosproblems.com/973)

Does there exist a constant $C > 1$ such that for every $n \geq 2$ there is a sequence of complex
numbers $z_1, \ldots, z_n$ with $z_1 = 1$ and $|z_i| \geq 1$, whose power sums satisfy
$\max_{2 \leq k \leq n+1} |\sum z_i^k| < C^{-n}$?

[Er65b] Erdős, P., _Extremal problems in number theory_. Lectures on Modern Mathematics,
Vol. III (1965), 196–244.

[Er92f] Erdős, P., _On some problems of Paul Turán concerning power sums of complex numbers_.
Acta Mathematica Hungarica (1992), 11–24.

[Ha74] Hayman, W. K., _Research problems in function theory: new problems_ (1974), 155–180.

[Tu84b] Turán, P., _On a new method of analysis and its applications_ (1984), xvi+584.

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference
"Paul Erdős and his mathematics", Budapest, July 1999 (1999).
-/

namespace Erdos973

/--
Does there exist a constant $C > 1$ such that, for every $n \geq 2$, there
exists a sequence $z_1, \ldots, z_n \in \mathbb{C}$ with $z_1 = 1$ and
$|z_i| \geq 1$ for all $i$, such that
$$\max_{2 \leq k \leq n+1} \left| \sum_{i=1}^{n} z_i^k \right| < C^{-n}?$$

A problem of Erdős [Er65b, p.213]. This is Problem 7.3 in [Ha74]. See also [Tu84b], [Er92f],
[Va99], and [519].
-/
@[category research open, AMS 30]
theorem erdos_973 : answer(sorry) ↔
    ∃ C : ℝ, C > 1 ∧
    ∀ (n : ℕ) (_ : n ≥ 2),
    ∃ z : Fin n → ℂ,
      z ⟨0, by omega⟩ = 1 ∧
      (∀ i, 1 ≤ ‖z i‖) ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ n + 1 →
        ‖∑ i : Fin n, z i ^ k‖ < C⁻¹ ^ n := by
  sorry

end Erdos973
