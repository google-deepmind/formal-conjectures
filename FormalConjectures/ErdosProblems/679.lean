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
# Erdős Problem 679

Erdős asked whether, for every ε > 0, there are infinitely many n such that
ω(n − k) < (1 + ε) log k / log log k for all sufficiently large k < n. A stronger
form with O(1) error was disproved.

*Reference:* [erdosproblems.com/679](https://www.erdosproblems.com/679)

[Er79d] Erdős, P., _Some unconventional problems in number theory_. Math. Mag. 52 (1979), 67-70.
-/

namespace Erdos679

/-- The number of distinct prime factors of $n$ ($\omega(n)$ in analytic number theory). -/
noncomputable def omega (n : ℕ) : ℕ :=
  (Nat.primeFactorsList n).toFinset.card

/--
Erdős Problem 679, Part 1 [Er79d]:

For every $\varepsilon > 0$, are there infinitely many $n$ such that for all sufficiently
large $k$ (with $1 \leq k < n$), we have
$\omega(n - k) < (1 + \varepsilon) \cdot \log k / \log \log k$?

Here "sufficiently large" means there exists a threshold $k_0$ depending on $\varepsilon$
(but not on $n$) such that the bound holds for all $k \geq k_0$ with $k < n$.
-/
@[category research open, AMS 11]
theorem erdos_679 :
    answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ k₀ : ℕ,
    Set.Infinite {n : ℕ |
      ∀ k : ℕ, k₀ ≤ k → k < n →
        (omega (n - k) : ℝ) <
          (1 + ε) * Real.log (k : ℝ) / Real.log (Real.log (k : ℝ))} := by
  sorry

/--
Erdős Problem 679, Part 2 (disproved by DottedCalculator) [Er79d]:

The stronger version asking whether $\omega(n - k) < \log k / \log \log k + O(1)$
holds for infinitely many $n$ is false. In fact, there exists a constant $c > 0$
such that for all sufficiently large $n$, there exists $k < n$ with
$$\omega(n - k) \geq \log k / \log \log k + c \cdot \log k / (\log \log k)^2.$$
-/
@[category research solved, AMS 11]
theorem erdos_679.variants.disproof :
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ k : ℕ, k < n ∧
        (omega (n - k) : ℝ) ≥
          Real.log (k : ℝ) / Real.log (Real.log (k : ℝ)) +
          c * Real.log (k : ℝ) / (Real.log (Real.log (k : ℝ))) ^ 2 := by
  sorry

end Erdos679
