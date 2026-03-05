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
# Erdős Problem 452

*Reference:* [erdosproblems.com/452](https://www.erdosproblems.com/452)

Let $\omega(n)$ count the number of distinct prime factors of $n$. What is the size
of the largest interval $I \subseteq [x, 2x]$ such that $\omega(n) > \log \log n$ for all
$n \in I$?

Erdős [Er37] proved that the density of integers $n$ with $\omega(n) > \log \log n$ is $1/2$.
The Chinese remainder theorem implies there is such an interval with
$|I| \geq (1+o(1)) \log x / (\log \log x)^2$.
It could be true that there is such an interval of length $(\log x)^k$ for
arbitrarily large $k$.

[Er37] Erdős, P., *On the normal number of prime factors of p-1 and some related problems
concerning Euler's φ-function*. Quart. J. Math. Oxford Ser. **8** (1937), 313-320.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).
-/

namespace Erdos452

/-- The number of distinct prime factors of $n$ ($\omega(n)$ in analytic number theory). -/
noncomputable def omega (n : ℕ) : ℕ :=
  (Nat.primeFactorsList n).toFinset.card

/--
Erdős Problem 452 [ErGr80, p.90]:

For every $k > 0$, for all sufficiently large $x$, there exists an interval
$[a, a + L] \subseteq [x, 2x]$ with $L \geq (\log x)^k$ such that $\omega(n) > \log \log n$
for all integers $n$ in $[a, a + L]$.
-/
@[category research open, AMS 11]
theorem erdos_452 :
    ∀ k : ℝ, 0 < k →
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      ∃ a L : ℕ, x ≤ a ∧ a + L ≤ 2 * x ∧
        (Real.log (x : ℝ)) ^ k ≤ (L : ℝ) ∧
        ∀ n ∈ Finset.Icc a (a + L),
          (omega n : ℝ) > Real.log (Real.log (n : ℝ)) := by
  sorry

end Erdos452
