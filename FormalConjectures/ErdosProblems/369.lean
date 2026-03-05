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
# Erdős Problem 369

*Reference:* [erdosproblems.com/369](https://www.erdosproblems.com/369)

The problem as literally stated is trivially true (take $\{1, \ldots, k\}$ with
$n > k^{1/\varepsilon}$). There are two non-trivial variants. The one formalized here
requires the $k$ consecutive integers to lie in $[n/2, n]$. A positive answer follows from
Balog–Wooley [BaWo98] for infinitely many $n$, but the case of all sufficiently large $n$
remains open.

See also [370] and [928].

[BaWo98] Balog, A. and Wooley, T., _On strings of consecutive integers with no large prime
factors_. J. Austral. Math. Soc. Ser. A (1998).

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

namespace Erdos369

/-- A natural number $m$ is $y$-smooth if every prime factor of $m$ is at most $y$. -/
def IsSmooth (y : ℝ) (m : ℕ) : Prop :=
  ∀ p ∈ m.primeFactorsList, (p : ℝ) ≤ y

/--
Erdős Problem 369 [ErGr80, p.69]:

For all $\varepsilon > 0$ and $k \geq 2$, for all sufficiently large $n$, there exist $k$
consecutive integers in $[n/2, n]$ that are all $n^{\varepsilon}$-smooth.
-/
@[category research open, AMS 11]
theorem erdos_369 : answer(sorry) ↔
    ∀ (ε : ℝ) (_ : 0 < ε) (k : ℕ) (_ : 2 ≤ k),
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ a : ℕ, n / 2 ≤ a ∧ a + k ≤ n + 1 ∧
        ∀ j : ℕ, j < k → IsSmooth ((n : ℝ) ^ ε) (a + j) := by
  sorry

end Erdos369
