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
# Erdős Problem 933

Erdős asked whether the limsup of the ratio of the {2,3}-smooth part of n(n+1)
to n·log(n) is infinite.

Stefan Steinerberger noted a simple proof that 2^k · 3^l > n · log n holds for
infinitely many n, by taking n = 2^{3^r}.

*Reference:* [erdosproblems.com/933](https://www.erdosproblems.com/933)

[Er76d] Erdős, P., _Problems and results on number theoretic properties of consecutive
integers and related questions_. Proceedings of the Fifth Manitoba Conference on Numerical
Mathematics (Univ. Manitoba, Winnipeg, Man., 1975) (1976), 25-44.
-/

open Real

namespace Erdos933

/--
The $\{2,3\}$-smooth part of a natural number $n$, i.e., $2^{v_2(n)} \cdot 3^{v_3(n)}$,
where $v_p$ denotes the $p$-adic valuation.
-/
noncomputable def smoothPart23 (n : ℕ) : ℕ :=
  2 ^ padicValNat 2 n * 3 ^ padicValNat 3 n

/--
Erdős Problem 933 [Er76d]:

If $n(n+1) = 2^k \cdot 3^l \cdot m$ where $\gcd(m, 6) = 1$, is it true that
$$\limsup_{n \to \infty} \frac{2^k \cdot 3^l}{n \log n} = \infty?$$

Equivalently: for every $C > 0$, there exist arbitrarily large $n$ such that
the $\{2,3\}$-smooth part of $n(n+1)$ exceeds $C \cdot n \cdot \log n$.

Mahler proved that $2^k \cdot 3^l < n^{1+o(1)}$.
Erdős wrote that 'it is easy to see' that for infinitely many $n$,
$2^k \cdot 3^l > n \cdot \log n$.
-/
@[category research open, AMS 11]
theorem erdos_933 : answer(sorry) ↔
    ∀ C : ℝ, C > 0 →
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (smoothPart23 (n * (n + 1)) : ℝ) > C * (n : ℝ) * Real.log (n : ℝ) := by
  sorry

end Erdos933
