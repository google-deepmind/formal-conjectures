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
# Erdős Problem 504

*Reference:* [erdosproblems.com/504](https://www.erdosproblems.com/504)

Blumenthal's minimax angle problem: let $\alpha_N$ be the supremum of all
$0 \le \alpha \le \pi$ such that every set of $N$ points in the plane contains
three distinct points determining an angle at least $\alpha$. Determine
$\alpha_N$.

Szekeres [Sz41] proved $\alpha_{2^n} \le \pi(1 - 1/n)$ together with a lower
bound for $2^n + 1$ points. Erdős and Szekeres [ErSz60] proved
$\alpha_{2^n} = \alpha_{2^n - 1} = \pi(1 - 1/n)$, and Sendov [Se95] determined
$\alpha_N$ for every $N$.

[Sz41] Szekeres, G., _On an extremum problem in the plane_. Amer. J. Math. 63
(1941), 208-210.

[ErSz60] Erdős, P. and Szekeres, G., _On some extremum problems in elementary
geometry_. Ann. Univ. Sci. Budapest. Eötvös Sect. Math. 3-4 (1960-61), 53-62.

[Se95] Sendov, Bl., _Minimax of the angles in a plane configuration of points_.
Acta Math. Hungar. 69 (1995), 27-46.
-/

open Real EuclideanGeometry

namespace Erdos504

/--
The minimax angle $\alpha_N$: the supremum of all $\alpha \in [0, \pi]$ such
that every set of $N$ points of the plane contains three pairwise distinct
points $x, z, y$ with $\angle x z y \ge \alpha$ (angle taken at the middle
point $z$).
-/
noncomputable def minimaxAngle (N : ℕ) : ℝ :=
  sSup {α : ℝ | α ∈ Set.Icc 0 π ∧
    ∀ S : Finset ℂ, S.card = N →
      ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
        α ≤ EuclideanGeometry.angle x z y}

/--
**Erdős–Szekeres (1960).** For $n \ge 3$,
$\alpha_{2^n} = \pi\left(1 - \frac{1}{n}\right)$.
-/
@[category research solved, AMS 52]
theorem erdos_504 {n : ℕ} (hn : 3 ≤ n) :
    minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π := by
  sorry

/--
**Erdős–Szekeres (1960).** For $n \ge 3$, also
$\alpha_{2^n - 1} = \pi\left(1 - \frac{1}{n}\right)$.
-/
@[category research solved, AMS 52]
theorem erdos_504.variants.endpoint {n : ℕ} (hn : 3 ≤ n) :
    minimaxAngle (2 ^ n - 1) = (1 - 1 / (n : ℝ)) * π := by
  sorry

/--
The lower-bound half of `erdos_504` in existential form (Theorem 1 of
[ErSz60]): any $2^n$ points of the plane contain three points determining an
angle strictly greater than $\pi(1 - 1/n)$.
-/
@[category research solved, AMS 52,
  formal_proof using lean4 at "https://github.com/ToshiDad/erdos-504/blob/fd344a9/Erdos504.lean#L6501"]
theorem erdos_504.variants.erdos_szekeres_1960 {n : ℕ} (hn : 3 ≤ n)
    (S : Finset ℂ) (hcard : S.card = 2 ^ n) :
    ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p ≠ q ∧ r ≠ q ∧
      (1 - 1 / (n : ℝ)) * π < EuclideanGeometry.angle p q r := by
  sorry

/--
**Szekeres (1941), lower bound.** More than $2^n$ points of the plane contain
three points determining an angle strictly greater than $\pi(1 - 1/n)$.
-/
@[category research solved, AMS 52,
  formal_proof using lean4 at "https://github.com/ToshiDad/erdos-504/blob/fd344a9/Erdos504.lean#L341"]
theorem erdos_504.variants.szekeres_lower {n : ℕ} (hn : 0 < n) (S : Finset ℂ)
    (hcard : 2 ^ n < S.card) :
    ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p ≠ q ∧ r ≠ q ∧
      (1 - 1 / (n : ℝ)) * π < EuclideanGeometry.angle p q r := by
  sorry

/--
**Szekeres (1941), upper-bound construction.** For every $\varepsilon > 0$
there is a set of exactly $2^t$ points of the plane all of whose angles are
less than $\pi(1 - 1/t) + \varepsilon$. Together with
`erdos_504.variants.erdos_szekeres_1960` this pins down
$\alpha_{2^t} = \pi(1 - 1/t)$: the supremum is approached but not attained by
any finite configuration.
-/
@[category research solved, AMS 52,
  formal_proof using lean4 at "https://github.com/ToshiDad/erdos-504/blob/fd344a9/Erdos504.lean#L801"]
theorem erdos_504.variants.szekeres_upper {t : ℕ} (ht : 0 < t) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ S : Finset ℂ, S.card = 2 ^ t ∧
      ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
        EuclideanGeometry.angle p q r < (1 - 1 / (t : ℝ)) * π + ε := by
  sorry

/--
**Sendov (1995).** The complete determination: for $n \ge 3$,
$\alpha_N = \pi(1 - 1/n)$ whenever $2^{n-1} + 2^{n-3} < N \le 2^n$, and
$\alpha_N = \pi\left(1 - \frac{1}{2n - 1}\right)$ whenever
$2^{n-1} < N \le 2^{n-1} + 2^{n-3}$.
-/
@[category research solved, AMS 52]
theorem erdos_504.variants.sendov {n N : ℕ} (hn : 3 ≤ n)
    (h1 : 2 ^ (n - 1) < N) (h2 : N ≤ 2 ^ n) :
    minimaxAngle N =
      if 2 ^ (n - 1) + 2 ^ (n - 3) < N then (1 - 1 / (n : ℝ)) * π
      else (1 - 1 / (2 * (n : ℝ) - 1)) * π := by
  sorry

end Erdos504
