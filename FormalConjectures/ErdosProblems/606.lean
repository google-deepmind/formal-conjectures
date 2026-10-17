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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 606

*References:*
- [erdosproblems.com/606](https://www.erdosproblems.com/606)
- [ErSa88] Salamon, Peter and Erdős, Paul,
  [The solution to a problem of Grünbaum](https://doi.org/10.4153/CMB-1988-020-2).
  Canad. Math. Bull. (1988), 129-138.
-/

@[expose] public section

open EuclideanGeometry

namespace Erdos606

open scoped Classical in
/-- The possible numbers of distinct lines determined by $n$ points in $\mathbb{R}^2$. -/
noncomputable def possibleLineCounts (n : ℕ) : Set ℕ :=
  {m | ∃ P : Finset ℝ², P.card = n ∧
    (P.offDiag.image fun p ↦ line[ℝ, p.1, p.2]).card = m}

/-- The $k$-th band in [ErSa88]: the interval from $k(n-k)-\binom{k}{2}+1$ to
$k(n-k)+\binom{k}{2}+1$, excluding one and three below the upper endpoint. -/
def lineCountBand (n k : ℕ) : Set ℕ :=
  let upper := k * (n - k) + k.choose 2 + 1
  Set.Icc (k * (n - k) - k.choose 2 + 1) upper \ {upper - 1, upper - 3}

/-- The eventual classification in [ErSa88, pp. 132-134]. With
$K=\lfloor\sqrt{n+2}\rfloor$, take all bands with $k<K$ and the interval from
$K(n-K)-\binom{K}{2}+1$ to $\binom{n}{2}$, excluding the two terminal gaps. -/
def classifiedLineCounts (n : ℕ) : Set ℕ :=
  let k := Nat.sqrt (n + 2)
  (⋃ j < k, lineCountBand n j) ∪
    (Set.Icc (k * (n - k) - k.choose 2 + 1) (n.choose 2) \
      {n.choose 2 - 1, n.choose 2 - 3})

/--
Given any $n$ distinct points in $\mathbb{R}^2$ let $f(n)$ count the number of distinct
lines determined by these points. For all sufficiently large $n$, what are the possible
values of $f(n)$?

A question of Grünbaum. Solved (for all sufficiently large $n$) completely by Erdős
and Salamon [ErSa88].
-/
@[category research solved, AMS 5 52]
theorem erdos_606 : possibleLineCounts =ᶠ[Filter.atTop] answer(classifiedLineCounts) := by
  sorry

/--
The Sylvester-Gallai theorem implies that if $f(n)>1$ then $f(n)\geq n$.
-/
@[category research solved, AMS 5 52]
theorem erdos_606.variants.lower_bound :
    ∀ n m : ℕ, m ∈ possibleLineCounts n → 1 < m → n ≤ m := by
  sorry

/--
Erdős showed that, for some constant $c>0$, all integers in
$[cn^{3/2},\binom{n}{2}]$ are possible except $\binom{n}{2}-1$ and $\binom{n}{2}-3$.
We take $n\geq 2$, so at least one line is determined.
-/
@[category research solved, AMS 5 52]
theorem erdos_606.variants.interval :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → ∀ m : ℕ,
      c * (n : ℝ) ^ (3 / 2 : ℝ) ≤ m → m ≤ n.choose 2 →
      (m ∈ possibleLineCounts n ↔ m ≠ n.choose 2 - 1 ∧ m ≠ n.choose 2 - 3) := by
  sorry

/-- The empty point set determines no lines. -/
@[category test, AMS 5 52]
theorem possibleLineCounts_zero : possibleLineCounts 0 = {0} := by
  ext m
  simp [possibleLineCounts]

/-- A single point determines no lines. -/
@[category test, AMS 5 52]
theorem possibleLineCounts_one : possibleLineCounts 1 = {0} := by
  ext m
  simp [possibleLineCounts, Finset.card_eq_one]

/-- The zeroth band consists of the single line count $1$. -/
@[category test, AMS 5 52]
theorem lineCountBand_zero (n : ℕ) : lineCountBand n 0 = {1} := by
  ext m
  simp [lineCountBand]

end Erdos606
