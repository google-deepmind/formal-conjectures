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
# Erdős Problem 466

*Reference:* [erdosproblems.com/466](https://www.erdosproblems.com/466)

Let $N(X, \delta)$ denote the maximum number of points $P_1, \ldots, P_n$ which can be chosen
in a disk of radius $X$ in $\mathbb{R}^2$ such that $\| |P_i - P_j| \| \geq \delta$ for all
$1 \leq i < j \leq n$, where $\|x\|$ denotes the distance from $x$ to the nearest integer.

This was proved by Graham, who showed $N(X, 1/10) > (\log X)/10$.
Sárközy substantially improved this, proving that for all sufficiently small $\delta > 0$,
$N(X, \delta) > X^{1/2 - \delta^{1/7}}$.

See also Problem 465, which gives complementary upper bounds on $N(X, \delta)$.

[Er72] Erdős, P., _Quelques problèmes de théorie des nombres_, p. 81, 1972.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[Er82e] Erdős, P., _Problems and results on finite and infinite graphs_. Recent advances
in graph theory (Proc. Second Czechoslovak Sympos., Prague, 1982).

[Sa76] Sárközy, A., _On difference sets of sequences of integers. I._ Acta Math. Acad. Sci.
Hungar. 31 (1978), no. 1-2, 125-149.
-/

namespace Erdos466

/-- The distance of a real number from the nearest integer. -/
noncomputable def distNearestInt (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/--
Erdős Problem 466 (Proved by Graham):

There exists $\delta > 0$ such that $N(X, \delta) \to \infty$ as $X \to \infty$. Formalized as:
there exists $\delta > 0$ such that for every $M$, for sufficiently large $X$,
one can find at least $M$ points in a disk of radius $X$ in $\mathbb{R}^2$ whose
pairwise distances all satisfy $\|d\| \geq \delta$.
-/
@[category research solved, AMS 11 52]
theorem erdos_466 :
    ∃ δ : ℝ, 0 < δ ∧
    ∀ M : ℕ, ∃ X₀ : ℝ, 0 < X₀ ∧
    ∀ (X : ℝ), X₀ ≤ X →
    ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      M ≤ A.card ∧
      (∀ p ∈ A, dist p 0 ≤ X) ∧
      (∀ p ∈ A, ∀ q ∈ A, p ≠ q → distNearestInt (dist p q) ≥ δ) := by
  sorry

/--
Graham's quantitative bound for Erdős Problem 466 [ErGr80]:

$N(X, 1/10) > (\log X) / 10$ for sufficiently large $X$.
This gives the first explicit lower bound with $\delta = 1/10$.
-/
@[category research solved, AMS 11 52]
theorem erdos_466_graham :
    ∀ X : ℝ, 1 < X →
    ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      (Real.log X / 10 : ℝ) ≤ ↑A.card ∧
      (∀ p ∈ A, dist p 0 ≤ X) ∧
      (∀ p ∈ A, ∀ q ∈ A, p ≠ q → distNearestInt (dist p q) ≥ 1 / 10) := by
  sorry

/--
Sárközy's improvement for Erdős Problem 466 [Sa76]:

For all sufficiently small $\delta > 0$ and all sufficiently large $X$,
$N(X, \delta) > X^{1/2 - \delta^{1/7}}$.
This is a polynomial lower bound, much stronger than Graham's logarithmic bound.
-/
@[category research solved, AMS 11 52]
theorem erdos_466_sarkozy :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∃ X₀ : ℝ, 0 < X₀ ∧
    ∀ X : ℝ, X₀ ≤ X →
    ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      (X ^ (1 / 2 - δ ^ (1 / 7)) : ℝ) ≤ ↑A.card ∧
      (∀ p ∈ A, dist p 0 ≤ X) ∧
      (∀ p ∈ A, ∀ q ∈ A, p ≠ q → distNearestInt (dist p q) ≥ δ) := by
  sorry

end Erdos466
