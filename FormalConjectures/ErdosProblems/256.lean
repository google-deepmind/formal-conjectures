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
# Erdős Problem 256

*Reference:* [erdosproblems.com/256](https://www.erdosproblems.com/256)

Let $n \geq 1$ and $f(n)$ be maximal such that for any integers
$1 \leq a_1 \leq \cdots \leq a_n$,
$$\max_{|z|=1} \left|\prod_i (1 - z^{a_i})\right| \geq f(n).$$

Equivalently, $f(n)$ is the infimum over all non-decreasing sequences of positive
integers $(a_1, \ldots, a_n)$ of the supremum of $\left|\prod_i (1 - z^{a_i})\right|$ over the
unit circle.

Erdős conjectured that there exists $c > 0$ such that $\log f(n) \gg n^c$ [Er61, Er64b].

This specific conjecture was answered negatively by Belov and Konyagin [BeKo96],
who proved that $\log f(n) \ll (\log n)^4$. The broader problem of precisely
estimating $f(n)$ remains open.

Related to the Chowla cosine problem (Erdős Problem #510).

[Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató
Int. Közl. **6** (1961), 221–254.

[Er64b] Erdős, P., _Problems and results on diophantine approximations_.
Compositio Math. (1964), 52–65.

[ErSz59] Erdős, P., Szekeres, G., _On the product $\prod_{k=1}^{n}(1-z^{a_k})$_.
Académie Serbe des Sciences, Institut de Mathématiques (1959), 29–34.

[At61] Atkinson, F. V., _On a problem of Erdős and Szekeres_. Canadian
Mathematical Bulletin (1961), 7–12.

[Od82] Odlyzko, A. M., _Minima of cosine sums and maxima of polynomials on the
unit circle_. Journal of the London Mathematical Society (Series 2) (1982), 412–420.

[BeKo96] Belov, A. S., Konyagin, S. V., _An estimate for the free term of a
nonnegative trigonometric polynomial with integer coefficients_. Matematicheskie
Zametki (Mathematical Notes) (1996), 627–629.

[BoCh18] Bourgain, J., Chang, M.-C., _On a paper of Erdős and Szekeres_.
Journal d'Analyse Mathématique (2018), 253–271.
-/

open Complex BigOperators Finset

namespace Erdos256

/-- The supremum of $\left|\prod_i (1 - z^{a_i})\right|$ as $z$ ranges over the unit circle,
for a fixed sequence of exponents $a$. -/
noncomputable def unitCircleMaxProd (n : ℕ) (a : Fin n → ℕ) : ℝ :=
  sSup {y : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧
    y = ‖∏ i : Fin n, (1 - z ^ (a i))‖}

/-- $f(n)$ is the infimum over all non-decreasing sequences of positive integers
$(a_1, \ldots, a_n)$ of the supremum of $\left|\prod_i (1 - z^{a_i})\right|$ on the unit
circle. Equivalently, $f(n)$ is the largest real number such that for any positive
integers $1 \leq a_1 \leq \cdots \leq a_n$, the maximum of
$\left|\prod_i (1 - z^{a_i})\right|$ on the unit circle is at least $f(n)$. -/
noncomputable def erdos256_f (n : ℕ) : ℝ :=
  sInf {y : ℝ | ∃ (a : Fin n → ℕ),
    (∀ i, 0 < a i) ∧ Monotone a ∧
    y = unitCircleMaxProd n a}

/--
Erdős Conjecture (Problem 256) [Er61, Er64b]:

Does there exist a constant $c > 0$ such that $\log f(n) \gg n^c$, i.e., do there exist
constants $c > 0$ and $C > 0$ such that for all sufficiently large $n$,
$$\log f(n) \geq C \cdot n^c?$$

This was answered negatively by Belov and Konyagin [BeKo96], who showed
$\log f(n) \ll (\log n)^4$.
-/
@[category research solved, AMS 11 30]
theorem erdos_256 : answer(False) ↔
    ∃ c : ℝ, 0 < c ∧
    ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      Real.log (erdos256_f n) ≥ C * (n : ℝ) ^ c := by
  sorry

/-- $f^*(n)$ is the variant of $f(n)$ where the exponents are required to be strictly
increasing ($a_1 < \cdots < a_n$) rather than non-decreasing. Bourgain and Chang [BoCh18]
proved $\log f^*(n) \ll (n \log n)^{1/2} \log \log n$. -/
noncomputable def erdos256_fStar (n : ℕ) : ℝ :=
  sInf {y : ℝ | ∃ (a : Fin n → ℕ),
    (∀ i, 0 < a i) ∧ StrictMono a ∧
    y = unitCircleMaxProd n a}

/--
Variant of Erdős Problem 256 with strictly increasing exponents:

Bourgain and Chang [BoCh18] proved that $\log f^*(n) \ll (n \log n)^{1/2} \log \log n$,
where $f^*(n)$ is defined as $f(n)$ but with the exponents required to be strictly
increasing rather than non-decreasing.
-/
@[category research open, AMS 11 30]
theorem erdos_256_strict : ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      Real.log (erdos256_fStar n) ≤
        C * ((n : ℝ) * Real.log n) ^ (1/2 : ℝ) * Real.log (Real.log n) := by
  sorry

end Erdos256
