/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 107

*Reference:* [erdosproblems.com/107](https://www.erdosproblems.com/107)
-/

open Filter
open EuclideanGeometry

namespace Erdos107

/-- The set `S` is in convex position. -/
def ConvexIndep (S : Set ℝ²) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

/-- The set `P` contains a convex `n`-gon. -/
def HasConvexNGon (n : ℕ) (P : Set ℝ²) : Prop :=
  ∃ S : Finset ℝ², S.card = n ∧ ↑S ⊆ P ∧ ConvexIndep S

noncomputable def f (n : ℕ) : ℕ :=
  sInf { N | ∀ (pts : Finset ℝ²), pts.card = N → NonTrilinear pts.toSet →
    HasConvexNGon n pts }

/--
Let $f(n)$ be minimal such that any $f(n)$ points in $ℝ^2$, no three on a line,
contain $n$ points which form the vertices of a convex $n$-gon.
Prove that $f(n) = 2^{n-2} + 1$.
-/
@[category research open, AMS 52]
theorem erdos_107 : (∀ n ≥ 3, f n = 2^(n - 2) + 1) ↔ answer(sorry) := by
  sorry

/-- Depending on details of definitions,
the statement is false or trivial for $n < 3$. -/
@[category test, AMS 52]
theorem erdos_107.f_zero_eq : f 0 = 0 := by
  have : ∀ P, HasConvexNGon 0 P := by
    intro; use ∅; simp [ConvexIndep]
  simp [f, this]

/--
Erdős and Szekeres proved the bounds
$$
  2^{n-2} + 1 ≤ f(n) ≤ \binom{2n-4}{n-2} + 1
$$
([ErSz60] and [ErSz35] respectively).

[ErSz60] Erdős, P. and Szekeres, G., _On some extremum problems in elementary geometry_.
  Ann. Univ. Sci. Budapest. Eötvös Sect. Math. (1960/61), 53-62.

[ErSz35] Erdős, P. and Szekeres, G., _A combinatorial problem in geometry_.
  Compos. Math. (1935), 463-470.
-/
@[category research solved, AMS 52]
theorem erdos_107.variants.ersz_bounds :
    ∀ n ≥ 3, 2^(n-2) + 1 ≤ f n ∧ f n ≤ Nat.choose (2*n - 4) (n - 2) + 1 := by
  sorry

/--
Suk [Su17] proved
$$
  f(n) ≤ 2^{(1+o(1))n}.
$$

[Su17] Suk, Andrew, _On the Erdős-Szekeres convex polygon problem_.
  J. Amer. Math. Soc. (2017), 1047-1053.
-/
@[category research solved, AMS 52]
theorem erdos_107.variants.su_bound :
    ∃ r : ℕ → ℝ, r =o[atTop] (fun n => (n : ℝ)) ∧
      ∀ n ≥ 3, (f n : ℝ) ≤ 2^(n + r n) := by
  sorry

/--
The current best bound is due to Holmsen, Mojarrad, Pach, and Tardos [HMPT20],
who prove
$$
  f(n) ≤ 2^{n+O(\sqrt{n\log n})}.
$$

[HMPT20] Holmsen, Andreas F. and Mojarrad, Hossein Nassajian and Pach, János and Tardos, Gábor,
  _Two extensions of the Erdős-Szekeres problem_. J. Eur. Math. Soc. (JEMS) (2020), 3981-3995.
-/
@[category research solved, AMS 52]
theorem erdos_107.variants.hmpt_bound :
    ∃ r : ℕ → ℝ, r =O[atTop] (fun n => Real.sqrt (n * Real.log n)) ∧
      ∀ n ≥ 3, (f n : ℝ) ≤ 2^(n + r n) := by
  sorry

end Erdos107
