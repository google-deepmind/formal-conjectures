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
public import FormalConjecturesForMathlib.Geometry.«2d»

/-!
# Erdős Problem 652

*References:*
- [erdosproblems.com/652](https://www.erdosproblems.com/652)
- [Ma21] Mathialagan, Surya, *On bipartite distinct distances in the plane*.
  Electron. J. Combin. **28** (2021), no. 4, Paper No. 4.33, 25 pp.
  [doi:10.37236/9687](https://doi.org/10.37236/9687)
- [Discussion](https://www.erdosproblems.com/forum/thread/652)
-/

@[expose] public section

open Filter
open scoped EuclideanGeometry

namespace Erdos652

open scoped Classical in
/-- The positive constants $a$ such that, for all sufficiently large $n$, some set of $n$
points has at least $k$ points determining fewer than $a\sqrt n$ distances to its other points.
Counting these points expresses $R(x_k)<a\sqrt n$ without choosing an ordering. -/
def AdmissibleConstant (k : ℕ) (a : ℝ) : Prop :=
  0 < a ∧ ∀ᶠ n : ℕ in atTop, ∃ points : Finset ℝ²,
    points.card = n ∧
      k ≤ (points.filter fun point => (distinctDistancesFrom points point : ℝ) <
        a * Real.sqrt n).card

/-- The infimum of the admissible positive constants for the $k$th smallest distance count.
An infimum is used because a least constant need not exist for a strict inequality. -/
noncomputable def alpha (k : ℕ) : ℝ :=
  sInf {a | AdmissibleConstant k a}

/-- An admissible constant is strictly positive. -/
@[category test, AMS 5 52]
theorem not_admissibleConstant_zero (k : ℕ) : ¬ AdmissibleConstant k 0 := by
  rintro ⟨ha, -⟩
  exact lt_irrefl _ ha

/-- Let $x_1,\ldots,x_n\in \mathbb{R}^2$ and let
$R(x_i)=\#\{ \lvert x_j-x_i\rvert : j\neq i\}$, where the points are ordered such that
$$R(x_1)\leq \cdots \leq R(x_n).$$
Let $\alpha_k$ be minimal such that, for all large enough $n$, there exists a set of $n$ points
with $R(x_k)<\alpha_kn^{1/2}$. Is it true that $\alpha_k\to \infty$ as $k\to \infty$?

Mathialagan [Ma21] proved that given a set $P$ of $k$ points and a set $Q$ of $n$ points,
with $2\leq k\leq n^{1/3}$, there exists a point in $P$ which determines
$\gg (kn)^{1/2}$ distances to points in $Q$. -/
@[category research solved, question, AMS 5 52]
theorem erdos_652 : Tendsto alpha atTop atTop := by
  sorry

/-- It is trivial that $R(x_1)=1$ is possible.
We require $n\geq 2$ because a singleton determines no distances to other points. -/
@[category research solved, AMS 5 52]
theorem erdos_652.variants.first (n : ℕ) (hn : 2 ≤ n) :
    ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1 := by
  sorry

/-- We always have $R(x_1)R(x_2)\gg n$.
Equivalently, the same bound holds for any two distinct points of the set. -/
@[category research solved, AMS 5 52]
theorem erdos_652.variants.product :
    ∃ c : ℝ, 0 < c ∧ ∀ points : Finset ℝ²,
      ∀ p ∈ points, ∀ q ∈ points, p ≠ q →
        c * points.card ≤
          (distinctDistancesFrom points p : ℝ) * distinctDistancesFrom points q := by
  sorry

/-- Elekes proved that for every $k$ and $n$ sufficiently large there exists some set of
$n$ points with $R(x_k)\ll_k n^{1/2}$. -/
@[category research solved, AMS 5 52]
theorem erdos_652.variants.elekes :
    ∀ k : ℕ, ∃ a : ℝ, AdmissibleConstant k a := by
  sorry

open scoped Classical in
/-- Mathialagan [Ma21, Theorem 14] proved that given a set $P$ of $k$ points and a set $Q$
of $n$ points, with $2\leq k\leq n^{1/3}$, there exists a point in $P$ which determines
$\gg (kn)^{1/2}$ distances to points in $Q$. -/
@[category research solved, AMS 5 52]
theorem erdos_652.variants.mathialagan :
    ∃ c : ℝ, 0 < c ∧ ∀ P Q : Finset ℝ²,
      2 ≤ P.card → P.card ^ 3 ≤ Q.card →
        ∃ p ∈ P, c * Real.sqrt ((P.card : ℝ) * Q.card) ≤
          (Q.image fun q => dist p q).card := by
  sorry

open scoped Classical in
/-- Mathialagan's bound immediately implies $R(x_k)\gg (kn)^{1/2}$ for
$2\leq k\leq n^{1/3}$: fewer than $k$ points have distance count below the bound. -/
@[category research solved, AMS 5 52]
theorem erdos_652.variants.kth_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ points : Finset ℝ², ∀ k : ℕ,
      2 ≤ k → k ^ 3 ≤ points.card →
        (points.filter fun point => (distinctDistancesFrom points point : ℝ) <
          c * Real.sqrt ((k : ℝ) * points.card)).card < k := by
  sorry

/-- Elekes' construction and Mathialagan's lower bound give
$\alpha_k=\Theta(\sqrt k)$, as noted by Zach Hunter in the discussion. -/
@[category research solved, AMS 5 52]
theorem erdos_652.variants.order_sqrt :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      c * Real.sqrt k ≤ alpha k ∧ alpha k ≤ C * Real.sqrt k := by
  sorry

end Erdos652
