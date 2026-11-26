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
# Erdős Problem 838

*References:*
- [erdosproblems.com/838](https://www.erdosproblems.com/838)
- [Er78c] Erdős, P., *Some more problems on elementary geometry*. Austral. Math. Soc. Gaz. 5
  (1978), 52-54. [PDF](https://www.renyi.hu/~p_erdos/1978-44.pdf)
-/

@[expose] public section

open Filter Asymptotics EuclideanGeometry

namespace Erdos838

/-- The number of convex subsets determined by a finite set $P$ of points of $\mathbb{R}^2$: the
subsets of $P$ that are in convex position (`ConvexIndep`). The empty set, the singletons and the
pairs count as convex. This shifts the count by exactly $1+n+\binom{n}{2}$ for $|P|=n$ compared
with counting only subsets of size at least $3$, and does not affect the asymptotics below. -/
noncomputable def numConvexSubsets (P : Finset ℝ²) : ℕ :=
  Set.ncard {S : Finset ℝ² | S ⊆ P ∧ ConvexIndep (S : Set ℝ²)}

/-- $f(n)$: the least number of convex subsets determined by $n$ points of $\mathbb{R}^2$ with no
three on a line. Such point sets exist for every $n$ (for example $n$ points on a parabola), so
the `sInf` is a true minimum. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ P : Finset ℝ², P.card = n ∧ NonTrilinear (P : Set ℝ²) ∧
    numConvexSubsets P = m}

/-- Any set of $n$ points with no three on a line gives the upper bound $f(n)\leq$ (its number of
convex subsets). -/
@[category API, AMS 52]
theorem f_le {n : ℕ} {P : Finset ℝ²} (hcard : P.card = n) (hP : NonTrilinear (P : Set ℝ²)) :
    f n ≤ numConvexSubsets P :=
  Nat.sInf_le ⟨P, hcard, hP, rfl⟩

def erdos_838.parts.i.answer : ℕ → ℝ := sorry

/--
Let $f(n)$ be maximal such that any $n$ points in $\mathbb{R}^2$, with no three on a line,
determine at least $f(n)$ different convex subsets. Estimate $f(n)$ - in particular, does there
exist a constant $c$ such that
$$\lim \frac{\log f(n)}{(\log n)^2}=c?$$

A question of Erdős and Hammer [Er78c, pp. 52-53]. This is the first part. We read "estimate" as
asking for an asymptotic formula for $\log f(n)$.
-/
@[category research open, question value, AMS 52]
theorem erdos_838.parts.i :
    (fun n : ℕ ↦ Real.log (f n)) ~[atTop] erdos_838.parts.i.answer := by
  sorry

/--
Let $f(n)$ be maximal such that any $n$ points in $\mathbb{R}^2$, with no three on a line,
determine at least $f(n)$ different convex subsets. Estimate $f(n)$ - in particular, does there
exist a constant $c$ such that
$$\lim \frac{\log f(n)}{(\log n)^2}=c?$$

A question of Erdős and Hammer [Er78c, p. 53]. This is the second part.
-/
@[category research open, question, AMS 52]
theorem erdos_838.parts.ii :
    ∃ c : ℝ, Tendsto (fun n : ℕ ↦ Real.log (f n) / Real.log n ^ 2) atTop (nhds c) := by
  sorry

/--
Erdős proved in [Er78c] that there exist constants $c_1,c_2>0$ such that
$$n^{c_1\log n}<f(n)< n^{c_2\log n}.$$
Here $\log$ is the natural logarithm (another base only changes the constants), and $n\geq 2$.
-/
@[category research solved, AMS 52]
theorem erdos_838.variants.erdos_bounds :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ n : ℕ, 2 ≤ n →
      (n : ℝ) ^ (c₁ * Real.log n) < f n ∧ (f n : ℝ) < (n : ℝ) ^ (c₂ * Real.log n) := by
  sorry

end Erdos838
