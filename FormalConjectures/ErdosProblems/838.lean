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
# Erdős Problem 838

Let $f(n)$ be the minimum number of convex subsets determined by $n$ points in general position
in $\mathbb{R}^2$. Does $\log f(n) / (\log n)^2$ converge to a constant?

*Reference:* [erdosproblems.com/838](https://www.erdosproblems.com/838)

[Er78c] Erdős, P. (1978).
-/

open Classical Filter Finset

open scoped Topology Real

namespace Erdos838

/--
A finite point set $P$ in $\mathbb{R}^2$ is in general position if no three of its points
are collinear.
-/
def InGeneralPosition (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = 3 → ¬Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))

/--
A finite point set $S$ in $\mathbb{R}^2$ is in convex position if no point of $S$ lies in
the convex hull of the remaining points.
-/
def InConvexPosition (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ S, p ∉ convexHull ℝ (↑(S.erase p) : Set (EuclideanSpace ℝ (Fin 2)))

/--
The number of subsets of $P$ that are in convex position.
-/
noncomputable def numConvexSubsets (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (P.powerset.filter fun S => InConvexPosition S).card

/--
$f(n)$ is the minimum number of convex subsets determined by any $n$ points in $\mathbb{R}^2$
in general position (no three collinear).
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
    P.card = n ∧ InGeneralPosition P ∧ numConvexSubsets P = k}

/--
Erdős Problem 838 (Erdős–Hammer):
Let $f(n)$ be the maximum number such that any $n$ points in $\mathbb{R}^2$, with no three
collinear, determine at least $f(n)$ different convex subsets. Does there exist
a constant $c$ such that
$$\lim_{n \to \infty} \frac{\log f(n)}{(\log n)^2} = c?$$

Erdős proved that $n^{c_1 \log n} < f(n) < n^{c_2 \log n}$ for some constants
$c_1, c_2 > 0$ [Er78c].
-/
@[category research open, AMS 5 52]
theorem erdos_838 : answer(sorry) ↔
    ∃ c : ℝ, Tendsto (fun n : ℕ => Real.log (f n : ℝ) / (Real.log (n : ℝ)) ^ 2)
      atTop (nhds c) := by
  sorry

end Erdos838
