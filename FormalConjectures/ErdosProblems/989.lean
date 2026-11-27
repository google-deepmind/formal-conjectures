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
# Erdős Problem 989

*References:*
- [erdosproblems.com/989](https://www.erdosproblems.com/989)
- [Be87] Beck, J., *Irregularities of distribution. I*. Acta Math. (1987), 1-49.
- [Er64b] Erdős, P., *Problems and results on diophantine approximations*. Compositio Math.
  (1964), 52-65.
-/

@[expose] public section

open Filter Real

open scoped EuclideanGeometry

namespace Erdos989

/--
An infinite discrete set of points in the plane: an infinite set that has only finitely many
points in every closed disc.
-/
def IsInfiniteDiscrete (A : Set ℝ²) : Prop :=
  A.Infinite ∧ ∀ (x : ℝ²) (r : ℝ), (A ∩ Metric.closedBall x r).Finite

/--
The discrepancy $\bigl\lvert \lvert A\cap C\rvert-\pi r^2\bigr\rvert$ of the closed disc $C$ with
centre $x$ and radius $r$.
-/
noncomputable def discrepancy (A : Set ℝ²) (x : ℝ²) (r : ℝ) : ℝ :=
  |((A ∩ Metric.closedBall x r).ncard : ℝ) - π * r ^ 2|

/--
If $A=\{z_1,z_2,\ldots \}\subset \mathbb{R}^2$ is an infinite sequence then let
$$f(r)=\max_C \left\lvert \lvert A\cap C\rvert-\pi r^2\right\rvert,$$
where the maximum is taken over all circles $C$ of radius $r$. Is $f(r)$ unbounded for every $A$?

This is true, and follows from the lower bound of Beck [Be87], see
`erdos_989.variants.lower`.

We take $A$ to be an infinite set with finitely many points in every disc; otherwise some disc
contains infinitely many points of $A$. The statement says that for every $M$ some disc has
discrepancy larger than $M$.
-/
@[category research solved, question, AMS 11 52]
theorem erdos_989 :
    ∀ A : Set ℝ², IsInfiniteDiscrete A → ∀ M : ℝ, ∃ r > 0, ∃ x, M < discrepancy A x r := by
  sorry

/--
Beck [Be87, Theorem 2A] proved that there is a constant $c>0$ such that, for every infinite
discrete set $A\subset\mathbb{R}^2$ and every $r\geq 1$, there is a disc of radius at most $r$
with discrepancy greater than $c r^{1/2}$.
-/
@[category research solved, AMS 11 52]
theorem erdos_989.variants.lower :
    ∃ c > (0 : ℝ), ∀ A : Set ℝ², IsInfiniteDiscrete A → ∀ r ≥ (1 : ℝ),
      ∃ ρ ∈ Set.Ioc 0 r, ∃ x, c * √r < discrepancy A x ρ := by
  sorry

/--
Beck [Be87] showed that the lower bound `erdos_989.variants.lower` is nearly best possible: there
is a constant $C$ such that, for every large $r$, there is an infinite discrete set
$A\subset\mathbb{R}^2$ such that every disc of radius at most $r$ has discrepancy less than
$C (r\log r)^{1/2}$.
-/
@[category research solved, AMS 11 52]
theorem erdos_989.variants.upper :
    ∃ C : ℝ, ∀ᶠ r : ℝ in atTop, ∃ A : Set ℝ², IsInfiniteDiscrete A ∧
      ∀ ρ ∈ Set.Ioc 0 r, ∀ x, discrepancy A x ρ < C * √(r * log r) := by
  sorry

end Erdos989
