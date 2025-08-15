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
# Gauss circle problem

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Gauss_circle_problem)
-/

open Filter

open scoped EuclideanGeometry Real Topology

/-! # Gauss Circle Problem

Consider a circle in $\mathbb{R}^2$ with center at the origin and radius $r\geq 0$.
Gauss's circle problem asks how many points there are inside this circle of the form
$(m, n)$ where $m$ and $n$ are both integers. Equivalently, how many pairs of integers
$m$ and $n$ are there such that
$$
  m^2 + n^2 \leq r^2.
$$
-/

noncomputable section

namespace GaussCircleProblem

/--
Let $N(r)$ be the number of points $(m, n)$ within a circle of radius $r$,
where $m$ and $n$ are both integers.
-/
private abbrev N (r : ℝ) : ℕ :=
  { (m, n) : ℤ × ℤ | !₂[↑m, ↑n] ∈ Metric.closedBall (0 : ℝ²) r }.ncard

/--
Let $E(r)$ be the error term between the number of integral points inside the circle and the
area of the circle; that is $N(r) = \pi r^2 + E(r)$.
-/
private abbrev E (r : ℝ) : ℝ := N r - π * r ^ 2

/--
Gauss proved that
$$
  |E(r)|\leq 2\sqrt{2}\pi r,
$$
for sufficiently large $r$.

[Ha59]  Hardy, G. H. (1959). _Ramanujan: Twelve Lectures on Subjects Suggested by His Life and Work_(3rd ed.). New York: Chelsea Publishing Company. p. 67
-/
@[category research solved, AMS 11]
theorem error_le : ∀ᶠ r in atTop, |E r| ≤ 2 * √2 * π * r := by
  sorry

/--
Hardy and Laundau independently found a lower bound by showing that
$$
  |E(r)| \neq o\left(r^{1/2}(\log r)^{1/4}\right)
$$
-/
@[category research solved, AMS 11]
theorem error_not_isLittleO : ¬E =o[atTop] (fun r => √r * √√r.log) := by
  sorry

/--
It is conjectured that the correct bound is
$$
  |E(r)| = O\left(r^{1/2 + o(1)})\right)
$$

[Ha59]  Hardy, G. H. (1959). _Ramanujan: Twelve Lectures on Subjects Suggested by His Life and Work_(3rd ed.). New York: Chelsea Publishing Company. p. 67

See also https://arxiv.org/abs/2305.03549
-/
@[category research open, AMS 11]
theorem error_isBigO : ∃ (o : ℝ → ℝ) (_ : Tendsto o atTop (𝓝 0)),
    E =O[atTop] fun r => r ^ (1/2 + o r) := by
  sorry

/--
The value of $N(r)$ can be expressed as
$$
  N(r) = 1 + 4\sum_{i=0}^{\infty}\left(\left\lfloor\frac{r^2}{4i+1}\right\rfloor -
    \left\lfloor\frac{r^2}{4i + 3}\right\rfloor\right).
$$
-/
@[category research solved, AMS 11]
theorem exact_form_floor (r : ℝ) (hr : 0 ≤ r) :
    N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋) := by
  sorry

end GaussCircleProblem
