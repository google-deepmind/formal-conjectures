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
# Erdős Problem 1099

*References:*
- [erdosproblems.com/1099](https://www.erdosproblems.com/1099)
- [Er81h] Erdős, P., Some problems and results on additive and multiplicative number theory.
  Analytic number theory (Philadelphia, Pa., 1980) (1981), 171-182.
- [Vo84] Vose, Michael D., Integers with consecutive divisors in small ratio. J. Number Theory
  (1984), 233-238.
-/

open Filter Finset Real
open scoped Topology

namespace Erdos1099

/-- The ordered list of positive divisors of `n`. -/
def orderedDivisors (n : ℕ) : List ℕ :=
  n.divisors.sort (· ≤ ·)

/-- Consecutive ratios minus one: for $d_1<\cdots<d_k$, the list
$(d_2/d_1-1,\ldots,d_k/d_{k-1}-1)$. Empty when `n` has fewer than two divisors. -/
noncomputable def consecutiveRatioGaps : List ℕ → List ℝ
  | a :: b :: rest => ((b : ℝ) / a - 1) :: consecutiveRatioGaps (b :: rest)
  | _ => []

/-- $h_\alpha(n)=\sum_i (d_{i+1}/d_i-1)^\alpha$ over consecutive divisors of $n$. -/
noncomputable def h (α : ℝ) (n : ℕ) : ℝ :=
  (consecutiveRatioGaps (orderedDivisors n)).map (fun t ↦ t ^ α) |>.sum

/-- $\sum_i d_{i+1}/d_i$. -/
noncomputable def sumConsecutiveRatios (n : ℕ) : ℝ :=
  (consecutiveRatioGaps (orderedDivisors n)).map (fun t ↦ t + 1) |>.sum

/--
Let $1=d_1<\cdots<d_{\tau(n)}=n$ be the divisors of $n$, and for $\alpha>1$ let
$$
h_\alpha(n) = \sum_i \left( \frac{d_{i+1}}{d_i}-1\right)^\alpha.
$$
Is it true that
$$
\liminf_{n\to \infty}h_\alpha(n) \ll_\alpha 1?
$$

A positive answer to the main question was provided by Vose [Vo84] by constructing a specific
sequence.
-/
@[category research solved, AMS 11]
theorem erdos_1099 :
    answer(True) ↔
      ∀ α > (1 : ℝ), ∃ C : ℝ, 0 < C ∧ liminf (fun n : ℕ ↦ h α n) atTop ≤ C := by
  sorry

/--
The $\liminf$ is trivially $\geq 1$, just considering the term $i=1$.
-/
@[category textbook, AMS 11]
theorem erdos_1099.variants.liminf_ge_one (α : ℝ) (hα : 1 < α) :
    1 ≤ liminf (fun n : ℕ ↦ h α n) atTop := by
  sorry

/--
Erdős [Er81h] remarks that $n!$ would be a good candidate for an infinite sequence of $n$ with
$h_\alpha(n)$ bounded. It remains open whether this sequence satisfies this property.
-/
@[category research open, AMS 11]
theorem erdos_1099.variants.factorial :
    answer(sorry) ↔
      ∀ α > (1 : ℝ), ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, h α n.factorial ≤ C := by
  sorry

/--
Erdős [Er81h] remarks that the least common multiple of $\{1,\ldots,n\}$ would be a good candidate
for an infinite sequence of $n$ with $h_\alpha(n)$ bounded. It remains open whether this sequence
satisfies this property.
-/
@[category research open, AMS 11]
theorem erdos_1099.variants.lcm :
    answer(sorry) ↔
      ∀ α > (1 : ℝ), ∃ C : ℝ, 0 < C ∧
        ∀ n ≥ 1, h α ((Icc 1 n).lcm id) ≤ C := by
  sorry

/--
Erdős remarks that this problem occurred to him when considering $\sum_i \frac{d_{i+1}}{d_i}$.
It is easy to see that
$$
\sum_{i} \frac{d_{i+1}}{d_i}> \tau(n)+\log n,
$$
and Erdős asked whether
$$
\liminf \left(\sum_{i} \frac{d_{i+1}}{d_i}-\tau(n)-\log n\right)<\infty,
$$
which would follow from an affirmative answer to the main question.
-/
@[category research solved, AMS 11]
theorem erdos_1099.variants.sum_ratios :
    liminf (fun n : ℕ ↦
      (sumConsecutiveRatios n - (n.divisors.card : ℝ) - log n : EReal)) atTop < ⊤ := by
  sorry

/-- $h_\alpha(1)=0$ (a single divisor, empty sum). -/
@[category test, AMS 11]
theorem erdos_1099.variants.h_one (α : ℝ) : h α 1 = 0 := by
  simp [h, orderedDivisors, consecutiveRatioGaps]

end Erdos1099
