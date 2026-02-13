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
# Erdős Problem 489

*Reference:* [erdosproblems.com/489](https://www.erdosproblems.com/489)
-/

namespace Erdos489

open Classical Filter
open scoped Topology

/-- The set of positive integers not divisible by any element of `A`. -/
def sievedSet (A : Set ℕ) : Set ℕ := {n : ℕ | 0 < n ∧ ∀ a ∈ A, ¬(a ∣ n)}

/-- The squared-gap sum `∑_{b_i < x} (b_{i+1} - b_i)²`, where `b_i` enumerates the positive
integers not divisible by any element of `A`. -/
noncomputable def GapSumSq (A : Set ℕ) (x : ℕ) : ℝ :=
  letI B := sievedSet A
  let b := Nat.nth (· ∈ B)
  ∑ i < Nat.count (· ∈ B) x, ((b (i + 1) : ℝ) - b i) ^ 2

/--
Let $A\subseteq \mathbb{N}$ be a set such that $\lvert A\cap [1,x]\rvert=o(x^{1/2})$. Let
$B=\{ n\geq 1 : a\nmid n\textrm{ for all }a\in A\}$.
If $B=\{b_1<b_2<\cdots\}$ then is it true that
$$\lim_{x \to \infty} \frac{1}{x}\sum_{b_i<x}(b_{i+1}-b_i)^2$$
exists (and is finite)?

For example, when $A=\{p^2: p\textrm{ prime}\}$ then $B$ is the set of squarefree numbers,
and the existence of this limit was proved by Erdős.

See also [208].
-/
@[category research open, AMS 11]
theorem erdos_489 : answer(sorry) ↔
    ∀ (A : Set ℕ),
      (fun x : ℕ => (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ)) =o[atTop]
        (fun x : ℕ => (x : ℝ).sqrt) →
      (sievedSet A).Infinite →
      ∃ L : ℝ, Tendsto (fun x : ℕ => GapSumSq A x / (x : ℝ)) atTop (𝓝 L) := by
  sorry

/-- When $A = \{p^2 : p \textrm{ prime}\}$, $B$ is the set of squarefree numbers, and the
existence of this limit was proved by Erdős. This is the $\alpha = 2$ case of Erdős Problem 145. -/
@[category research solved, AMS 11]
theorem erdos_489.variants.squarefree :
    ∃ L : ℝ, Tendsto
      (fun x : ℕ => GapSumSq {n | ∃ p, Nat.Prime p ∧ n = p ^ 2} x / (x : ℝ))
      atTop (𝓝 L) := by
  sorry

end Erdos489
