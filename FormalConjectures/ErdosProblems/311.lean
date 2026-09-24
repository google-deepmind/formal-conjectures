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
# Erdős Problem 311

*References:*
- [erdosproblems.com/311](https://www.erdosproblems.com/311)
- [ErGr80] P. Erdős and R. L. Graham, *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathématique (1980), p. 40.
-/

namespace Erdos311

open Finset Filter Topology

/--
`δ N` is the minimal non-zero value of $|1 - \sum_{n \in A} 1/n|$ as `A` ranges over all subsets
of `{1, …, N}`. The empty set gives the value `1`, so the set below is nonempty for every `N`.
-/
noncomputable def delta (N : ℕ) : ℝ :=
  sInf {x : ℝ | x ≠ 0 ∧ ∃ A ⊆ Icc 1 N, x = |1 - ∑ n ∈ A, (1 : ℝ) / n|}

/--
Let $\delta(N)$ be the minimal non-zero value of $\lvert 1-\sum_{n\in A}\frac{1}{n}\rvert$ as $A$
ranges over all subsets of $\{1,\ldots,N\}$. Is it true that
$$\delta(N)=e^{-(c+o(1))N}$$
for some constant $c\in (0,1)$?

The formulation in [ErGr80] has the additional condition that $A$ contains no $S$ with
$\sum_{n\in S}\frac{1}{n}=1$; Kovac (in the comments on the problem page) showed that the
formulation above is equivalent. We state $\delta(N)=e^{-(c+o(1))N}$ as
$-\log \delta(N) / N \to c$.
-/
@[category research open, AMS 11]
theorem erdos_311 : answer(sorry) ↔
    ∃ c ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun N : ℕ => -Real.log (delta N) / N) atTop (𝓝 c) := by
  sorry

/--
The trivial lower bound: every non-zero value of $1 - \sum_{n \in A} 1/n$ is a non-zero rational
with denominator dividing $[1, \ldots, N]$, so $\delta(N) \geq 1/[1,\ldots,N]$.
-/
@[category textbook, AMS 11]
theorem delta_ge_inv_lcm (N : ℕ) : 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N := by
  sorry

/-- Since $[1, \ldots, N] = e^{(1+o(1))N}$, the trivial bound gives $\delta(N) \ge e^{-(1+o(1))N}$. -/
@[category textbook, AMS 11]
theorem delta_ge_exp : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, Real.exp (-(1 + ε) * N) ≤ delta N := by
  sorry

/-- For `N = 1` the only non-zero value is `|1 - 0| = 1` (from `A = ∅`), so `δ(1) = 1`. -/
@[category test, AMS 11]
theorem delta_one : delta 1 = 1 := by
  have hset : {x : ℝ | x ≠ 0 ∧ ∃ A ⊆ Icc (1 : ℕ) 1, x = |1 - ∑ n ∈ A, (1 : ℝ) / n|} = {1} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, A, hA, rfl⟩
      rw [Icc_self, subset_singleton_iff] at hA
      rcases hA with rfl | rfl
      · simp
      · simp at hx
    · rintro rfl
      exact ⟨one_ne_zero, ∅, empty_subset _, by simp⟩
  unfold delta
  rw [hset, csInf_singleton]

end Erdos311
