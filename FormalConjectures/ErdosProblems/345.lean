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
# Erdős Problem 345

*References:*
- [erdosproblems.com/345](https://www.erdosproblems.com/345)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980), p. 55.
- [Ki17] Kim, D., *On the largest integer that is not a sum of distinct positive nth powers*.
  Journal of Integer Sequences 20 (2017), Article 17.7.5.
  [arXiv:1610.02439](https://arxiv.org/abs/1610.02439)
-/

@[expose] public section

namespace Erdos345

open IsAddComplete

/-- The set of $k$-th powers of positive integers. -/
def kthPowers (k : ℕ) : Set ℕ :=
  {x | ∃ n : ℕ, 0 < n ∧ n ^ k = x}

/--
Let $A\subseteq \mathbb{N}$ be a complete sequence, and define the threshold of completeness
$T(A)$ to be the least integer $m$ such that all $n\geq m$ are in
$$P(A) = \left\{\sum_{n\in B}n : B\subseteq A\textrm{ finite }\right\}$$
(the existence of $T(A)$ is guaranteed by completeness).

Is it true that there are infinitely many $k$ such that $T(n^k)>T(n^{k+1})$?

Here $T(n^k)$ means the threshold of the positive $k$-th powers. Least-threshold witnesses
ensure that the thresholds exist. We restrict to $k\geq 1$, since the zeroth powers form
$\{1\}$, which is incomplete. Positive powers are complete [Ki17].
-/
@[category research open, AMS 5 11]
theorem erdos_345 : answer(sorry) ↔
    {k : ℕ | 0 < k ∧ ∃ a b : ℕ, IsLeast (thresholds (kthPowers k)) a ∧
      IsLeast (thresholds (kthPowers (k + 1))) b ∧ b < a}.Infinite := by
  sorry

/-- Every set of positive $k$-th powers with $k\geq 1$ is complete [Ki17]. -/
@[category research solved, AMS 5 11]
theorem kthPowers_isAddComplete : ∀ k : ℕ, 0 < k → IsAddComplete (kthPowers k) := by
  sorry

/-- Under the convention $0\in\mathbb{N}$, the threshold of the first powers is $0$:
the empty sum represents $0$, and every positive integer is a singleton sum. -/
@[category test, AMS 5 11]
theorem isLeast_thresholds_one : IsLeast (thresholds (kthPowers 1)) 0 := by
  refine ⟨fun n _ ↦ ?_, fun m _ ↦ Nat.zero_le m⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨∅, by simp, by simp⟩
  · refine ⟨{n}, ?_, by simp⟩
    intro x hx
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx
    exact ⟨n, hn, by simp [hx]⟩

@[category test, AMS 5 11]
theorem threshold_one : threshold (kthPowers 1) = 0 :=
  threshold_eq_of_isLeast isLeast_thresholds_one

end Erdos345
