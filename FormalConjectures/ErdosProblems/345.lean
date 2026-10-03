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
# Erdős Problem 345

*References:*
- [erdosproblems.com/345](https://www.erdosproblems.com/345)
- [ErGr80] P. Erdős and R. L. Graham, *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathématique (1980), p. 55.
- [OEIS A001661](https://oeis.org/A001661): largest number not the sum of distinct positive
  $k$-th powers.
- [Sp48] R. Sprague, *Über Zerlegungen in n-te Potenzen mit lauter verschiedenen Grundzahlen*.
  Math. Z. 51 (1948), 466--468.
-/

namespace Erdos345

open Filter

/--
The threshold of completeness `T A` of a set `A ⊆ ℕ`: the least positive `m` such that every
`n ≥ m` is a subset sum of `A`. For a complete set (see `IsAddComplete`) such an `m` exists. For a
set that is not complete this is `sInf ∅ = 0`. We require `0 < m` so that `T {1, 2, 3, …} = 1`, as
in the source; `0` is always a subset sum (the empty sum).
-/
noncomputable def threshold (A : Set ℕ) : ℕ :=
  sInf {m | 0 < m ∧ ∀ n, m ≤ n → n ∈ subsetSums A}

/-- The set of positive `k`-th powers `{1^k, 2^k, 3^k, …}`. -/
def powers (k : ℕ) : Set ℕ := {a | ∃ n, 0 < n ∧ a = n ^ k}

/--
Let $A\subseteq \mathbb{N}$ be a complete sequence, and define the threshold of completeness
$T(A)$ to be the least integer $m$ such that all $n\geq m$ are in
$$P(A) = \left\{\sum_{n\in B}n : B\subseteq A\textrm{ finite }\right\}$$
(the existence of $T(A)$ is guaranteed by completeness). Is it true that there are infinitely many
$k$ such that $T(n^k)>T(n^{k+1})$?

Here $T(n^k)$ denotes $T(A)$ for $A = \{1^k, 2^k, 3^k, \ldots\}$. The set of positive $k$-th
powers is complete for every $k \geq 1$ (Sprague, 1948). Erdős and Graham suggest $k = 2^t$ as
candidates. OEIS A001661 lists the largest integer that is not a sum of distinct positive
$k$-th powers, that is $T(n^k) - 1$: $128, 12758, 5134240, 67898771, 11146309947,
766834015734, 4968618780985762$ for $k = 2, \ldots, 8$. These values are increasing in $k$, so
no $k \leq 7$ with $T(n^k) > T(n^{k+1})$ is known.
-/
@[category research open, AMS 11]
theorem erdos_345 : answer(sorry) ↔
    {k : ℕ | 0 < k ∧ threshold (powers (k + 1)) < threshold (powers k)}.Infinite := by
  sorry

/-- The positive `k`-th powers form a complete set for every `k ≥ 1` [Sp48]. -/
@[category research solved, AMS 11]
theorem powers_isAddComplete (k : ℕ) (hk : 0 < k) : IsAddComplete (powers k) := by
  sorry

/-- The set of positive first powers is all of `{1, 2, 3, …}`, so its threshold is `1`. -/
@[category test, AMS 11]
theorem threshold_powers_one : threshold (powers 1) = 1 := by
  have h1 : 1 ∈ {m | 0 < m ∧ ∀ n, m ≤ n → n ∈ subsetSums (powers 1)} := by
    refine ⟨Nat.one_pos, fun n hn => ⟨{n}, ?_, by simp⟩⟩
    intro a ha
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha
    exact ⟨n, hn, by simp [ha]⟩
  apply le_antisymm (Nat.sInf_le h1)
  exact (Nat.sInf_mem ⟨1, h1⟩).1

end Erdos345
