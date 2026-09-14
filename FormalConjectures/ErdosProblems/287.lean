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
# Erdős Problem 287

*Reference:* [erdosproblems.com/287](https://www.erdosproblems.com/287)
-/

namespace Erdos287

/-- The maximum gap between consecutive terms of a finite sequence `s : Fin k → ℕ`,
i.e., $\max_{0 \le i < k-1} (s(i+1) - s(i))$. -/
def max_gap (k : ℕ) (s : Fin k → ℕ ) : ℕ  :=
   Finset.sup Finset.univ (fun i : Fin (k - 1) =>
      s  ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)

/--
Let $k\geq2$. Is it true that, for any distinct integers
$1 < n_1 < \cdots < n_k$ such that $\sum_{i=1}^k \frac{1}{n_i} = 1$,
we must have $\max(n_{i+1} - n_i) \geq 3$?
-/
@[category research open, AMS 11]
theorem erdos_287 : answer(sorry) ↔
    ∀ (k : ℕ) (hk : 2 ≤ k) (s : Fin k → ℕ),
    StrictMono s → 1 < s ⟨0, by omega⟩ →
    ∑ i : Fin k, 1/ (s i : ℝ) = 1 →
    3 ≤ max_gap k s:= by
  sorry

/--
The lower bound of $\geq 2$ is equivalent to saying that $1$ is not the sum of reciprocals of
consecutive integers, proved by Erdős [Er32].
-/
@[category research solved, AMS 11]
theorem erdos_287.variants.gap_at_least_two :
    ∀ (k : ℕ) (_ : 2 ≤ k) (s : Fin k → ℕ),
    StrictMono s → 1 < s ⟨0, by omega⟩ →
    ∑ i : Fin k, 1 / (s i : ℝ) = 1 →
    2 ≤ max_gap k s := by
  sorry

/--
The example $1 = \frac{1}{2}+\frac{1}{3}+\frac{1}{6}$ shows that $3$ would be best possible here:
the sequence $(2, 3, 6)$ is a valid Egyptian fraction representation of $1$ with
`max_gap = 3`.
-/
@[category test, AMS 11]
theorem erdos_287.test.best_possible :
    let s : Fin 3 → ℕ := ![2, 3, 6]
    StrictMono s ∧
    1 < s 0 ∧
    ∑ i : Fin 3, 1 / (s i : ℝ) = 1 ∧
    max_gap 3 s = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · norm_num [Fin.sum_univ_three, max_gap, show (![2, 3, 6] : Fin 3 → ℕ) 0 = 2 from rfl,
      show (![2, 3, 6] : Fin 3 → ℕ) 1 = 3 from rfl,
      show (![2, 3, 6] : Fin 3 → ℕ) 2 = 6 from rfl]
  · native_decide

/--
For all large $N$, there exists a prime $p \in [N, 2N]$ such that $\frac{p+1}{2}$ is also prime.

This is an open conjecture. If true, it would imply `erdos_287` for all but at most finitely
many exceptions (see `erdos_287.variants.prime_conjecture_implies`).
-/
@[category research open, AMS 11]
theorem erdos_287.variants.prime_conjecture : answer(sorry) ↔
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ p : ℕ, Nat.Prime p ∧ N ≤ p ∧ p ≤ 2 * N ∧ Nat.Prime ((p + 1) / 2) := by
  sorry

/--
The conjecture `erdos_287` would follow for all but at most finitely many exceptions if it were
known that, for all large $N$, there exists a prime $p \in [N, 2N]$ such that $\frac{p+1}{2}$
is also prime.

More precisely: if the prime conjecture holds, then there exists $k_0$ such that for all
$k \geq k_0$, any Egyptian fraction representation of $1$ with $k$ terms and all terms $> 1$
must have $\max(n_{i+1} - n_i) \geq 3$.
-/
@[category textbook, AMS 11]
theorem erdos_287.variants.prime_conjecture_implies : type_of% erdos_287.variants.prime_conjecture →
    ∃ (k₀ : ℕ), ∀ᵉ (k : ℕ) (hk₀ : k₀ ≤ k) (hk : 2 ≤ k) (s : Fin k → ℕ),
      StrictMono s → 1 < s ⟨0, by omega⟩ →
      ∑ i : Fin k, 1 / (s i : ℝ) = 1 →
      3 ≤ max_gap k s := by
  sorry

end Erdos287
