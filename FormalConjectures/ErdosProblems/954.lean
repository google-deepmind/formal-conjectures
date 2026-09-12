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
# Erdős Problem 954

*References:*
- [erdosproblems.com/954](https://www.erdosproblems.com/954)
- [Er77c] Erdős, Paul, *Problems and results on combinatorial number theory. III*.
  Number theory day (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43-72.
- [OEIS A390642](https://oeis.org/A390642)
-/

open Filter Asymptotics

namespace Erdos954

/--
The number of solutions to `seq i + seq j ≤ n` with `0 ≤ i ≤ j ≤ k` and `j ≥ 1`.
-/
def solutionCountWith (seq : ℕ → ℕ) (k n : ℕ) : ℕ :=
  ((Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter
    fun p => p.1 ≤ p.2 ∧ 1 ≤ p.2 ∧ seq p.1 + seq p.2 ≤ n).card

/--
There is always some `n` with strictly fewer than `n` such solutions, since the number of
admissible pairs is at most `(k + 1) ^ 2`.
-/
@[category API, AMS 5 11]
theorem exists_lt_solutionCountWith (seq : ℕ → ℕ) (k : ℕ) :
    ∃ n, solutionCountWith seq k n < n := by
  refine ⟨(k + 1) * (k + 1) + 1, ?_⟩
  have hle : solutionCountWith seq k ((k + 1) * (k + 1) + 1) ≤ (k + 1) * (k + 1) := by
    simpa [solutionCountWith, Finset.card_product, Finset.card_range] using
      Finset.card_filter_le (Finset.range (k + 1) ×ˢ Finset.range (k + 1))
        (fun p => p.1 ≤ p.2 ∧ 1 ≤ p.2 ∧ seq p.1 + seq p.2 ≤ (k + 1) * (k + 1) + 1)
  exact Nat.lt_succ_of_le hle

/--
Rosen's sequence: `a 0 = 0`, `a 1 = 1`, and `a (k + 1)` is the least `n` for which
`solutionCountWith a k n < n`.
-/
def a : ℕ → ℕ :=
  Nat.strongRec fun k ih =>
    match k with
    | 0 => 0
    | k + 1 =>
      let seq (i : ℕ) : ℕ := if h : i < k + 1 then ih i h else 0
      Nat.find (exists_lt_solutionCountWith seq k)

/--
The number of solutions to `a i + a j ≤ x` with `0 ≤ i ≤ j` and `j ≥ 1`. The index bound
`i, j ≤ x` is harmless: the sequence is strictly increasing with `a 0 = 0`, so `n ≤ a n`.
-/
def solutionCount (x : ℕ) : ℕ :=
  solutionCountWith a x x

/-- $a_0 = 0$. -/
@[category test, AMS 5 11]
theorem a_zero : a 0 = 0 := by
  simp [a, Nat.strongRec]

/--
Let $0=a_0<a_1<a_2<\cdots$ be the sequence of integers defined by $a_0=0$ and $a_1=1$, and $a_{k+1}$ is the smallest integer $n$ for which the number of solutions to $a_i+a_j \leq n$ (with $0\leq i\leq j\leq k$ and $j\geq 1$) is $<n$.

Is the number of solutions to $a_i+a_j \leq x$ equal to $x+O(x^{1/4+o(1)})$?
-/
@[category research open, AMS 5 11]
theorem erdos_954 : answer(sorry) ↔
    ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
      IsBigO atTop (fun x => (solutionCount x : ℝ) - x)
        (fun x => (x : ℝ) ^ ((1 : ℝ) / 4 + o x)) := by
  sorry

/--
Note that the number of solutions to $a_i+a_j\leq x$ is always at least $x$ by construction.
-/
@[category research solved, AMS 5 11]
theorem erdos_954.variants.lower_bound (x : ℕ) : x ≤ solutionCount x := by
  sorry

/--
Erdős and Rosen could not even prove whether it is at most $(1+o(1))x$.
-/
@[category research open, AMS 5 11]
theorem erdos_954.variants.linear : answer(sorry) ↔
    ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
      ∀ᶠ x : ℕ in atTop, (solutionCount x : ℝ) ≤ x * (1 + o x) := by
  sorry

end Erdos954
