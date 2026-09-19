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
# Erdős Problem 430

*References:*
- [erdosproblems.com/430](https://www.erdosproblems.com/430)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).

The question is equivalent to the first part of
[Erdős Problem 385](https://www.erdosproblems.com/385) (an observation of Sarosh Adenwalla
recorded on both problem pages).
-/

namespace Erdos430

open Filter

/--
The terms of the sequence of Erdős Problem 430 for a given $n$: the integers $m$ with
$1 < m < n$ all of whose prime factors are $> n - m$.

The decreasing sequence $a_1 > a_2 > \cdots$ of the problem lists the elements of this set in
decreasing order: $a_1 = n - 1$ is its largest element and $a_k$ is its largest element below
$a_{k-1}$. The integer $1$ has no prime factors and is not a term of the sequence, which stops
instead, as in the example on erdosproblems.com: for $n = 8$ the sequence is $7, 5$.
-/
def terms (n : ℕ) : Finset ℕ := (Finset.Ioo 1 n).filter fun m => ∀ p ∈ m.primeFactors, n - m < p

/-- For example if $n=8$ we have $a_1=7$ and $a_2=5$ and then must stop. -/
@[category test, AMS 11]
theorem terms_eight : terms 8 = {5, 7} := by
  decide +kernel

/-- The first term of the sequence is $a_1 = n - 1$, the largest element of `terms n`. -/
@[category API, AMS 11]
theorem isGreatest_sub_one {n : ℕ} (hn : 3 ≤ n) : IsGreatest (terms n : Set ℕ) (n - 1) := by
  refine ⟨?_, fun m hm => ?_⟩
  · simp only [terms, Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioo]
    refine ⟨⟨by omega, by omega⟩, fun p hp => ?_⟩
    have := (Nat.prime_of_mem_primeFactors hp).one_lt
    omega
  · simp only [terms, Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioo] at hm
    omega

/--
Fix some integer $n$ and define a decreasing sequence in $[1,n)$ by $a_1=n-1$ and, for
$k\geq 2$, letting $a_k$ be the greatest integer in $[1,a_{k-1})$ such that all of the prime
factors of $a_k$ are $>n-a_k$.

Is it true that, for sufficiently large $n$, not all of this sequence can be prime?
-/
@[category research open, AMS 11]
theorem erdos_430 : answer(sorry) ↔ ∀ᶠ n in atTop, ¬ ∀ m ∈ terms n, m.Prime := by
  sorry

end Erdos430
