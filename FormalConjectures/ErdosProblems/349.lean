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

import FormalConjecturesUtil

/-! # Erdős Problem 349

*Reference:* [erdosproblems.com/349](https://www.erdosproblems.com/349)
-/

namespace Erdos349

open Set Filter Real Nat Function


/--
This defines the core property of the problem: For what values of $t,\alpha \in (0,\infty)$
is the sequence $\lfloor t\alpha^n\rfloor$ complete?
-/
def IsGoodPair (t α : ℝ) : Prop :=
  IsAddComplete (range (fun n ↦ ⌊t * α ^ n⌋))

/--
For what values of $t,\alpha \in (0,\infty)$ is the sequence $\lfloor t\alpha^n\rfloor$ complete
(that is, all sufficiently large integers are the sum of distinct integers of the form $\lfloor t\alpha^n\rfloor$)?
-/
@[category research open, AMS 11]
theorem erdos_349 :
    {(t, α) | 0 < t ∧ 0 < α ∧ IsGoodPair t α} = answer(sorry) := by
  sorry

/--
It seems likely that the sequence is complete for all
for all $t>0$ and all $1 < \alpha < \frac{1+\sqrt{5}}{2}$.
-/
@[category research open, AMS 11]
theorem complete_for_alpha_in_Ioo_one_to_goldenRatio (t α : ℝ) (ht : 0 < t)
    (hα : α ∈ Set.Ioo 1 ((1 + √5) / 2)) : IsGoodPair t α := by
  sorry

/--
For any $k$ there exists some $t_k\in (0,1)$ such that the set of $\alpha$
such that the sequence $\lfloor t_k\alpha^n\rfloor$ is complete consists of at least $k$
disjoint line segments.
-/
@[category research solved, AMS 11]
theorem exists_t_for_k_disjoint_segments (k : ℕ) :
    ∃ t ∈ Ioo 0 1, ∃ (ι : Type), k ≤ (Set.univ : Set ι).encard ∧ ∃ I : ι → Set ℝ,
      (∀ i, 2 ≤ (I i).encard ∧ (I i).Nonempty ∧ IsConnected (I i)) ∧
      Pairwise (Disjoint on I) ∧ (⋃ i, I i) ⊆ {α | α > 0 ∧ IsGoodPair t α} := by
  sorry

/--
Is it true that the terms of the sequence $\lfloor (3/2)^n\rfloor$ are odd infinitely
often and even infinitely often?
-/
@[category research open, AMS 11]
theorem erdos_349.variants.floor_3_halves_odd :
    answer(sorry) ↔ {n | Odd ⌊(3/2 : ℝ) ^ n⌋}.Infinite := by
  sorry

/--
Is it true that the terms of the sequence $\lfloor (3/2)^n\rfloor$ are even infinitely often?
-/
@[category research open, AMS 11]
theorem erdos_349.variants.floor_3_halves_even :
    answer(sorry) ↔ {n | Even ⌊(3/2 : ℝ) ^ n⌋}.Infinite := by
  sorry

/-- For $\alpha > 2$ and any $t > 0$, the sequence $\lfloor t\alpha^n\rfloor$ is not additively
complete; equivalently $(t, \alpha)$ is not a "good pair". A partial result on the open Erdős
Problem 349: it complements `complete_for_alpha_in_Ioo_one_to_goldenRatio`.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/23c629bc2347864782ce88f957a64d6567b978a1/FormalConjectures/ErdosProblems/349.lean#L87"]
theorem alpha_gt_two_not_isGoodPair (t α : ℝ) (ht : 0 < t) (hα : 2 < α) : ¬ IsGoodPair t α := by
  sorry

/-- For $0 < \alpha \le 1$ and any $t > 0$, $(t, \alpha)$ is not a good pair: every term
$\lfloor t\alpha^n\rfloor$ lies in the finite interval $[0, \lfloor t\rfloor]$ (since
$\alpha^n \le 1$), so every subset sum is bounded by the constant $\sum_{i \in [0,\lfloor t\rfloor]} i$,
and no large integer can be a subset sum. A partial result on the open Erdős Problem 349,
complementing the $2 < \alpha$ and integer-coefficient cases. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/erdos-349-integer-characterization-proof/FormalConjectures/ErdosProblems/349.lean"]
theorem alpha_le_one_not_isGoodPair (t α : ℝ) (ht : 0 < t) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ¬ IsGoodPair t α := by
  sorry

/-- **Binary expansion.** Every natural number $k$ is a sum of distinct powers of two: there is
a finite set $E$ of exponents with $k = \sum_{i \in E} 2^i$. Proved by strong induction:
subtract the largest power $2^m \le k$, recurse on the remainder. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/erdos-349-integer-characterization-proof/FormalConjectures/ErdosProblems/349.lean"]
theorem exists_finset_sum_two_pow (k : ℕ) :
    ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i := by
  sorry

/-- **The pair $(1, 2)$ is good.** The powers of two $\lfloor 1\cdot 2^n\rfloor = 2^n$ form an
additively complete set: every $k \ge 1$ is a finite sum of distinct powers of two. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/erdos-349-integer-characterization-proof/FormalConjectures/ErdosProblems/349.lean"]
theorem one_two_isGoodPair : IsGoodPair 1 2 := by
  sorry

/-- **The dyadic fiber at $\alpha = 2$.** For every $k$, the pair $(1/2^k, 2)$ is good: the
sequence $\lfloor 2^n / 2^k\rfloor$ is additively complete because at index $n = m + k$ it equals
the exact power $2^m$, so its range contains all powers of two, which already form an additively
complete set. Uses monotonicity `IsAddComplete.mono`. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/erdos-349-integer-characterization-proof/FormalConjectures/ErdosProblems/349.lean"]
theorem dyadic_two_isGoodPair (k : ℕ) : IsGoodPair (1 / 2 ^ k) 2 := by
  sorry

/-- **Integer leading coefficient $t \ge 2$ blocks completeness.** For every integer base
$\alpha$, the pair $(t, \alpha)$ with integer $t \ge 2$ is not good: $\lfloor t\alpha^n\rfloor =
t\alpha^n$ is a multiple of $t$, so every subset sum is too, but two consecutive large integers
cannot both be multiples of $t$. Generalizes the parity obstruction ($t = 2$). A partial result
on Erdős Problem 349. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/erdos-349-integer-characterization-proof/FormalConjectures/ErdosProblems/349.lean"]
theorem int_coeff_ge_two_not_isGoodPair (t : ℤ) (ht : 2 ≤ t) (α : ℤ) :
    ¬ IsGoodPair (t : ℝ) (α : ℝ) := by
  sorry

/-- **Erdős Problem 349, complete characterization on positive integer pairs.** For integers
$t \ge 1$, $\alpha \ge 1$, the pair $(t, \alpha)$ is good (i.e. $\lfloor t\alpha^n\rfloor$ is
additively complete) iff $(t, \alpha) = (1, 2)$. Assembles the four partial results: $(1,2)$ is
good, $\alpha \le 1$ fails, $2 < \alpha$ fails (`alpha_gt_two_not_isGoodPair`), and integer
$t \ge 2$ fails. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/erdos-349-integer-characterization-proof/FormalConjectures/ErdosProblems/349.lean"]
theorem integer_isGoodPair_iff (t α : ℤ) (ht : 1 ≤ t) (hα : 1 ≤ α) :
    IsGoodPair (t : ℝ) (α : ℝ) ↔ t = 1 ∧ α = 2 := by
  sorry

/-- **The pair $(3/2, 2)$ is NOT good.** The negative companion of `dyadic_two_isGoodPair`:
while every dyadic coefficient $1/2^k$ gives a good pair at $\alpha = 2$, the non-dyadic rational
$t = 3/2$ does not. The sequence $\lfloor (3/2)\cdot 2^n\rfloor = 1, 3, 6, 12, 24, \ldots$ is not
additively complete because every term but the first $\lfloor 3/2\rfloor = 1$ is a multiple of
$3$ (namely $\lfloor (3/2)\cdot 2^{n+1}\rfloor = 3\cdot 2^n$), so every subset sum is
$\equiv 0$ or $1 \pmod 3$; the infinitely many integers $\equiv 2 \pmod 3$ are never reached.
A partial result on Erdős Problem 349 in the same divisibility family as
`int_coeff_ge_two_not_isGoodPair` (here the modulus is $3$). -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/erdos-349-three-halves-fiber-proof/FormalConjectures/ErdosProblems/349.lean"]
theorem three_halves_two_not_isGoodPair : ¬ IsGoodPair (3 / 2) 2 := by
  sorry

end Erdos349
