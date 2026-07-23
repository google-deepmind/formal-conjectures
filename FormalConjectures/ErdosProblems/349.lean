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
subtract the largest power $2^m \le k$, recurse on the remainder. A textbook-level building
block for `one_two_isGoodPair` below; it says nothing about `IsGoodPair` itself. -/
@[category textbook, AMS 11,
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

/-- A set $A \subseteq \mathbb{Z}$ is *entirely additively complete* if **every** positive integer
is a finite subset sum of $A$ (van Doorn's "entirely complete": $P(A) = \mathbb{N}_{\ge 1}$).
Strictly stronger than `IsAddComplete`, which only requires all *sufficiently large* integers.

This is a problem-local definition; it could be promoted to
`FormalConjecturesForMathlib/NumberTheory/AdditivelyComplete.lean` (next to `IsAddComplete`) if
the maintainers prefer it to live there. -/
def IsEntirelyAddComplete (A : Set ℤ) : Prop :=
  ∀ k : ℤ, 1 ≤ k → k ∈ subsetSums A

/-- **Glue.** Entire completeness implies (eventual) completeness: if every $k \ge 1$ is a subset
sum, then in particular all sufficiently large $k$ are. Textbook-level: an immediate consequence
of the definitions, not itself a partial result on Erdős Problem 349. -/
@[category textbook, AMS 11]
theorem isEntirelyAddComplete_imp_isAddComplete {A : Set ℤ}
    (h : IsEntirelyAddComplete A) : IsAddComplete A :=
  Filter.eventually_atTop.mpr ⟨1, fun k hk => h k hk⟩

/-- **Abstract single-gap criterion.** For a monotone, nonnegative integer sequence $a$, a single
gap $\sum_{k < r+1} a_k < m < a_{r+1}$ with $m \ge 1$ already shows that $m$ is not a subset sum,
hence the range of $a$ is not entirely additively complete.

This is the pure-$\mathbb{Z}$ core of `alpha_gt_two_not_isGoodPair`'s
`by_cases ∃ b ∈ B, a (r+1) ≤ b` case-split, with $m$ *given* rather than constructed via
`Tendsto` (strictly easier, and enough for the band $5/3 \le \alpha < 2$ below). A textbook-level
combinatorial fact about monotone integer sequences, phrased abstractly (no $t, \alpha$); the
research content of Erdős Problem 349 is in its application below. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/erdos-349-entire-gap-criterion-proof/FormalConjectures/ErdosProblems/349.lean"]
theorem entire_gap_not_complete (a : ℕ → ℤ) (hmono : Monotone a) (hnn : ∀ n, 0 ≤ a n)
    (r : ℕ) (m : ℤ) (hm : 1 ≤ m)
    (hlo : (∑ k ∈ Finset.range (r + 1), a k) < m) (hhi : m < a (r + 1)) :
    ¬ IsEntirelyAddComplete (Set.range a) := by
  sorry

/-- The $0$-th term of $\lfloor t\alpha^n\rfloor$ is $\lfloor t\rfloor$ (since $\alpha^0 = 1$).
Textbook-level: a one-line simplification, not a partial result on Erdős Problem 349. -/
@[category textbook, AMS 11]
theorem floorSeq_zero (t α : ℝ) : ⌊t * α ^ (0 : ℕ)⌋ = ⌊t⌋ := by
  simp [pow_zero, mul_one]

/-- The $1$-st term of $\lfloor t\alpha^n\rfloor$ is $\lfloor t\alpha\rfloor$. Textbook-level:
a one-line simplification, not a partial result on Erdős Problem 349. -/
@[category textbook, AMS 11]
theorem floorSeq_one (t α : ℝ) : ⌊t * α ^ (1 : ℕ)⌋ = ⌊t * α⌋ := by
  simp [pow_one]

/-- $n \mapsto \lfloor t\alpha^n\rfloor$ is monotone when $0 \le t$ and $1 \le \alpha$.
Textbook-level: elementary monotonicity of `Int.floor` composed with a monotone power. -/
@[category textbook, AMS 11]
theorem floorSeq_monotone (t α : ℝ) (ht : 0 ≤ t) (hα : 1 ≤ α) :
    Monotone (fun n => ⌊t * α ^ n⌋) := by
  intro n m hnm
  simp only
  apply Int.floor_le_floor
  apply mul_le_mul_of_nonneg_left _ ht
  exact pow_le_pow_right₀ hα hnm

/-- $n \mapsto \lfloor t\alpha^n\rfloor$ is nonnegative when $0 \le t$ and $0 \le \alpha$.
Textbook-level: an immediate `positivity` consequence, not a partial result on Erdős Problem 349. -/
@[category textbook, AMS 11]
theorem floorSeq_nonneg (t α : ℝ) (ht : 0 ≤ t) (hα : 0 ≤ α) (n : ℕ) :
    0 ≤ (fun n => ⌊t * α ^ n⌋) n := by
  simp only
  rw [Int.floor_nonneg]
  positivity

/-- **Application inside the band $5/3 \le \alpha < 2$.** For $t \ge 3$ and $5/3 \le \alpha < 2$,
the sequence $\lfloor t\alpha^n\rfloor$ is NOT entirely additively complete: the very first gap
$\lfloor t\rfloor < \lfloor t\rfloor+1 < \lfloor t\alpha\rfloor$ already misses the positive
integer $\lfloor t\rfloor+1$.

This is the $r = 0$, $m = \lfloor t\rfloor + 1$ instance of `entire_gap_not_complete`. The gap
inequality comes from $t\alpha \ge t\cdot(5/3) = t + 2t/3 \ge t + 2 \ge \lfloor t\rfloor + 2$.
The constant $5/3$ (not $\varphi$) is the sharp clean threshold uniform in $t \ge 3$: at
$\alpha = \varphi$, $t = 3$ gives $\lfloor 3\varphi\rfloor = 4 = \lfloor t\rfloor+1$, so the first
gap closes. This is *entire* (not eventual) incompleteness; the gap need not recur for
$\varphi \le \alpha < 2$, where Erdős Problem 349 stays open. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/erdos-349-entire-gap-criterion-proof/FormalConjectures/ErdosProblems/349.lean"]
theorem floorSeq_not_entirelyComplete_of_le_two
    (t α : ℝ) (ht : 3 ≤ t) (hα : 5 / 3 ≤ α) (hα2 : α < 2) :
    ¬ IsEntirelyAddComplete (Set.range (fun n => ⌊t * α ^ n⌋)) := by
  sorry

/-- **Abstract doubling criterion** (van Doorn's Lemma 3, applied with base phase length $r = 0$).

Let $a : \mathbb{N} \to \mathbb{Z}$ be a monotone integer sequence with $a_0 = 1$, satisfying the
doubling bound $a_{n+1} \le 2 a_n$ for every $n$, and unbounded ($\forall M,\ \exists n,\ M \le
a_n$). Then every positive integer is a finite subset sum of distinct values of $a$, i.e. the
range of $a$ is entirely additively complete.

A textbook-level combinatorial fact about monotone integer sequences (no $t, \alpha$); its
application to $a_n = \lfloor \alpha^n \rfloor$ below (`isGoodPair_one_alpha_of_lt_three_halves`)
is the research content of Erdős Problem 349.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/6e869b32eccf185e6c57f3f5cae571a8ce1bb4fb/FormalConjectures/ErdosProblems/349.lean#L708"]
theorem entirely_complete_of_doubling (a : ℕ → ℤ)
    (ha0 : a 0 = 1)
    (hmono : Monotone a)
    (hdouble : ∀ n, a (n + 1) ≤ 2 * a n)
    (hub : ∀ M : ℤ, ∃ n, M ≤ a n) :
    IsEntirelyAddComplete (Set.range a) := by
  sorry

/-- **Doubling bound for the floor of a power sequence.** For $1 < \alpha < 3/2$ and any
$n \ge 0$, $\lfloor \alpha^{n+1} \rfloor \le 2 \lfloor \alpha^n \rfloor$.

Proof: $\alpha^{n+1} = \alpha \cdot \alpha^n < \tfrac{3}{2}\alpha^n \le \tfrac{3}{2}(\lfloor
\alpha^n\rfloor + 1) \le 2\lfloor \alpha^n\rfloor + 1$, using $\lfloor \alpha^n\rfloor \ge 1$
(since $\alpha > 1$). A textbook-level floor/inequality fact. -/
@[category textbook, AMS 11]
theorem floor_pow_succ_le_two_mul_floor_pow (α : ℝ) (hα_lo : 1 < α) (hα_hi : α < 3 / 2)
    (n : ℕ) :
    ⌊α ^ (n + 1)⌋ ≤ 2 * ⌊α ^ n⌋ := by
  have hpos : (0 : ℝ) < α ^ n := by positivity
  have hone : (1 : ℝ) ≤ α ^ n := one_le_pow₀ hα_lo.le
  have hm1 : (1 : ℤ) ≤ ⌊α ^ n⌋ := by rw [Int.le_floor]; push_cast; linarith
  have hflo : (↑(⌊α ^ n⌋) : ℝ) ≤ α ^ n := Int.floor_le _
  have hfle : α ^ n - 1 < (↑(⌊α ^ n⌋) : ℝ) := by linarith [Int.sub_one_lt_floor (α ^ n)]
  rw [Int.floor_le_iff]
  push_cast
  have hsucc : α ^ (n + 1) = α * α ^ n := by ring
  rw [hsucc]
  have hm1r : (1 : ℝ) ≤ (↑(⌊α ^ n⌋) : ℝ) := by exact_mod_cast hm1
  nlinarith [mul_pos (by linarith : (0 : ℝ) < α) hpos, hflo, hfle, hm1r]

/-- **Erdős Problem 349, Proposition 6 (van Doorn), "if" direction, case $t = 1$.**

For $1 < \alpha < 3/2$, the pair $(1, \alpha)$ is good: the sequence $\lfloor \alpha^n\rfloor$ is
additively complete (in fact *entirely* additively complete — every $k \ge 1$ is a finite subset
sum of distinct terms $\lfloor \alpha^n\rfloor$).

A **partial result** on the open Erdős Problem 349: it complements
`floorSeq_not_entirelyComplete_of_le_two` (which rules out $5/3 \le \alpha < 2$ for $t \ge 3$) and
the integer-pair characterization `integer_isGoodPair_iff`. Proof: instantiate
`entirely_complete_of_doubling` with $a_n = \lfloor \alpha^n\rfloor$, using
`floor_pow_succ_le_two_mul_floor_pow` for the doubling bound.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/6e869b32eccf185e6c57f3f5cae571a8ce1bb4fb/FormalConjectures/ErdosProblems/349.lean#L864"]
theorem isGoodPair_one_alpha_of_lt_three_halves (α : ℝ) (hα_lo : 1 < α) (hα_hi : α < 3 / 2) :
    IsGoodPair 1 α := by
  sorry

/-- **First-term value for $1 \le t < 2$.** The $0$-th term of the floor sequence is
$\lfloor t\alpha^0\rfloor = \lfloor t\rfloor = 1$. Textbook-level: an immediate consequence of
`floorSeq_zero` and `Int.floor_eq_iff`, not itself a partial result on Erdős Problem 349. -/
@[category textbook, AMS 11]
theorem floorSeq_zero_eq_one_of_lt_two (t α : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) :
    ⌊t * α ^ (0 : ℕ)⌋ = 1 := by
  simp only [pow_zero, mul_one]
  rw [Int.floor_eq_iff]
  constructor
  · push_cast; linarith
  · push_cast; linarith

/-- **Doubling bound for a general floor power sequence.** For $1 < \alpha < 3/2$, $1 \le t$, and
any $n \ge 0$, $\lfloor t\alpha^{n+1}\rfloor \le 2\lfloor t\alpha^n\rfloor$.

Generalizes `floor_pow_succ_le_two_mul_floor_pow` (the $t = 1$ case) to every $t \ge 1$: the
argument only needs $\lfloor t\alpha^n\rfloor \ge 1$, which now comes from $t \ge 1$ rather than
from $\alpha > 1$ alone. Textbook-level floor/inequality fact, not itself a partial result on
Erdős Problem 349. -/
@[category textbook, AMS 11]
theorem floor_mul_pow_succ_le_two_mul (t α : ℝ) (hα_lo : 1 < α) (hα_hi : α < 3 / 2)
    (ht1 : 1 ≤ t) (n : ℕ) :
    ⌊t * α ^ (n + 1)⌋ ≤ 2 * ⌊t * α ^ n⌋ := by
  have hpos : (0 : ℝ) < α ^ n := by positivity
  have hone : (1 : ℝ) ≤ α ^ n := one_le_pow₀ hα_lo.le
  have htpow : (1 : ℝ) ≤ t * α ^ n := by nlinarith [ht1, hone]
  have hm1 : (1 : ℤ) ≤ ⌊t * α ^ n⌋ := by rw [Int.le_floor]; push_cast; linarith
  have hflo : (↑(⌊t * α ^ n⌋) : ℝ) ≤ t * α ^ n := Int.floor_le _
  have hfle : (t * α ^ n) - 1 < (↑(⌊t * α ^ n⌋) : ℝ) := by
    linarith [Int.sub_one_lt_floor (t * α ^ n)]
  rw [Int.floor_le_iff]
  push_cast
  have hsucc : t * α ^ (n + 1) = α * (t * α ^ n) := by ring
  rw [hsucc]
  have hm1r : (1 : ℝ) ≤ (↑(⌊t * α ^ n⌋) : ℝ) := by exact_mod_cast hm1
  nlinarith [mul_pos (by linarith : (0 : ℝ) < α) (by nlinarith [htpow] : (0 : ℝ) < t * α ^ n),
    hflo, hfle, hm1r]

/-- **Erdős Problem 349, sharp entire completeness for $1 \le t < 2$ on the strip
$1 < \alpha < 3/2$.**

The sequence $\lfloor t\alpha^n\rfloor$ is *entirely* additively complete: every positive
integer $k \ge 1$ is a finite subset sum of distinct terms.

A **partial result** on the open Erdős Problem 349 and on the named open conjecture
`complete_for_alpha_in_Ioo_one_to_goldenRatio` (restricted to $\alpha < 3/2$, entire sense, and
$t < 2$). Sharpens `isGoodPair_one_alpha_of_lt_three_halves` (its $t = 1$ special case) by taking
$t < 2$ as a direct hypothesis instead of deriving it from $t\alpha < 2$: the doubling bound
`floor_mul_pow_succ_le_two_mul` already holds for every $1 \le t$ on this strip, so the widening
is free. E.g. $(t, \alpha) = (1.7, 1.4)$ has $t\alpha = 2.38 > 2$ yet is covered here.

Proof: instantiate `entirely_complete_of_doubling` with $a_n = \lfloor t\alpha^n\rfloor$, using
`floorSeq_zero_eq_one_of_lt_two` for $a_0 = 1$ and `floor_mul_pow_succ_le_two_mul` for the
doubling bound.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/fc02fb6d4045478b070742b7d04d09ceed561183/FormalConjectures/ErdosProblems/349.lean#L949"]
theorem isEntirelyAddComplete_of_one_le_lt_two (t α : ℝ) (hα_lo : 1 < α) (hα_hi : α < 3 / 2)
    (ht1 : 1 ≤ t) (ht2 : t < 2) :
    IsEntirelyAddComplete (Set.range (fun n : ℕ ↦ ⌊t * α ^ n⌋)) := by
  sorry

/-- **Erdős Problem 349, good pair for $1 \le t < 2$ on the strip $1 < \alpha < 3/2$.**

Corollary of `isEntirelyAddComplete_of_one_le_lt_two`, lifted from entire to eventual
completeness via `isEntirelyAddComplete_imp_isAddComplete`. A partial result on the named open
conjecture `complete_for_alpha_in_Ioo_one_to_goldenRatio`, restricted to $\alpha < 3/2$ and
$t < 2$.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline (it depends on a linked theorem). -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/fc02fb6d4045478b070742b7d04d09ceed561183/FormalConjectures/ErdosProblems/349.lean#L983"]
theorem isGoodPair_of_one_le_lt_two (t α : ℝ) (hα_lo : 1 < α) (hα_hi : α < 3 / 2)
    (ht1 : 1 ≤ t) (ht2 : t < 2) :
    IsGoodPair t α := by
  sorry

/-- **Erdős Problem 349, not entirely complete for $2 \le t$.**

For $2 \le t$ and $1 \le \alpha$, every term $\lfloor t\alpha^n\rfloor \ge \lfloor t\rfloor \ge 2$,
so every subset sum of the range is $0$ (empty subset) or $\ge 2$ (nonempty subset of values each
$\ge 2$): the value $1$ is never a subset sum, so the range is not entirely additively complete.

This is the DeepMind-faithful "only if" direction of the sharp threshold ($t \ge 2$), and it
matters to state precisely: the superficially plausible stronger claim "$t\alpha \ge 2 \Rightarrow$
not entirely complete" is FALSE under this repository's $n = 0$ indexing — e.g.
$(t, \alpha) = (3/2, 7/5)$ has $t\alpha = 2.1 \ge 2$ yet IS entirely complete, because
$a_0 = \lfloor t\rfloor = 1$ already saves it. The correct sharp threshold is on $t$ alone, not on
$t\alpha$; that is exactly `entirelyComplete_floorSeq_iff_lt_two` below.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/fc02fb6d4045478b070742b7d04d09ceed561183/FormalConjectures/ErdosProblems/349.lean#L1006"]
theorem not_entirelyComplete_of_two_le (t α : ℝ) (ht : 2 ≤ t) (hα : 1 ≤ α) :
    ¬ IsEntirelyAddComplete (Set.range (fun n : ℕ ↦ ⌊t * α ^ n⌋)) := by
  sorry

/-- **Erdős Problem 349, sharp entire characterization on the strip $1 < \alpha < 3/2$.**

For $1 \le t$ and $1 < \alpha < 3/2$:
$$\text{IsEntirelyAddComplete}\big(\operatorname{range}(n \mapsto \lfloor t\alpha^n\rfloor)\big)
\iff t < 2.$$
Assembles `isEntirelyAddComplete_of_one_le_lt_two` and `not_entirelyComplete_of_two_le`, split on
$t < 2 \lor 2 \le t$. The threshold is exactly $t = 2$: that is where the front term $a_0$ jumps
from $1$ to $2$ and blocks the value $1$. A partial result on the named open conjecture
`complete_for_alpha_in_Ioo_one_to_goldenRatio`, sharp on the sub-strip $1 < \alpha < 3/2$ (in the
entire sense).

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline (it depends on two linked theorems). -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/fc02fb6d4045478b070742b7d04d09ceed561183/FormalConjectures/ErdosProblems/349.lean#L1041"]
theorem entirelyComplete_floorSeq_iff_lt_two (t α : ℝ) (hα_lo : 1 < α) (hα_hi : α < 3 / 2)
    (ht1 : 1 ≤ t) :
    IsEntirelyAddComplete (Set.range (fun n : ℕ ↦ ⌊t * α ^ n⌋)) ↔ t < 2 := by
  sorry


/-- **Distinct-value prefix sum.** `C a N` is the sum of the *distinct* values among
`a 0, ..., a (N - 1)`, i.e. the "running reachable total" for subset sums over the SET
`Set.range a` (duplicate values counted once, unlike a plain prefix sum). Auxiliary to
`floorSeq_brown_all` / `eventuallyComplete_of_brown_of_base_window` below. -/
noncomputable def C (a : ℕ → ℤ) (N : ℕ) : ℤ := ∑ x ∈ (Finset.range N).image a, x

/-- **Unboundedness of the floor sequence.** For $t > 0$ and $\alpha > 1$, the sequence
$n \mapsto \lfloor t\alpha^n\rfloor$ is unbounded above: for every $M$ there is an $n$ with
$M \le \lfloor t\alpha^n\rfloor$. Textbook-level consequence of $\alpha^n \to \infty$, not itself
a partial result on Erdős Problem 349; a building block for `isGoodPair_of_pos_of_lt_two` below. -/
@[category textbook, AMS 11]
theorem floorSeq_unbounded (t α : ℝ) (ht : 0 < t) (hα1 : 1 < α) :
    ∀ M : ℤ, ∃ n : ℕ, M ≤ ⌊t * α ^ n⌋ := by
  intro M
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (((M : ℝ) + 1) / t) hα1
  refine ⟨n, Int.le_floor.mpr ?_⟩
  have : (M : ℝ) + 1 < t * α ^ n := by
    rw [div_lt_iff₀ ht] at hn; linarith
  linarith

/-- **Distinct-value prefix sum, toolbox: the empty prefix.** $C\ a\ 0 = 0$. Textbook-level;
shared with `entirely_complete_of_doubling` above (same `C`), reused here for the small-$t$
eventual-completeness engine. -/
@[category textbook, AMS 11]
theorem C_zero (a : ℕ → ℤ) : C a 0 = 0 := by simp [C]

/-- **Distinct-value prefix sum, toolbox: the one-term prefix.** $C\ a\ 1 = a_0$.
Textbook-level. -/
@[category textbook, AMS 11]
theorem C_one (a : ℕ → ℤ) : C a 1 = a 0 := by simp [C]

/-- **Distinct-value prefix sum, toolbox: duplicates.** If $a_n$ already occurred among
$a_0, \ldots, a_{n-1}$, then $C\ a\ (n+1) = C\ a\ n$. Textbook-level. -/
@[category textbook, AMS 11]
theorem C_succ_of_mem (a : ℕ → ℤ) {n : ℕ} (h : a n ∈ (Finset.range n).image a) :
    C a (n + 1) = C a n := by
  have himg : (Finset.range (n + 1)).image a = (Finset.range n).image a := by
    rw [Finset.range_add_one, Finset.image_insert, Finset.insert_eq_self.mpr h]
  simp only [C, himg]

/-- **Distinct-value prefix sum, toolbox: genuinely new values.** If $a_n$ did not occur among
$a_0, \ldots, a_{n-1}$, then $C\ a\ (n+1) = a_n + C\ a\ n$. Textbook-level. -/
@[category textbook, AMS 11]
theorem C_succ_of_notMem (a : ℕ → ℤ) {n : ℕ} (h : a n ∉ (Finset.range n).image a) :
    C a (n + 1) = a n + C a n := by
  have himg : (Finset.range (n + 1)).image a = insert (a n) ((Finset.range n).image a) := by
    rw [Finset.range_add_one, Finset.image_insert]
  simp only [C, himg, Finset.sum_insert h]

/-- **Distinct-value prefix sum, toolbox: strict novelty.** A value strictly larger than all of
its predecessors has not occurred before. Textbook-level. -/
@[category textbook, AMS 11]
theorem notMem_image_of_forall_lt (a : ℕ → ℤ) {n : ℕ} (h : ∀ j, j < n → a j < a n) :
    a n ∉ (Finset.range n).image a := by
  intro hmem
  rw [Finset.mem_image] at hmem
  obtain ⟨j, hj, hja⟩ := hmem
  have := h j (Finset.mem_range.mp hj)
  omega

/-- **Distinct-value prefix sum, toolbox: domination.** Each nonnegative term is dominated by
the prefix sum containing it: $a_n \le C\ a\ (n+1)$. Textbook-level. -/
@[category textbook, AMS 11]
theorem le_C_succ (a : ℕ → ℤ) (hnn : ∀ n, 0 ≤ a n) (n : ℕ) : a n ≤ C a (n + 1) := by
  have hmem : a n ∈ (Finset.range (n + 1)).image a := by
    rw [Finset.mem_image]; exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), rfl⟩
  have : a n ≤ ∑ x ∈ (Finset.range (n + 1)).image a, x := by
    apply Finset.single_le_sum (f := id) _ hmem
    intro x hx; rw [Finset.mem_image] at hx; obtain ⟨i, _, rfl⟩ := hx; exact hnn i
  simpa [C] using this

/-- **Abstract eventual-completeness engine from a base window.** Let $a : \mathbb{N} \to
\mathbb{Z}$ be nonnegative, monotone and unbounded, and suppose there are a rank $N_0$ and a
threshold $L$ such that: (i) *base window* — every $k$ with $L \le k \le C\ a\ N_0$ is already a
subset sum of $\{a_0, \ldots, a_{N_0 - 1}\}$; (ii) *shifted Brown margin* — $a_n + L \le 1 + C\ a\
n$ for every $n \ge N_0$. Then $\operatorname{range} a$ is additively complete in the eventual
sense (in fact every $k \ge L$ is a finite subset sum).

Textbook-level: a purely combinatorial merge-induction on monotone integer sequences, phrased
abstractly (no $t, \alpha$); the research content of Erdős Problem 349 is in its instantiation
`isGoodPair_of_pos_of_lt_two` below. Analogous in spirit to `entirely_complete_of_doubling` above,
but concluding *eventual* (not *entire*) completeness from a *base-window* hypothesis instead of a
doubling bound — the two are independent engines for different regimes.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/0ed837c90387a146fc88a23172074d01533f94ee/FormalConjectures/ErdosProblems/349.lean#L1134"]
theorem eventuallyComplete_of_brown_of_base_window (a : ℕ → ℤ)
    (hnn : ∀ n, 0 ≤ a n)
    (hmono : Monotone a)
    (hub : ∀ M : ℤ, ∃ n, M ≤ a n)
    (N₀ : ℕ) (L : ℤ)
    (hbase : ∀ k : ℤ, L ≤ k → k ≤ C a N₀ →
      k ∈ subsetSums (((Finset.range N₀).image a : Finset ℤ) : Set ℤ))
    (hbrown : ∀ n : ℕ, N₀ ≤ n → a n + L ≤ 1 + C a n) :
    IsAddComplete (Set.range a) := by
  sorry

/-- **Universal Brown condition for $0 < t < 2$ on the strip $1 < \alpha < 3/2$.** The floor
sequence $a_n = \lfloor t\alpha^n\rfloor$ satisfies $a_n \le 1 + C(n)$ for **every** $n$ (not
merely eventually), where $C(n)$ sums the distinct values among $a_0, \ldots, a_{n-1}$. This is
the `hbrown` hypothesis of `eventuallyComplete_of_brown_of_base_window` instantiated with the
witnesses $N_0 = 0$, $L = 0$: since $C\ a\ 0 = 0$, no "eventually" is available and the bound must
hold from $n = 0$ on.

Proof sketch (two phases, split at the first index $n_0$ where the sequence jumps by at least
$2$): while all increments are $\le 1$ (Phase 1), $t < 2$ gives $a_0 \le 1$ so the values form an
initial segment and $2C(n+1) \ge a_n(a_n + 1)$ grows quadratically, giving the Brown condition
directly. If a jump $a_{n_0 + 1} \ge a_{n_0} + 2$ occurs (Phase 2), it forces
$t\alpha^{n_0}(\alpha - 1) > 1$, hence $t\alpha^{n_0} > 2$ (as $\alpha - 1 < 1/2$ from
$\alpha < 3/2$), hence $a_{n_0} \ge 2$; the Phase 1 quadratic stock then starts the linear
invariant $a_n + 1 \le 2C(n)$, which is self-propagating (all terms distinct past $n_0$, so
$C(n+1) = a_n + C(n)$) and carries the Brown condition forward:
$2a_{n+1} \le 3a_n + 2 < 2(1 + C(n+1))$.

A **partial result** on the open Erdős Problem 349 and on the named open conjecture
`complete_for_alpha_in_Ioo_one_to_goldenRatio` (restricted to $\alpha < 3/2$): this is the new
mathematical content behind `isGoodPair_of_pos_of_lt_two` below.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/0ed837c90387a146fc88a23172074d01533f94ee/FormalConjectures/ErdosProblems/349.lean#L1244"]
theorem floorSeq_brown_all (t α : ℝ) (ht : 0 < t) (ht2 : t < 2) (hα1 : 1 < α) (hα2 : α < 3 / 2) :
    ∀ n : ℕ, ⌊t * α ^ n⌋ ≤ 1 + C (fun m : ℕ => ⌊t * α ^ m⌋) n := by
  sorry

/-- **Erdős Problem 349, eventual completeness for $0 < t < 2$ on the strip $1 < \alpha < 3/2$.**

The pair $(t, \alpha)$ is good, i.e. $\lfloor t\alpha^n\rfloor$ is additively complete in the
**eventual** sense. Instantiates `eventuallyComplete_of_brown_of_base_window` with the explicit
base window $N_0 = 0$, $L = 0$: `hbase` is trivial ($C\ a\ 0 = 0$, so the only admissible $k$ is
$0 = \sum_{i \in \emptyset} i$) and `hbrown` is `floorSeq_brown_all`.

This closes the sub-case $0 < t < 1$ left out of scope by `isGoodPair_of_one_le_lt_two` /
`entirelyComplete_floorSeq_iff_lt_two` above (which need $1 \le t$): for $0 < t < 1$,
$a_0 = \lfloor t\rfloor = 0$ and the sequence begins with a prefix of zeros, so *entire*
completeness is not even the right notion there — only *eventual* completeness, which is exactly
`IsGoodPair`. Together with `isGoodPair_of_one_le_lt_two` this gives eventual completeness for
**all** $0 < t < 2$ on the strip, strictly beyond the *entire*-completeness threshold $t < 2$
proved there: e.g. $(t, \alpha) = (7/4, 7/5)$ has $t\alpha = 2.45 > 2$, outside van Doorn's
"easy" $t\alpha < 2$ range, yet is covered here.

A **partial result** on the open Erdős Problem 349 and on the named open conjecture
`complete_for_alpha_in_Ioo_one_to_goldenRatio` (restricted to $\alpha < 3/2$, eventual sense,
$t < 2$); nothing is claimed for $t \ge 2$ on this route, and no "only if" direction is claimed.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline (it depends on two linked theorems). -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/0ed837c90387a146fc88a23172074d01533f94ee/FormalConjectures/ErdosProblems/349.lean#L1436"]
theorem isGoodPair_of_pos_of_lt_two (t α : ℝ) (ht : 0 < t) (ht2 : t < 2)
    (hα1 : 1 < α) (hα2 : α < 3 / 2) : IsGoodPair t α := by
  sorry

/-- **Erdős Problem 349, eventual completeness for $0 < t < 1$ on the strip $1 < \alpha < 3/2$.**

Corollary of `isGoodPair_of_pos_of_lt_two`, specialized to $t < 1$: the sub-case left entirely out
of scope by the *entire*-completeness results above (`isGoodPair_of_one_le_lt_two`,
`entirelyComplete_floorSeq_iff_lt_two`), which all require $1 \le t$. A **partial result** on the
open Erdős Problem 349 and on `complete_for_alpha_in_Ioo_one_to_goldenRatio` (restricted to
$\alpha < 3/2$, eventual sense, $t < 1$).

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it depends
on a linked theorem. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/0ed837c90387a146fc88a23172074d01533f94ee/FormalConjectures/ErdosProblems/349.lean#L1460"]
theorem isGoodPair_of_pos_of_lt_one (t α : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hα1 : 1 < α) (hα2 : α < 3 / 2) : IsGoodPair t α := by
  sorry

end Erdos349
