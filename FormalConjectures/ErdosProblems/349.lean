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

/- ## Good pairs deep in the open zone `1 < α < 3/2` for `t ≥ 2`

The results below extend the partial characterization of Erdős Problem 349 with 21 concrete good
pairs $(t, \alpha)$ satisfying $t \ge 2$, reaching well beyond the strip $\alpha \le 1 +
1/(2\lfloor t\rfloor + 2)$ already covered by `isGoodPair_of_pos_of_lt_two` above (which only
handles $t < 2$).

The engine is a **reduction theorem**, `isGoodPair_of_run`: the whole (still open) band $t \ge
2$, $1 < \alpha < 3/2$ collapses to a single finite combinatorial certificate — a rank $N_0$ at
which the floor sequence produces a *new* value whose predecessors' subset sums already cover a
run of length $\ge a_{N_0}$. It is proved by adding a *deficit* parameter to the base-window
engine `eventuallyComplete_of_brown_of_base_window` above (letting the covered window sit
strictly inside $[L, C\ a\ N_0]$ instead of filling it exactly), then instantiated below with 21
explicit finite certificates, each kernel-checked by `decide` on concrete `Finset ℤ` literals.

**Why this does not close the band.** The reduction does not narrow the band itself: at its
$\alpha \to 3/2^-$ endpoint, the arithmetic core of the (RUN) certificate — the existence of a
$t$ making every $\lfloor t\alpha^n\rfloor$ share a nontrivial common structure forever — is
literally Mahler's $3/2$ problem (non-existence of "$Z$-numbers"), open since 1968. What *is*
proved here is that the band can be filled **arbitrarily close to $3/2$, point by point**: the
barrier obstructs only the universal statement over the whole band, not any single concrete
pair. -/

/-- **Subset-sum witness constructor.** If $B \subseteq A$ (as finite sets of integers) and
$k = \sum_{i \in B} i$, then $k$ is a subset sum of $A$. A trivial repackaging of the definition
of `subsetSums`, used throughout the finite window certificates below. Textbook-level. -/
@[category textbook, AMS 11]
theorem mem_subsetSums_of_subset {A B : Finset ℤ} (hsub : B ⊆ A) {k : ℤ}
    (hk : k = ∑ i ∈ B, i) : k ∈ subsetSums ((A : Finset ℤ) : Set ℤ) :=
  ⟨B, by exact_mod_cast Finset.coe_subset.mpr hsub, hk⟩

/-- **Eventual-completeness engine with an interior deficit window.** Generalizes
`eventuallyComplete_of_brown_of_base_window` above by letting the covered base window sit
*strictly inside* $[L, C\ a\ N_0]$, at distance $D$ from its right end. Let $a : \mathbb{N} \to
\mathbb{Z}$ be nonnegative, monotone and unbounded, and suppose there are $N_0 : \mathbb{N}$ and
$L, D \in \mathbb{Z}$ such that: (i) *interior base window* — every $k$ with $L \le k \le C\ a\
N_0 - D$ is already a subset sum of $\{a_0, \ldots, a_{N_0-1}\}$; (ii) *shifted Brown margin* —
$a_n + L + D \le 1 + C\ a\ n$ for every $n \ge N_0$. Then $\operatorname{range} a$ is additively
complete in the eventual sense.

Taking $D = 0$ recovers `eventuallyComplete_of_brown_of_base_window` exactly. The deficit $D$ is
what lets `isGoodPair_of_run` below reduce goodness to a *finite* certificate: taking
$D := C\ a\ N_0 - U$ for an explicit run $[L, U]$ collapses (i) to the run hypothesis and the base
case of (ii) to a single arithmetic inequality on $a_{N_0}$.

Textbook-level: a purely combinatorial merge-induction on monotone integer sequences (no $t,
\alpha$), directly analogous to `eventuallyComplete_of_brown_of_base_window`; the research content
of Erdős Problem 349 is in `isGoodPair_of_run` below.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L682"]
theorem eventuallyComplete_of_brown_of_deficit_window (a : ℕ → ℤ)
    (hnn : ∀ n, 0 ≤ a n)
    (hmono : Monotone a)
    (hub : ∀ M : ℤ, ∃ n, M ≤ a n)
    (N₀ : ℕ) (L D : ℤ)
    (hbase : ∀ k : ℤ, L ≤ k → k ≤ C a N₀ - D →
      k ∈ subsetSums (((Finset.range N₀).image a : Finset ℤ) : Set ℤ))
    (hbrown : ∀ n : ℕ, N₀ ≤ n → a n + L + D ≤ 1 + C a n) :
    IsAddComplete (Set.range a) := by
  sorry

/-- **Shifted Brown margin propagates from a doubling bound.** For a monotone sequence $a$
satisfying the doubling bound $a_{n+1} \le 2 a_n$, if $a_{N_0}$ is a new value (not among $a_0,
\ldots, a_{N_0-1}$) and the base inequality $a_{N_0} + L + D \le 1 + C\ a\ N_0$ holds, then the
shifted margin $a_n + L + D \le 1 + C\ a\ n$ propagates to every $n \ge N_0$.

Textbook-level: a purely combinatorial induction on monotone integer sequences (no $t, \alpha$);
its instantiation `floorSeq_brown_shifted` below (for $a_n = \lfloor t\alpha^n\rfloor$) supplies
hypothesis (ii) of `eventuallyComplete_of_brown_of_deficit_window` for `isGoodPair_of_run`.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L768"]
theorem brown_shifted_of_doubling (a : ℕ → ℤ) (L D : ℤ) (N₀ : ℕ)
    (hmono : Monotone a)
    (hdouble : ∀ n, a (n + 1) ≤ 2 * a n)
    (hnew : a N₀ ∉ (Finset.range N₀).image a)
    (hbase : a N₀ + L + D ≤ 1 + C a N₀) :
    ∀ n : ℕ, N₀ ≤ n → a n + L + D ≤ 1 + C a n := by
  sorry

/-- **Shifted Brown margin for the floor sequence.** Instance of `brown_shifted_of_doubling` for
$a_n = \lfloor t\alpha^n\rfloor$, whose doubling bound is `floor_mul_pow_succ_le_two_mul` above
(valid for $1 \le t$, $1 < \alpha < 3/2$). A building block for `isGoodPair_of_run` below.
Textbook-level. -/
@[category textbook, AMS 11]
theorem floorSeq_brown_shifted (t α : ℝ) (L D : ℤ) (N₀ : ℕ)
    (ht : 1 ≤ t) (hα1 : 1 < α) (hα2 : α < 3 / 2)
    (hnew : ⌊t * α ^ N₀⌋ ∉ (Finset.range N₀).image (fun n : ℕ => ⌊t * α ^ n⌋))
    (hbase : ⌊t * α ^ N₀⌋ + L + D ≤ 1 + C (fun n : ℕ => ⌊t * α ^ n⌋) N₀) :
    ∀ n : ℕ, N₀ ≤ n →
      ⌊t * α ^ n⌋ + L + D ≤ 1 + C (fun n : ℕ => ⌊t * α ^ n⌋) n :=
  brown_shifted_of_doubling (fun n : ℕ => ⌊t * α ^ n⌋) L D N₀
    (floorSeq_monotone t α (by linarith) hα1.le)
    (fun n => floor_mul_pow_succ_le_two_mul t α hα1 hα2 ht n)
    hnew hbase

/-- **The Reduction Theorem for Erdős Problem 349, `t ≥ 2` regime.** Let $t, \alpha \in
\mathbb{R}$ with $1 \le t$, $1 < \alpha < 3/2$, and write $a_n = \lfloor t\alpha^n\rfloor$. If
there are $N_0 \in \mathbb{N}$ and $L, U \in \mathbb{Z}$ such that

* $a_{N_0}$ is a *new* value (not among $a_0, \ldots, a_{N_0-1}$);
* every integer of $[L, U]$ is a subset sum of $\{a_0, \ldots, a_{N_0-1}\}$;
* $a_{N_0} \le U - L + 1$ (the run already covered is at least as long as the next term needs),

then $(t, \alpha)$ is a good pair.

This is the honest permanent statement of what remains open about the band $t \ge 2$, $1 < \alpha
< 3/2$: it is *exactly* the collection of pairs admitting such a run certificate, and no
soft/metric criterion can imply the certificate in general — its arithmetic core at $\alpha \to
3/2^-$ is Mahler's $3/2$ problem, open since 1968. Instantiated below for 21 explicit pairs, never
asserted for a whole region.

Proof: instantiate `eventuallyComplete_of_brown_of_deficit_window` with $a_n = \lfloor
t\alpha^n\rfloor$ and deficit $D := C\ a\ N_0 - U$; then $C\ a\ N_0 - D = U$, the interior base
window collapses to exactly the run hypothesis, and the base case of the shifted Brown margin
(`floorSeq_brown_shifted`) collapses to exactly $a_{N_0} \le U - L + 1$.

A **partial result** on the open Erdős Problem 349, in the same family as
`isGoodPair_of_pos_of_lt_two` above but for the $t \ge 2$ regime that theorem does not cover.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L846"]
theorem isGoodPair_of_run (t α : ℝ) (ht : 1 ≤ t) (hα1 : 1 < α) (hα2 : α < 3 / 2)
    (N₀ : ℕ) (L U : ℤ)
    (hnew : ⌊t * α ^ N₀⌋ ∉ (Finset.range N₀).image (fun n : ℕ => ⌊t * α ^ n⌋))
    (hrun : ∀ k : ℤ, L ≤ k → k ≤ U →
      k ∈ subsetSums (((Finset.range N₀).image (fun n : ℕ => ⌊t * α ^ n⌋) : Finset ℤ) : Set ℤ))
    (hfit : ⌊t * α ^ N₀⌋ ≤ U - L + 1) :
    IsGoodPair t α := by
  sorry

/-- Every integer of $[2, 7]$ is a subset sum of $\{2, 3, 4\}$ (6 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11]
theorem window_two_four : ∀ k : ℤ, 2 ≤ k → k ≤ 7 →
    k ∈ subsetSums ((({2, 3, 4} : Finset ℤ)) : Set ℤ) := by
  intro k hk1 hk2
  have h : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_subsetSums_of_subset (B := {2}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 3}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 4}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4}) (by decide) (by decide)

/-- Every integer of $[7, 21]$ is a subset sum of $\{3, 4, 5, 7, 9\}$ (15 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L881"]
theorem window_three_nine : ∀ k : ℤ, 7 ≤ k → k ≤ 21 →
    k ∈ subsetSums ((({3, 4, 5, 7, 9} : Finset ℤ)) : Set ℤ) := by
  sorry

/-- Every integer of $[8, 49]$ is a subset sum of $\{2, 4, 6, 9, 14, 22\}$ (42 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L906"]
theorem window_W1 : ∀ k : ℤ, 8 ≤ k → k ≤ 49 →
    k ∈ subsetSums ((({2, 4, 6, 9, 14, 22} : Finset ℤ)) : Set ℤ) := by
  sorry

/-- Every integer of $[14, 79]$ is a subset sum of $\{2, 4, 6, 10, 15, 22, 34\}$ (66 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L956"]
theorem window_W2 : ∀ k : ℤ, 14 ≤ k → k ≤ 79 →
    k ∈ subsetSums ((({2, 4, 6, 10, 15, 22, 34} : Finset ℤ)) : Set ℤ) := by
  sorry

/-- Every integer of $[23, 77]$ is a subset sum of $\{2, 3, 5, 7, 11, 16, 23, 33\}$ (55 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L1030"]
theorem window_W3 : ∀ k : ℤ, 23 ≤ k → k ≤ 77 →
    k ∈ subsetSums ((({2, 3, 5, 7, 11, 16, 23, 33} : Finset ℤ)) : Set ℤ) := by
  sorry

/-- Every integer of $[25, 93]$ is a subset sum of $\{2, 3, 5, 8, 12, 18, 28, 42\}$ (69 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L1093"]
theorem window_W4 : ∀ k : ℤ, 25 ≤ k → k ≤ 93 →
    k ∈ subsetSums ((({2, 3, 5, 8, 12, 18, 28, 42} : Finset ℤ)) : Set ℤ) := by
  sorry

/-- Every integer of $[12, 45]$ is a subset sum of $\{3, 4, 6, 9, 14, 21\}$ (34 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L1170"]
theorem window_W5 : ∀ k : ℤ, 12 ≤ k → k ≤ 45 →
    k ∈ subsetSums ((({3, 4, 6, 9, 14, 21} : Finset ℤ)) : Set ℤ) := by
  sorry

/-- Every integer of $[34, 111]$ is a subset sum of $\{3, 4, 6, 10, 15, 22, 34, 51\}$ (78 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L1212"]
theorem window_W6 : ∀ k : ℤ, 34 ≤ k → k ≤ 111 →
    k ∈ subsetSums ((({3, 4, 6, 10, 15, 22, 34, 51} : Finset ℤ)) : Set ℤ) := by
  sorry

/-- Every integer of $[31, 120]$ is a subset sum of $\{4, 5, 8, 11, 16, 24, 34, 49\}$ (90 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L1298"]
theorem window_W7 : ∀ k : ℤ, 31 ≤ k → k ≤ 120 →
    k ∈ subsetSums ((({4, 5, 8, 11, 16, 24, 34, 49} : Finset ℤ)) : Set ℤ) := by
  sorry

/-- Every integer of $[47, 146]$ is a subset sum of $\{5, 7, 10, 14, 21, 30, 43, 63\}$ (100 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L1396"]
theorem window_W8 : ∀ k : ℤ, 47 ≤ k → k ≤ 146 →
    k ∈ subsetSums ((({5, 7, 10, 14, 21, 30, 43, 63} : Finset ℤ)) : Set ℤ) := by
  sorry

/-- Every integer of $[42, 117]$ is a subset sum of $\{7, 9, 13, 18, 26, 36, 50\}$ (76 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L1504"]
theorem window_W9 : ∀ k : ℤ, 42 ≤ k → k ≤ 117 →
    k ∈ subsetSums ((({7, 9, 13, 18, 26, 36, 50} : Finset ℤ)) : Set ℤ) := by
  sorry

/-- Every integer of $[69, 136]$ is a subset sum of $\{10, 12, 15, 20, 25, 32, 40, 51\}$ (68 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L1588"]
theorem window_W10 : ∀ k : ℤ, 69 ≤ k → k ≤ 136 →
    k ∈ subsetSums ((({10, 12, 15, 20, 25, 32, 40, 51} : Finset ℤ)) : Set ℤ) := by
  sorry

/-- **First good pair strictly outside the near-one strip.** $(5/2, 7/5)$ is a good pair:
$N_0 = 3$, the floor sequence gives the distinct values $\{2, 3, 4\}$, then $a_3 = 6$ exactly
fits the run $[2, 7]$ (`window_two_four`). Since $\lfloor 5/2\rfloor = 2$, the strip
`isGoodPair_of_pos_of_lt_two` only reaches $\alpha \le 1 + 1/(2\cdot 2+2) = 7/6 \approx 1.167$;
here $\alpha = 7/5 = 1.4$ is $70\%$ of the way across the open interval $(7/6, 3/2)$. Instance of
`isGoodPair_of_run`. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L1669"]
theorem isGoodPair_five_halves_seven_fifths : IsGoodPair (5 / 2 : ℝ) (7 / 5 : ℝ) := by
  sorry

/-- **Reaching $\alpha = 1.4999$, deep toward the $3/2$ endpoint (headline, $t = 2$).**
$(2, 14999/10000)$ is a good pair: $N_0 = 8$, distinct values
$\{2, 4, 6, 10, 15, 22, 34\}$, then $a_8 = 51$ fits the run $[14, 79]$ (`window_W2`). Instance of
`isGoodPair_of_run`, showing the band can be filled arbitrarily close to $3/2$ point by point even
though the full band $t \ge 2$, $1 < \alpha < 3/2$ remains open. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L1689"]
theorem isGoodPair_two_alpha_1_4999 : IsGoodPair (2 : ℝ) (14999 / 10000 : ℝ) := by
  sorry

/-- **Reaching $\alpha = 1.4999$, deep toward the $3/2$ endpoint (headline, $t = 5/2$).**
$(5/2, 14999/10000)$ is a good pair: $N_0 = 8$, distinct values
$\{2, 3, 5, 8, 12, 18, 28, 42\}$, then $a_8 = 64$ fits the run $[25, 93]$ (`window_W4`). Instance
of `isGoodPair_of_run`; see `isGoodPair_two_alpha_1_4999` for the significance of this frontier. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L1713"]
theorem isGoodPair_five_halves_alpha_1_4999 : IsGoodPair (5 / 2 : ℝ) (14999 / 10000 : ℝ) := by
  sorry

/-- **Reaching $\alpha = 1.4999$, deep toward the $3/2$ endpoint (headline, $t = 3$).**
$(3, 14999/10000)$ is a good pair: $N_0 = 8$, distinct values
$\{3, 4, 6, 10, 15, 22, 34, 51\}$, then $a_8 = 76$ fits the run $[34, 111]$ (`window_W6`). Instance
of `isGoodPair_of_run`; see `isGoodPair_two_alpha_1_4999` for the significance of this frontier. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L1737"]
theorem isGoodPair_three_alpha_1_4999 : IsGoodPair (3 : ℝ) (14999 / 10000 : ℝ) := by
  sorry

/-- **Seventeen further good pairs, same reduction, compactly bundled.** All instantiate
`isGoodPair_of_run` exactly like the four headline results above (explicit floor values up to a
new rank $N_0$, matched against a finite window certificate); bundled into one statement so the
family is reviewed as a single declaration rather than seventeen near-identical ones. In the order
listed: $t = 5/2$ at $\alpha = 4/3$; $t = 2$ at $\alpha \in \{4/3, 5/4, 112/75, 299/200,
1499/1000\}$; $t = 5/2$ at $\alpha \in \{29/20, 449/300\}$; $t = 3$ at $\alpha \in \{4/3, 5/4,
37/25, 89/60, 1499/1000\}$; $t = 4$ at $\alpha = 76/53$; $t = 5$ at $\alpha = 79/55$; $t = 7$ at
$\alpha = 71/51$; $t = 10$ at $\alpha = 43/34$. Together with the four headline pairs, this gives
**21 good pairs total** with $t \in \{2, 5/2, 3, 4, 5, 7, 10\}$ and $\alpha$ ranging from $5/4$ up
to $14999/10000$, all strictly outside the strip $\alpha \le 1 + 1/(2\lfloor t\rfloor+2)$ covered
by `isGoodPair_of_pos_of_lt_two`.

A **partial result** on the open Erdős Problem 349: these are 17 more explicit instances of
`isGoodPair_of_run`, never a claim about a whole region. The full band $t \ge 2$, $1 < \alpha <
3/2$ remains open.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/ed8779b1a3cc906098b201569aa14c1f3b7a2993/FormalConjectures/ErdosProblems/349.lean#L1775"]
theorem isGoodPair_run_further_instances :
    IsGoodPair (5 / 2 : ℝ) (4 / 3 : ℝ) ∧
    IsGoodPair (2 : ℝ) (4 / 3 : ℝ) ∧
    IsGoodPair (2 : ℝ) (5 / 4 : ℝ) ∧
    IsGoodPair (3 : ℝ) (4 / 3 : ℝ) ∧
    IsGoodPair (3 : ℝ) (5 / 4 : ℝ) ∧
    IsGoodPair (2 : ℝ) (112 / 75 : ℝ) ∧
    IsGoodPair (2 : ℝ) (299 / 200 : ℝ) ∧
    IsGoodPair (2 : ℝ) (1499 / 1000 : ℝ) ∧
    IsGoodPair (5 / 2 : ℝ) (29 / 20 : ℝ) ∧
    IsGoodPair (5 / 2 : ℝ) (449 / 300 : ℝ) ∧
    IsGoodPair (3 : ℝ) (37 / 25 : ℝ) ∧
    IsGoodPair (3 : ℝ) (89 / 60 : ℝ) ∧
    IsGoodPair (3 : ℝ) (1499 / 1000 : ℝ) ∧
    IsGoodPair (4 : ℝ) (76 / 53 : ℝ) ∧
    IsGoodPair (5 : ℝ) (79 / 55 : ℝ) ∧
    IsGoodPair (7 : ℝ) (71 / 51 : ℝ) ∧
    IsGoodPair (10 : ℝ) (43 / 34 : ℝ) := by
  sorry

/- ## The block-run lemma: from 21 pointwise certificates to an infinite family

`isGoodPair_of_run` above reduces goodness of a single pair $(t, \alpha)$ to a *finite*
combinatorial certificate at one rank $N_0$. It was instantiated 21 times above, each time by
hand-picking a concrete finite window (`window_two_four`, `window_W1`, ..., `window_W10`) for one
specific pair. The lemma below, `interval_block_run`, produces such a certificate **uniformly**,
for every block $[m, M]$ of consecutive integers with $m \ge 2$ and $M \ge 2m$ — turning the
21 isolated points into the whole near-one sub-band $1 < \alpha \le 1 + 1/(2\lfloor t\rfloor + 2)$
of the band $t \ge 2$, $1 < \alpha < 3/2$, for **every** $t \ge 2$ at once
(`isGoodPair_of_two_le` below).

This does not close the open band itself: at $\alpha \to (3/2)^-$ the arithmetic core of a
run certificate is Mahler's $3/2$ problem (open since 1968), so no uniform argument can reach the
whole band this way — only, as here, closer and closer sub-bands as $\alpha \to (3/2)^-$ point by
point (already witnessed above by `isGoodPair_two_alpha_1_4999` etc.), or, as here, a full
neighbourhood of $\alpha = 1$ whose width shrinks like $1/(2t)$ as $t \to \infty$. -/

/-- **The merge fact.** If every integer of the window $[L, U]$ is a subset sum of the finite set
$S$, and $v \notin S$ is at most one more than the window's width ($v \le U - L + 1$), then every
integer of the widened window $[L, U + v]$ is a subset sum of $S \cup \{v\}$.

For $k \le U$ reuse the old witness; for $k > U$ the shifted point $k - v$ lands back in
$[L, U]$ (using $v \le U - L + 1$), and adjoining $v$ to its witness gives the sum $v + (k-v) = k$.
A textbook-level fact about `subsetSums`, the combinatorial core of `interval_block_run` below. -/
@[category textbook, AMS 11]
theorem merge_fact (L U : ℤ) (S : Finset ℤ) (v : ℤ)
    (hLU : ∀ k : ℤ, L ≤ k → k ≤ U → k ∈ subsetSums (S : Set ℤ))
    (hvS : v ∉ S) (hv : v ≤ U - L + 1) :
    ∀ k : ℤ, L ≤ k → k ≤ U + v → k ∈ subsetSums ((insert v S : Finset ℤ) : Set ℤ) := by
  intro k hk₁ hk₂
  by_cases hkU : k ≤ U
  · obtain ⟨B, hB₁, hB₂⟩ := hLU k hk₁ hkU
    refine ⟨B, hB₁.trans ?_, hB₂⟩
    rw [Finset.coe_insert]
    exact Set.subset_insert v _
  · obtain ⟨B, hB₁, hB₂⟩ := hLU (k - v) (by omega) (by omega)
    have hvB : v ∉ B := fun hmem => hvS (by simpa using hB₁ (Finset.mem_coe.mpr hmem))
    refine ⟨insert v B, ?_, ?_⟩
    · rw [Finset.coe_insert, Finset.coe_insert]
      exact Set.insert_subset_insert hB₁
    · rw [Finset.sum_insert hvB, ← hB₂]; ring

/-- **Block-run lemma.** For integers $m, M$ with $2 \le m$ and $2m \le M$, put $M_1 := \lfloor
M/2\rfloor$ and $S_1 := \sum_{v \in [m, M_1]} v$. Then every integer of the interval
$[M_1 + 1,\ M + S_1]$ is a finite subset sum of the *distinct* integers $m, m+1, \ldots, M$.

Proved by the downward invariant $P(p) : [M_1+1,\, M + \sum_{v \in [p, M_1]} v] \subseteq
\operatorname{subsetSums}[p, M]$ for $m \le p \le M_1 + 1$, with base $P(M_1+1)$ the singleton
interval $[M_1+1, M]$ and step $P(p+1) \to P(p)$ merging the new value $v := p$ via `merge_fact`
(realised as an upward `Nat` induction on $M_1 + 1 - p$).

This is the genuinely new combinatorial content behind `isGoodPair_of_two_le` below: it supplies
`isGoodPair_of_run`'s finite certificate simultaneously for every admissible $(m, M)$, rather than
one hand-picked window per pair as in the 21 instances above.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/9cdf79b3fb41bf4535fc153b77d5580786a5b8f8/FormalConjectures/ErdosProblems/349.lean#L2122"]
theorem interval_block_run (m M : ℤ) (hm : 2 ≤ m) (hM : 2 * m ≤ M) :
    ∀ k : ℤ, M / 2 + 1 ≤ k → k ≤ M + ∑ v ∈ Finset.Icc m (M / 2), v →
      k ∈ subsetSums ((Finset.Icc m M : Finset ℤ) : Set ℤ) := by
  sorry

/-- The near-one hypothesis $\alpha \le 1 + 1/M$, cleared of denominators: $M(\alpha - 1) \le 1$.
A textbook-level algebraic rewriting, a building block for the near-one strip lemmas below. -/
@[category textbook, AMS 11]
theorem mul_sub_one_le_one_of_near_one (α : ℝ) (M : ℤ) (hM : 1 ≤ M)
    (hα : α ≤ 1 + 1 / (M : ℝ)) : (M : ℝ) * (α - 1) ≤ 1 := by
  have hMR : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM
  have h := mul_le_mul_of_nonneg_left (by linarith : α - 1 ≤ 1 / (M : ℝ)) hMR.le
  rwa [mul_one_div, div_self (ne_of_gt hMR)] at h

/-- **Contiguity step.** On the near-one strip $1 < \alpha \le 1 + 1/M$, as long as the floor
sequence $a_n = \lfloor t\alpha^n\rfloor$ stays at most $M - 1$ it can increase by at most $1$
at the next step: $a_n \le M - 1$ gives $t\alpha^n < M$, hence $t\alpha^{n+1} = t\alpha^n +
t\alpha^n(\alpha - 1) < t\alpha^n + M(\alpha - 1) \le t\alpha^n + 1 < a_n + 2$. A building block
for `floorSeq_covers_Icc` below. -/
@[category textbook, AMS 11]
theorem floorSeq_succ_le_succ_of_lt (t α : ℝ) (M : ℤ) (n : ℕ)
    (ht : 0 ≤ t) (hM : 1 ≤ M) (hα1 : 1 < α) (hα : α ≤ 1 + 1 / (M : ℝ))
    (h : ⌊t * α ^ n⌋ ≤ M - 1) :
    ⌊t * α ^ (n + 1)⌋ ≤ ⌊t * α ^ n⌋ + 1 := by
  have hα0 : (0:ℝ) < α := by linarith
  have hx0 : (0:ℝ) ≤ t * α ^ n := mul_nonneg ht (pow_nonneg hα0.le n)
  have hxM : t * α ^ n < (M : ℝ) := Int.floor_lt.mp (by omega)
  have hMa := mul_sub_one_le_one_of_near_one α M hM hα
  have hkey : (t * α ^ n) * (α - 1) < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hxM) (sub_pos.mpr hα1)]
  have hfl : t * α ^ n < (⌊t * α ^ n⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hlt : t * α ^ (n + 1) < ((⌊t * α ^ n⌋ + 2 : ℤ) : ℝ) := by
    have hsucc : t * α ^ (n + 1) = t * α ^ n + (t * α ^ n) * (α - 1) := by ring
    push_cast
    rw [hsucc]
    linarith
  have := Int.floor_lt.mpr hlt
  omega

/-- **The term just past a cut.** On the near-one strip, one step after a term that is at most
$M$ the sequence is at most $M + 2$: $a_n \le M$ gives $t\alpha^n < M+1$, hence $t\alpha^{n+1} <
(M+1) + (M(\alpha-1) + (\alpha - 1)) \le (M+1) + 2 = M+3$. A building block for
`isGoodPair_of_two_le_of_window` below. -/
@[category textbook, AMS 11]
theorem floorSeq_le_add_two_at_cut (t α : ℝ) (M : ℤ) (n : ℕ)
    (ht : 0 ≤ t) (hM : 1 ≤ M) (hα1 : 1 < α) (hα : α ≤ 1 + 1 / (M : ℝ))
    (h : ⌊t * α ^ n⌋ ≤ M) :
    ⌊t * α ^ (n + 1)⌋ ≤ M + 2 := by
  have hα0 : (0:ℝ) < α := by linarith
  have hMR : (1:ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hx0 : (0:ℝ) ≤ t * α ^ n := mul_nonneg ht (pow_nonneg hα0.le n)
  have hxM : t * α ^ n < (M : ℝ) + 1 := by
    have : t * α ^ n < ((M + 1 : ℤ) : ℝ) := Int.floor_lt.mp (by omega)
    push_cast at this; linarith
  have hMa := mul_sub_one_le_one_of_near_one α M hM hα
  have hsmall : α - 1 ≤ 1 := by nlinarith
  have hkey : (t * α ^ n) * (α - 1) < 2 := by
    nlinarith [mul_pos (sub_pos.mpr hxM) (sub_pos.mpr hα1)]
  have hlt : t * α ^ (n + 1) < ((M + 3 : ℤ) : ℝ) := by
    have hsucc : t * α ^ (n + 1) = t * α ^ n + (t * α ^ n) * (α - 1) := by ring
    push_cast
    rw [hsucc]
    linarith
  have := Int.floor_lt.mpr hlt
  omega

/-- **The block is swept (discrete IVT).** On the near-one strip $1 < \alpha \le 1 + 1/M$, every
integer $v$ of the block $[\lfloor t\rfloor, M]$ is attained by the floor sequence. Take the
least $n$ with $v \le a_n$: if $n = 0$ then $v \le a_0 = \lfloor t\rfloor \le v$; otherwise
$n = k+1$ with $a_k \le v - 1 \le M - 1$, so `floorSeq_succ_le_succ_of_lt` gives $a_{k+1} \le
a_k + 1 \le v$, and minimality gives $v \le a_{k+1}$. A building block for
`floorSeq_image_range_cut` below. -/
@[category textbook, AMS 11]
theorem floorSeq_covers_Icc (t α : ℝ) (M : ℤ)
    (ht : 0 < t) (hM : 1 ≤ M) (hα1 : 1 < α) (hα : α ≤ 1 + 1 / (M : ℝ))
    (v : ℤ) (hv1 : ⌊t⌋ ≤ v) (hv2 : v ≤ M) :
    ∃ n : ℕ, ⌊t * α ^ n⌋ = v := by
  classical
  have hex : ∃ n : ℕ, v ≤ ⌊t * α ^ n⌋ := floorSeq_unbounded t α ht hα1 v
  obtain ⟨N, hN, hmin⟩ : ∃ N : ℕ, v ≤ ⌊t * α ^ N⌋ ∧ ∀ j, j < N → ⌊t * α ^ j⌋ < v :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => by have := Nat.find_min hex hj; omega⟩
  refine ⟨N, ?_⟩
  cases N with
  | zero =>
    rw [floorSeq_zero] at hN ⊢
    omega
  | succ k =>
    have hk : ⌊t * α ^ k⌋ < v := hmin k (Nat.lt_succ_self k)
    have hstep := floorSeq_succ_le_succ_of_lt t α M k ht.le hM hα1 hα (by omega)
    omega

/-- **The clean cut.** Let $N_0$ be the first rank at which the floor sequence exceeds $M$ (given
by its two defining properties, so that no `Nat.find` appears in the statement). Then the
distinct values produced before the cut are exactly the block $[\lfloor t\rfloor, M]$: $\subseteq$
is monotonicity plus minimality of $N_0$, and $\supseteq$ is `floorSeq_covers_Icc`. A building
block for `isGoodPair_of_two_le_of_window` below. -/
@[category textbook, AMS 11]
theorem floorSeq_image_range_cut (t α : ℝ) (M : ℤ)
    (ht : 0 < t) (hM : 1 ≤ M) (hα1 : 1 < α) (hα : α ≤ 1 + 1 / (M : ℝ))
    (N₀ : ℕ) (hN₀ : M < ⌊t * α ^ N₀⌋) (hN₀min : ∀ j, j < N₀ → ⌊t * α ^ j⌋ ≤ M) :
    (Finset.range N₀).image (fun n : ℕ => ⌊t * α ^ n⌋) = Finset.Icc ⌊t⌋ M := by
  have hmono := floorSeq_monotone t α ht.le hα1.le
  ext v
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨?_, hN₀min j hj⟩
    have h0 : ⌊t * α ^ (0 : ℕ)⌋ ≤ ⌊t * α ^ j⌋ := hmono (Nat.zero_le j)
    rw [floorSeq_zero] at h0
    exact h0
  · rintro ⟨hv1, hv2⟩
    obtain ⟨n, hn⟩ := floorSeq_covers_Icc t α M ht hM hα1 hα v hv1 hv2
    refine ⟨n, ?_, hn⟩
    by_contra hcon
    have hle : ⌊t * α ^ N₀⌋ ≤ ⌊t * α ^ n⌋ := hmono (by omega)
    omega

/-- **Erdős Problem 349, the near-one strip for all $t \ge 2$, modulo an explicit window.** For
$t \ge 2$, an integer $M \ge 2\lfloor t\rfloor + 2$ and $1 < \alpha \le 1 + 1/M$, the pair
$(t, \alpha)$ is good **as soon as** the central window $[M/2 + 1,\, M + \sum_{v \in [\lfloor
t\rfloor, M/2]} v]$ is covered by the subset sums of the block $[\lfloor t\rfloor, M]$.

Locates the cut rank $N_0$ (first index past $M$), identifies the pre-cut image with the block
$[\lfloor t\rfloor, M]$ (`floorSeq_image_range_cut`) and bounds the term just past the cut by
$M + 2$ (`floorSeq_le_add_two_at_cut`), then feeds `isGoodPair_of_run` above with $L = M/2+1$,
$U = M + \sum_{v \in [\lfloor t\rfloor, M/2]} v$: `hrun` is `hwin` transported along the image
identification, and `hfit` reduces to $M + 2 \le U - L + 1$, i.e. $\sum_{v \in [\lfloor t\rfloor,
M/2]} v \ge M/2 + 2$ — true because the two largest elements $M/2 - 1, M/2$ of that range alone
already sum to $\ge M/2 - 1 + M/2$ (using $\lfloor t\rfloor \le M/2 - 1$, from $M \ge
2\lfloor t\rfloor + 2$).

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/9cdf79b3fb41bf4535fc153b77d5580786a5b8f8/FormalConjectures/ErdosProblems/349.lean#L2293"]
theorem isGoodPair_of_two_le_of_window (t α : ℝ) (M : ℤ)
    (ht : 2 ≤ t) (hM : 2 * ⌊t⌋ + 2 ≤ M)
    (hα1 : 1 < α) (hα : α ≤ 1 + 1 / (M : ℝ))
    (hwin : ∀ k : ℤ, M / 2 + 1 ≤ k → k ≤ M + ∑ v ∈ Finset.Icc ⌊t⌋ (M / 2), v →
      k ∈ subsetSums ((Finset.Icc ⌊t⌋ M : Finset ℤ) : Set ℤ)) :
    IsGoodPair t α := by
  sorry

/-- **Erdős Problem 349, THE THEOREM for all $t \ge 2$, $M$-parametrised, unconditional.** For
every $t \ge 2$ and every integer $M \ge 2\lfloor t\rfloor + 2$, if $1 < \alpha \le 1 + 1/M$ then
$(t, \alpha)$ is good. Instantiates `isGoodPair_of_two_le_of_window` above with the block-run
lemma `interval_block_run`, which discharges its `hwin` hypothesis unconditionally. A **partial**
result on the open Erdős Problem 349: only *eventual* completeness is claimed, and only on the
strip $\alpha \le 1 + 1/M$; the full band $t \ge 2$, $1 < \alpha < 3/2$ remains open. -/
@[category research solved, AMS 11]
theorem isGoodPair_of_two_le_of_near_one (t α : ℝ) (M : ℤ)
    (ht : 2 ≤ t) (hM : 2 * ⌊t⌋ + 2 ≤ M)
    (hα1 : 1 < α) (hα : α ≤ 1 + 1 / (M : ℝ)) :
    IsGoodPair t α := by
  have hm2 : (2:ℤ) ≤ ⌊t⌋ := Int.le_floor.mpr (by exact_mod_cast ht)
  exact isGoodPair_of_two_le_of_window t α M ht hM hα1 hα
    (interval_block_run ⌊t⌋ M hm2 (by omega))

/-- **Erdős Problem 349, THE HEADLINE THEOREM: $(t, \alpha)$ is a good pair for all $t \ge 2$ and
$1 < \alpha \le 1 + \frac{1}{2\lfloor t\rfloor + 2}$.**

The instance $M = 2\lfloor t\rfloor + 2$ of `isGoodPair_of_two_le_of_near_one` above, the widest
strip this argument gives (at $t = 2$ the base inequality of `isGoodPair_of_two_le_of_window` is
tangent, with slack exactly $0$, so the constant $2\lfloor t\rfloor+2$ is not improvable by this
method).

A **partial result** on the open Erdős Problem 349, and on the named open conjecture
`complete_for_alpha_in_Ioo_one_to_goldenRatio`: it gives, for **every** $t \ge 2$, a
sub-strip of positive width around $\alpha = 1$ whose width $1/(2\lfloor t\rfloor+2)$ shrinks like
$1/(2t)$ as $t \to \infty$. Together with `isGoodPair_of_pos_of_lt_two` above ($0 < t < 2$), the
good region provably contains, for **every** $t > 0$, a strip of positive width around
$\alpha = 1$.

**What is NOT claimed:** the full band $t \ge 2$, $1 < \alpha < 3/2$ remains **open** — nothing
here extends outside the strip $\alpha \le 1 + 1/(2\lfloor t\rfloor+2)$ (see
`isGoodPair_two_alpha_1_4999` etc. above for pointwise progress deeper into that band); no
*entire* completeness is claimed (for $t \ge 2$, $1$ is never a subset sum, since every term is
$\ge \lfloor t\rfloor \ge 2$); and no converse ("only if") of any kind is stated. -/
@[category research solved, AMS 11]
theorem isGoodPair_of_two_le (t α : ℝ)
    (ht : 2 ≤ t) (hα1 : 1 < α) (hα : α ≤ 1 + 1 / ((2 * ⌊t⌋ + 2 : ℤ) : ℝ)) :
    IsGoodPair t α :=
  isGoodPair_of_two_le_of_near_one t α (2 * ⌊t⌋ + 2) ht le_rfl hα1 hα

/-- **Finite check: every integer of $[4, 11]$ is a subset sum of $\{2,3,4,5,6\}$.** Witnesses:
$4, 5, 6$ alone, $7 = 3+4$, $8 = 2+6$, $9 = 4+5$, $10 = 4+6$, $11 = 5+6$. The $m=2, M=6$ instance
of the block-run family, checked directly (no induction needed at this size) as a warm-up sanity
check for `isGoodPair_of_two_le` restricted to $2 \le t < 3$. -/
@[category textbook, AMS 11]
theorem window_two_six (k : ℤ) (hk1 : 4 ≤ k) (hk2 : k ≤ 11) :
    k ∈ subsetSums ((Finset.Icc (2 : ℤ) 6 : Finset ℤ) : Set ℤ) := by
  have hIcc : Finset.Icc (2 : ℤ) 6 = {2, 3, 4, 5, 6} := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
  rw [hIcc]
  have h : k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_subsetSums_of_subset (B := {4}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 6}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 5}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 6}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 6}) (by decide) (by decide)

/-- **Erdős Problem 349, the $2 \le t < 3$ warm-up, unconditional.** For $2 \le t < 3$ and
$1 < \alpha \le 7/6$, the pair $(t, \alpha)$ is good. The $2 \le t < 3$ instance of
`isGoodPair_of_two_le` above, reproved independently from the finite check `window_two_six`
rather than the general `interval_block_run`, as a sanity check that the general theorem
specializes correctly. A **partial result** on the open Erdős Problem 349. -/
@[category research solved, AMS 11]
theorem isGoodPair_of_two_le_lt_three_of_near_one (t α : ℝ)
    (ht : 2 ≤ t) (ht3 : t < 3) (hα1 : 1 < α) (hα : α ≤ 7 / 6) :
    IsGoodPair t α := by
  have hfl : ⌊t⌋ = 2 := by
    rw [Int.floor_eq_iff]
    refine ⟨by exact_mod_cast ht, ?_⟩
    push_cast; linarith
  have h62 : (6 : ℤ) / 2 = 3 := by norm_num
  have hsum : ∑ v ∈ Finset.Icc (2:ℤ) 3, v = 5 := by
    have h : Finset.Icc (2 : ℤ) 3 = {2, 3} := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    rw [h]; decide
  refine isGoodPair_of_two_le_of_window t α 6 ht (by omega) hα1 (by push_cast; linarith) ?_
  rw [hfl, h62, hsum]
  intro k hk1 hk2
  exact window_two_six k (by omega) (by omega)

/-- **Non-vacuity, inside the $2 \le t < 3$ warm-up.** $(t, \alpha) = (5/2, 9/8)$: $9/8 \le 7/6$.
-/
@[category test, AMS 11]
example : IsGoodPair (5 / 2 : ℝ) (9 / 8 : ℝ) :=
  isGoodPair_of_two_le_lt_three_of_near_one (5 / 2) (9 / 8) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- **Non-vacuity, strictly outside the $2 \le t < 3$ warm-up — the critical witness.**
$(t, \alpha) = (5, 13/12)$, with $t = 5 \ge 3$: the warm-up above does not apply, so this pair is
good only by the general theorem `isGoodPair_of_two_le`, i.e. only because `interval_block_run`
is proved for general blocks, not just $\{2,\ldots,6\}$. Bound check: $\lfloor 5\rfloor = 5$, so
$2\lfloor t\rfloor + 2 = 12$ and the strip bound is $1 + 1/12 = 13/12$; $\alpha = 13/12$ meets it
with **equality**, the extreme admissible value at $t = 5$. This shows `isGoodPair_of_two_le`
provably exceeds the $t < 3$ warm-up: it is not merely a repackaging of `window_two_six`. -/
@[category test, AMS 11]
example : IsGoodPair (5 : ℝ) (13 / 12 : ℝ) := by
  have hfl : ⌊(5 : ℝ)⌋ = 5 := by norm_num
  refine isGoodPair_of_two_le 5 (13 / 12) (by norm_num) (by norm_num) ?_
  rw [hfl]
  norm_num
end Erdos349
