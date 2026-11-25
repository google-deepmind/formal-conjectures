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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 124

*References:*
- [erdosproblems.com/124](https://www.erdosproblems.com/124)
- [BEGL96] Burr, S. A. and Erdős, P. and Graham, R. L. and Li, W. Wen-Ching, Complete sequences of sets of integer powers. Acta Arith. (1996), 133-138.
- [Fa26] Fan, S., *Strongly complete sets and a conjecture of Erdős* (2026).
  [arXiv:2607.14071](https://arxiv.org/abs/2607.14071)
- [Gr64] Graham, R. L., *Complete sequences of polynomial values*. Duke Math. J. (1964), 275-285.
- [Pa98] Park, S. K., *The r-complete partitions*. Discrete Math. (1998), 293-297.
-/

@[expose] public section

open Filter
open scoped Pointwise

namespace Erdos124

/-- The set of integers which are the sum of distinct powers `d ^ i` with `i ≥ k`. -/
def sumsOfDistinctPowers (d k : ℕ) : Set ℕ :=
  {x | ∃ s : Finset ℕ, (∀ i ∈ s, k ≤ i) ∧ ∑ i ∈ s, d ^ i = x}

/--
Let  $3 \le d_1 < d_2 < \dots < d_r$ be integers such that
$$\sum_{1 \le i \le r}\frac 1{d_i - 1} \ge 1.$$
Can all sufficiently large integers be written as a sum of the shape $\sum_i c_ia_i$
where $c_i \in \{0, 1\}$ and $a_i$ has only the digits $0, 1$ when written in base $d_i$?

Conjectured by Erdős [Er97], solved by Boris Alexeev using Aristotle.
-/
@[category research solved, question, AMS 11]
lemma erdos124.zero :
    ∀ D : Finset ℕ, (∀ d ∈ D, 3 ≤ d) → 1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹ →
      ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d 0 := sorry

/--
Let $k \ne 0$ and $3\leq d_1 < d_2 < \cdots < d_r$ be integers of gcd equal to $1$ such that
$$\sum_{1 \le i \le r}\frac 1{d_i - 1} \ge 1.$$
Can all sufficiently large integers be written as a sum of the shape $\sum_i c_ia_i$
where $c_i \in \{0, 1\}$ and $a_i$ is divisible by $d_i ^ k$ and has only the digits $0, 1$ when
written in base $d_i$?

Conjectured by Burr, Erdős, Graham, and Li [BEGL96]
-/
@[category research open, question, AMS 11]
lemma erdos124.ne_zero :
    ∀ k ≠ 0, ∀ D : Finset ℕ, (∀ d ∈ D, 3 ≤ d) → 1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹ → D.gcd id = 1 →
      ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d k := by
  sorry

/--
All sufficiently large integers can be written as $a + b + c$, where $a$, $b$, and $c$ are
divisible by $3$, $4$, and $7$ respectively, and after division by that base have only the
digits $0, 1$ in that base.

Proved by Burr, Erdős, Graham, and Li [BEGL96]
-/
@[category research solved, AMS 11]
lemma erdos124.ne_zero_three_four_seven :
    ∀ᶠ n in atTop,
      n ∈ sumsOfDistinctPowers 3 1 + sumsOfDistinctPowers 4 1 + sumsOfDistinctPowers 7 1 :=
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Let $D$ be a finite set of integers $\geq 3$, and write $D = C \sqcup E$, where $C$ is a nonempty
set of powers $h^a$ ($a \geq 1$) of one integer $h$ with
$$2\sum_{c \in C}\frac 1{c - 1} \ge 1, \qquad \sum_{d \in E}\frac 1{d - 1} > 1,$$
and some element of $E$ is coprime to $h$. Then for every $k \ne 0$ all sufficiently large
integers can be written as $\sum_{d \in D} a_d$, where $a_d$ is divisible by $d^k$ and has only
the digits $0, 1$ in base $d$.

The proof follows Graham's scheme [Gr64, Lemmas 4 and 5]: the powers $d^j$, $d \in E$,
$j \geq k$, have subset sums with bounded gaps, and finitely many disjoint pairs of sets $U_i, V_i$
with $\sum U_i - \sum V_i = 1$ fill the gaps. Each pair is built from one power $c^e \equiv 1
\pmod{h^K}$ of the coprime element $c$ and a signed representation of $(c^e - 1) / h^K$ by powers
of the elements of $C$, which exists because $2 \sum_{c \in C} 1/(c - 1) \geq 1$ [Pa98, Thm 2.2].
The new ingredient is that the gap bound $\sum_{d \in E} d^k / (d - 1)$ survives the deletion of
the powers $c^e$ used in the pairs, if they are taken at scales where every $d \in E$ has a power
close to $c^e$ (compare the sparse deletions in [Fa26, Cor. 6.3]).
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/mnn31/erdos-lean/blob/19a780c7f73c6a3de7f29c552f4c70209c135419/ErdosLean/Erdos124ThmAB.lean"]
lemma erdos124.variants.ne_zero_of_power_block :
    ∀ k ≠ 0, ∀ D C : Finset ℕ, ∀ h : ℕ, (∀ d ∈ D, 3 ≤ d) → C ⊆ D → C.Nonempty →
      (∀ x ∈ C, ∃ a ≥ 1, x = h ^ a) → 1 ≤ 2 * ∑ d ∈ C, (d - 1 : ℚ)⁻¹ →
      1 < ∑ d ∈ D \ C, (d - 1 : ℚ)⁻¹ → (∃ c ∈ D \ C, c.Coprime h) →
      ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d k := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Let $k \ne 0$ and let $D$ be a finite set of integers $\geq 3$ with $3 \in D$, $\gcd(D) = 1$ and
$$\sum_{d \in D}\frac 1{d - 1} > \frac 32.$$
Then all sufficiently large integers can be written as $\sum_{d \in D} a_d$, where $a_d$ is
divisible by $d^k$ and has only the digits $0, 1$ in base $d$.

This is the case $C = \{3\}$ of `erdos124.variants.ne_zero_of_power_block`: some element of
$D \setminus \{3\}$ is not divisible by $3$ since $\gcd(D) = 1$. For example
$D = \{3, 4, 5, 6, 7, 8\}$, with $\sum_{d \in D} 1/(d - 1) = 223/140 < 2$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/mnn31/erdos-lean/blob/19a780c7f73c6a3de7f29c552f4c70209c135419/ErdosLean/Erdos124ThmAB.lean"]
lemma erdos124.variants.ne_zero_of_three_mem :
    ∀ k ≠ 0, ∀ D : Finset ℕ, (∀ d ∈ D, 3 ≤ d) → 3 ∈ D → 3 / 2 < ∑ d ∈ D, (d - 1 : ℚ)⁻¹ →
      D.gcd id = 1 → ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d k := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Let $3\leq d_1 < d_2 < \cdots < d_r$ be integers such that all sufficiently large integers can be
written as a sum of the shape $\sum_i c_ia_i$ where $c_i \in \{0, 1\}$ and $a_i$ has only the digits
$0, 1$ when written in base $d_i$. Then
$$\sum_{1 \le i \le r}\frac 1{d_i - 1} \ge 1.$$

Reported by Burr, Erdős, Graham, and Li [BEGL96] as an observation of Pomerance
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/arex1337/formal-conjectures-proofs/blob/3b7d581c75fd00e482deabfb20675cf3ccfaf49f/Erdos124/Converse.lean"]
lemma erdos124.converse {D : Finset ℕ} (hD₃ : ∀ d ∈ D, 3 ≤ d)
    (h : ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d 0) : 1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹ :=
  sorry

/--
For any $\varepsilon > 0$, there exists an infinite sequence $2 \le d_0 < d_1 < \dots$ such
that the series $\sum_{i=0}^{\infty} \frac{1}{d_i - 1}$ converges to a value at most
$\varepsilon$, and yet for every $k \ne 0$ all sufficiently large integers can be written as
$\sum_{i \in I} a_i$ for some finite set $I$, where each $a_i$ is divisible by $d_i^k$ and has
only the digits $0, 1$ when written in base $d_i$.

The restriction $k \ne 0$ excludes the degenerate representation of $n$ as a sum of $n$ copies
of $1 = d_i^0$ taken from $n$ distinct bases.

Proved by Melfi [Me04, Proposition 1]
-/
@[category research solved, AMS 11]
lemma erdos124.melfi_construction {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n := by
  sorry

end Erdos124
