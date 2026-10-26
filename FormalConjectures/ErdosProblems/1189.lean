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
# Erdős Problem 1189

*References:*
- [erdosproblems.com/1189](https://www.erdosproblems.com/1189)
- [Er80] Erdős, P., *A survey of problems in combinatorial number theory*. Ann. Discrete Math. 6
  (1980), 89-115. [PDF](https://www.renyi.hu/~p_erdos/1980-03.pdf)
- [Si85] Simpson, R. J., *Regular coverings of the integers by arithmetic progressions*. Acta Arith.
  45 (1985), 145-152.
- [Su07] Sun, Z.-W., *On covering numbers*. Combinatorial Number Theory, de Gruyter (2007),
  443-453. [arXiv:math/0601017](https://arxiv.org/abs/math/0601017)
- [BBMST24] Balister, P., Bollobás, B., Morris, R., Sahasrabudhe, J. and Tiba, M., *The structure
  and number of Erdős covering systems*. J. Eur. Math. Soc. 26 (2024), 75-109.
  [arXiv:1904.04806](https://arxiv.org/abs/1904.04806)

See also [erdosproblems.com/1188](https://www.erdosproblems.com/1188), which counts minimal
covering systems with bounded moduli.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos1189

/-- `M` is a covering set: all its elements are $> 1$ and some choice of residues
`a m (mod m)`, one for each `m ∈ M`, is such that every integer satisfies at least one of the
congruences. -/
def IsCoveringSet (M : Finset ℕ) : Prop :=
  (∀ m ∈ M, 1 < m) ∧ ∃ a : ℕ → ℤ, ∀ z : ℤ, ∃ m ∈ M, z ≡ a m [ZMOD m]

/-- `M` is an irreducible covering set: it is a covering set and no proper subset of it is. -/
def IsIrreducibleCoveringSet (M : Finset ℕ) : Prop :=
  IsCoveringSet M ∧ ∀ N : Finset ℕ, N ⊂ M → ¬ IsCoveringSet N

/-- The empty set is not a covering set, since the integer `0` satisfies no congruence. -/
@[category test, AMS 11]
theorem not_isCoveringSet_empty : ¬ IsCoveringSet ∅ := by
  rintro ⟨-, a, ha⟩
  obtain ⟨m, hm, -⟩ := ha 0
  simp at hm

/-- $I(k)$ is the number of irreducible covering sets of size `k`. There are only finitely many
[Er80, p. 95], so `ncard` is the true count. It is `0` if there are none. -/
noncomputable def irreducibleCount (k : ℕ) : ℕ :=
  {M : Finset ℕ | IsIrreducibleCoveringSet M ∧ M.card = k}.ncard

/-- The values taken by the largest modulus $n_k$ over the irreducible covering sets of size
`k`. -/
def largestModulus (k : ℕ) : Set ℕ :=
  {n | ∃ M : Finset ℕ, IsIrreducibleCoveringSet M ∧ M.card = k ∧ IsGreatest (M : Set ℕ) n}

/-- The maximum of $\sum 1/n_i$ over the irreducible covering sets $\{n_1, \ldots, n_k\}$ of size
`k`. There are only finitely many such sets, so the `sSup` is a maximum, except that it is `0` if
there are none. -/
noncomputable def maxReciprocalSum (k : ℕ) : ℝ :=
  sSup {s : ℝ | ∃ M : Finset ℕ, IsIrreducibleCoveringSet M ∧ M.card = k ∧
    s = ∑ m ∈ M, (m : ℝ)⁻¹}

def erdos_1189.parts.i.answer : ℕ → ℝ := sorry

/--
Call a set of distinct integers $1<n_1<\cdots<n_k$ a covering set if there is a choice of
$a_i\pmod{n_i}$ for $1\leq i\leq k$ such that every integer satisfies at least one of these
congruences. A set is an irreducible covering set if no proper subset is a covering set.

How many irreducible covering sets of size $k$ are there?

This is the first part of the questions of Erdős [Er80, p. 95]. We read "how many" as asking for
the asymptotics of $\log I(k)$, where $I(k)$ is the number of irreducible covering sets of size
$k$; this is the scale on which the number of minimal covering systems is known [BBMST24].
-/
@[category research open, question value, AMS 11]
theorem erdos_1189.parts.i :
    (fun k : ℕ ↦ Real.log (irreducibleCount k : ℝ)) ~[atTop] erdos_1189.parts.i.answer := by
  sorry

def erdos_1189.parts.ii.answer : ℕ → ℕ × ℕ := sorry

/--
Call a set of distinct integers $1<n_1<\cdots<n_k$ a covering set if there is a choice of
$a_i\pmod{n_i}$ for $1\leq i\leq k$ such that every integer satisfies at least one of these
congruences. A set is an irreducible covering set if no proper subset is a covering set.

What is the minimum and maximum that $n_k$ can be?

This is the second part. Here $n_k$ is the largest element of an irreducible covering set of
size $k$. The answer is a pair (minimum, maximum), stated for each $k$ for which an irreducible
covering set of size $k$ exists.
-/
@[category research open, question value, AMS 11]
theorem erdos_1189.parts.ii (k : ℕ)
    (hk : ∃ M : Finset ℕ, IsIrreducibleCoveringSet M ∧ M.card = k) :
    IsLeast (largestModulus k) (erdos_1189.parts.ii.answer k).1 ∧
      IsGreatest (largestModulus k) (erdos_1189.parts.ii.answer k).2 := by
  sorry

def erdos_1189.parts.iii.answer : ℕ → ℝ := sorry

/--
Call a set of distinct integers $1<n_1<\cdots<n_k$ a covering set if there is a choice of
$a_i\pmod{n_i}$ for $1\leq i\leq k$ such that every integer satisfies at least one of these
congruences. A set is an irreducible covering set if no proper subset is a covering set.

Determine or estimate $\max \sum\frac{1}{n_i}$, where the maximum ranges over all irreducible
covering sets of size $k$.

This is the third part. We read "determine or estimate" as an estimate up to constant factors.
In [Er80, p. 95] the maximum is taken over the irreducible covering sets
$1<n_1<\cdots<n_k\leq x$, as a function of $x$; we follow the problem page, which takes it over
the irreducible covering sets of size $k$.
-/
@[category research open, question value, AMS 11]
theorem erdos_1189.parts.iii :
    maxReciprocalSum =Θ[atTop] erdos_1189.parts.iii.answer := by
  sorry

/--
Call a set of distinct integers $1<n_1<\cdots<n_k$ a covering set if there is a choice of
$a_i\pmod{n_i}$ for $1\leq i\leq k$ such that every integer satisfies at least one of these
congruences. A set is an irreducible covering set if no proper subset is a covering set.

Are there infinitely many $n$ such that the divisors of $n$ (which are $>1$) form an irreducible
covering set?

This is the fourth part. Sun [Su07, Theorem 1.4(i) and Corollary 1.3] proved that the answer is
yes: see `erdos_1189.variants.sun`.
-/
@[category research solved, question, AMS 11]
theorem erdos_1189.parts.iv :
    {n : ℕ | IsIrreducibleCoveringSet (n.divisors.filter (1 < ·))}.Infinite := by
  sorry

/--
The divisors of $12$ (which are $>1$) are an example of an irreducible covering set. Sun [Su07]
proved more generally that, for any odd prime $p$, the divisors (which are $>1$) of $2^{p-1}p$
form an irreducible covering set, settling the final question.

That $n=12$ is an example is already noted in [Er80, p. 95].
-/
@[category research solved, AMS 11]
theorem erdos_1189.variants.sun (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    IsIrreducibleCoveringSet ((2 ^ (p - 1) * p).divisors.filter (1 < ·)) := by
  sorry

/--
Simpson [Si85] proved $n_k\leq 2^{k-1}$.

Here $n_k$ is the largest element of an irreducible covering set of size $k$. The bound follows
from Simpson's theorem [Si85] (see [BBMST24, Theorem 2.4]), as stated in [BBMST24, Section 1].
-/
@[category research solved, AMS 11]
theorem erdos_1189.variants.simpson (M : Finset ℕ) (hM : IsIrreducibleCoveringSet M) :
    ∀ n ∈ M, n ≤ 2 ^ (M.card - 1) := by
  sorry

/-- The constant $\tau = \sum_{t \geq 1} \log^2\left(\frac{t+1}{t}\right)$ of [BBMST24]. -/
noncomputable def bbmstTau : ℝ :=
  ∑' t : ℕ, Real.log (((t : ℝ) + 2) / ((t : ℝ) + 1)) ^ 2

/--
Let $I(k)$ count the number of irreducible covering sets of size $k$. Balister, Bollobás, Morris,
Sahasrabudhe, and Tiba [BBMST24] proved that
$$I(k) \leq \exp\left((c+o(1))\frac{k^{3/2}}{(\log k)^{1/2}}\right)$$
by proving that the right-hand side is an asymptotic for the number of minimal covering systems
on $k$ moduli.

Here $c = 4\sqrt{\tau}/3$ [BBMST24, Theorem 1.1]. The bound for $I(k)$ follows because each
irreducible covering set is the set of moduli of a minimal covering system. The $o(1)$ is stated
with an arbitrary $\varepsilon > 0$.
-/
@[category research solved, AMS 11]
theorem erdos_1189.variants.bbmst (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, (irreducibleCount k : ℝ) ≤
      Real.exp ((4 * Real.sqrt bbmstTau / 3 + ε) *
        ((k : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt (Real.log k))) := by
  sorry

end Erdos1189
