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
# Erdős Problem 1211

*References:*
- [erdosproblems.com/1211](https://www.erdosproblems.com/1211)
- [CFP22] Conlon, David and Fox, Jacob and Pham, Huy Tuan, *The upper logarithmic density of
  monochromatic subset sums*. Mathematika 68 (2022), 1292--1301.
  [arXiv:2105.15195](https://arxiv.org/abs/2105.15195)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115. [PDF](https://www.renyi.hu/~p_erdos/1980-03.pdf)
-/

@[expose] public section

open Filter

namespace Erdos1211

/-- `IsNatPartition A B` says that `A` and `B` are disjoint and `A ∪ B` is all of `ℕ`.
Here `ℕ` contains $0$. This is harmless: $0$ adds nothing to a sum of distinct elements and does
not count in the density below, so partitions of `ℕ` and of the positive integers give the same
values. -/
def IsNatPartition (A B : Set ℕ) : Prop :=
  Disjoint A B ∧ A ∪ B = Set.univ

/-- The upper logarithmic density
$$\overline{\delta}(X)=\limsup_{x\to\infty}\frac{1}{\log x}\sum_{n\in X,\ n<x}\frac{1}{n}$$
of a set `X` of natural numbers, with a real cutoff `x`. The sum runs over the positive integers
`n < x` in `X`, written as `1 ≤ n < ⌈x⌉₊` (see `mem_Ico_ceil_iff`). The quotient is eventually at
most $1 + 1/\log x$, so the `limsup` is not a junk value. -/
noncomputable def upperLogDensity (X : Set ℕ) : ℝ :=
  open scoped Classical in
  limsup (fun x : ℝ ↦
    (∑ n ∈ (Finset.Ico 1 ⌈x⌉₊).filter (· ∈ X), (n : ℝ)⁻¹) / Real.log x) atTop

/-- The larger of the upper logarithmic densities of the subset-sum sets of the two classes,
$\max(\overline{\delta}(S(A)),\overline{\delta}(S(B)))$. Here `subsetSums A` is the set of sums of
finitely many distinct elements of `A`; it contains the empty sum $0$, which does not affect the
density. -/
noncomputable def partitionValue (A B : Set ℕ) : ℝ :=
  max (upperLogDensity (subsetSums A)) (upperLogDensity (subsetSums B))

/-- A natural number `n` lies in `Finset.Ico 1 ⌈x⌉₊` exactly when it is positive and below the
real cutoff `x`. -/
@[category API, AMS 11]
theorem mem_Ico_ceil_iff (n : ℕ) (x : ℝ) :
    n ∈ Finset.Ico 1 ⌈x⌉₊ ↔ 1 ≤ n ∧ (n : ℝ) < x := by
  rw [Finset.mem_Ico, Nat.lt_ceil]

/-- Every set `A` is part of a partition, with the complement as the other class. -/
@[category API, AMS 11]
theorem isNatPartition_compl (A : Set ℕ) : IsNatPartition A Aᶜ :=
  ⟨disjoint_compl_right, Set.union_compl_self A⟩

/-- The answer, $\frac{2+\sqrt{3}}{4}$. -/
noncomputable def erdos_1211.answer : ℝ := (2 + √3) / 4

/--
Let $\mathbb{N}=A\cup B$ where $A$ and $B$ are disjoint. Let $S(A)$ be those integers which are the
sum of finitely many distinct elements of $A$, and similarly for $S(B)$.

If
$$
\overline{\delta}(X)=\limsup_{x\to \infty}\frac{1}{\log x}
  \sum_{\substack{n\in X\\ n<x}}\frac{1}{n}
$$
is the upper logarithmic density of $X$ then how large must
$$\max(\overline{\delta}(S(A)),\overline{\delta}(S(B)))$$
be?

A question of Erdős [Er80]. Conlon, Fox, and Pham [CFP22, Theorem 1] proved that the least
possible value of $\max(\overline{\delta}(S(A)),\overline{\delta}(S(B)))$ is
$\frac{2+\sqrt{3}}{4}\approx 0.93301$, and that it is attained.
-/
@[category research solved, question value, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1211.lean#L401"]
theorem erdos_1211 :
    (∀ A B : Set ℕ, IsNatPartition A B → erdos_1211.answer ≤ partitionValue A B) ∧
      ∃ A B : Set ℕ, IsNatPartition A B ∧ partitionValue A B = erdos_1211.answer := by
  sorry

end Erdos1211
