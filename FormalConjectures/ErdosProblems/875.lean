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
# Erdős Problem 875

*References:*
- [erdosproblems.com/875](https://www.erdosproblems.com/875)
- [Er98] Erdős, P., *Some of my new and almost new problems and results in combinatorial number
  theory*. Number theory (Eger, 1996) (1998), 169-180.
- [Er62c] Erdős, P., *Some remarks on number theory. III* (in Hungarian). Mat. Lapok 13 (1962),
  28-38. [PDF](https://www.renyi.hu/~p_erdos/1962-22.pdf)
- [ENS91] Erdős, P., Nicolas, J.-L. and Sárközy, A., *Sommes de sous-ensembles*. J. Théor. Nombres
  Bordeaux 3 (1991), 55-72. [Numdam](https://www.numdam.org/item/JTNB_1991__3_1_55_0/)
- [DeFr99] Deshouillers, J.-M. and Freiman, G. A., *On an additive problem of Erdős and Straus,
  2*. Astérisque 258 (1999), 141-148. [Numdam](https://www.numdam.org/item/AST_1999__258__141_0/)

The finite version of this problem is [erdosproblems.com/874](https://www.erdosproblems.com/874).
-/

@[expose] public section

open Filter

namespace Erdos875

/-- `rSums A r` is the set $S_r$ of all sums $a_1+\cdots+a_r$ of $r$ distinct elements of `A`.
For `r = 0` it is `{0}`. -/
def rSums (A : Set ℕ) (r : ℕ) : Set ℕ :=
  {s | ∃ T : Finset ℕ, (T : Set ℕ) ⊆ A ∧ T.card = r ∧ ∑ x ∈ T, x = s}

/-- A set `A` of natural numbers is *admissible* if the sets $S_r$ of sums of $r$ distinct
elements of `A` are pairwise disjoint for $r\geq 1$. Here `ℕ` contains $0$, but an infinite
admissible set does not contain $0$: for any other element $a$ we would have
$a=0+a\in S_1\cap S_2$. -/
def IsAdmissible (A : Set ℕ) : Prop :=
  (Set.Ici (1 : ℕ)).PairwiseDisjoint (rSums A)

/-- The counting function $A(x)$: the number of elements of `A` that are at most `x`. The set is
finite, so `ncard` is the true cardinality. -/
noncomputable def countingFunction (A : Set ℕ) (x : ℕ) : ℕ :=
  (A ∩ Set.Iic x).ncard

/-- For an infinite set `A = {a₁ < a₂ < ⋯}`, `Nat.nth (· ∈ A) k` is $a_{k+1}$, because the
enumeration starts at index `0`. Hence `gap A n` is $a_{n+1}-a_n$ for $n\geq 1$. The value at
`n = 0` is junk and is never used, since the statements below only concern large `n`. -/
noncomputable def gap (A : Set ℕ) (n : ℕ) : ℕ :=
  Nat.nth (· ∈ A) n - Nat.nth (· ∈ A) (n - 1)

/-- The sums of one element are the elements: $S_1=A$. -/
@[category API, AMS 11]
theorem rSums_one (A : Set ℕ) : rSums A 1 = A := by
  ext s
  constructor
  · rintro ⟨T, hT, hc, rfl⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
    simpa using hT
  · intro hs
    exact ⟨{s}, by simpa using hs, by simp, by simp⟩

def erdos_875.answer : Set ℝ := sorry

/--
Let $A=\{a_1<a_2<\cdots\}\subset \mathbb{N}$ be an infinite set such that the sets
$$S_r = \{ a_1+\cdots +a_r : a_1<\cdots<a_r\in A\}$$
are disjoint for distinct $r\geq 1$. How fast can such a sequence grow? How small can
$a_{n+1}-a_n$ be? In particular, for which $c$ is it possible that $a_{n+1}-a_n\leq n^{c}$?

A problem of Deshouillers and Erdős [Er98] (an infinite version of
[874](https://www.erdosproblems.com/874)). Such sets are sometimes called admissible. We state the
last question: the set of such $c$ is `erdos_875.answer`. The bound is required for all large $n$,
since otherwise the first few $n$ would constrain the answer. The first two questions are not
formalised separately. Erdős also writes that it is not completely trivial to find such a sequence
with $a_{n+1}/a_n\to 1$ (not formalised).
-/
@[category research open, question value, AMS 11]
theorem erdos_875 :
    {c : ℝ | ∃ A : Set ℕ, A.Infinite ∧ IsAdmissible A ∧
      ∀ᶠ n : ℕ in atTop, (gap A n : ℝ) ≤ (n : ℝ) ^ c} = erdos_875.answer := by
  sorry

/--
Erdős, Nicolas and Sárközy [ENS91, Theorem 2] constructed an infinite admissible set $A$ with
$$A(x)=\lvert\{a\in A: a\leq x\}\rvert \gg x^{5-2\sqrt6}.$$
The implied constant is positive and the inequality is required for all large $x$. This improves
a result of Erdős [Er62c], who obtained $A(x)\gg x^{c}$ for some unspecified $c>0$.
-/
@[category research solved, AMS 11]
theorem erdos_875.variants.erdos_nicolas_sarkozy :
    ∃ A : Set ℕ, A.Infinite ∧ IsAdmissible A ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ x : ℕ in atTop, c * (x : ℝ) ^ (5 - 2 * Real.sqrt 6) ≤ (countingFunction A x : ℝ) := by
  sorry

/--
Since $5-2\sqrt6=(5+2\sqrt6)^{-1}$, the result of [ENS91, Theorem 2] gives
$a_n\ll n^{5+2\sqrt6}$, hence $a_{n+1}-a_n\leq a_{n+1}\ll n^{5+2\sqrt6}$. So every
$c>5+2\sqrt6$ is possible in the main question.
-/
@[category research solved, AMS 11]
theorem erdos_875.variants.polynomial_gaps (c : ℝ) (hc : 5 + 2 * Real.sqrt 6 < c) :
    ∃ A : Set ℕ, A.Infinite ∧ IsAdmissible A ∧
      ∀ᶠ n : ℕ in atTop, (gap A n : ℝ) ≤ (n : ℝ) ^ c := by
  sorry

/--
Deshouillers and Freiman [DeFr99, Theorem 1] proved a conjecture of Erdős on the finite version
([874](https://www.erdosproblems.com/874)): for all sufficiently large $N$, every admissible set
$A\subseteq\{1,\ldots,N\}$ satisfies
$$\lvert A\rvert\leq 2\sqrt{N+\tfrac14}-1.$$
This is sharp: by Straus, the set of $k$ consecutive integers ending at $N$ is admissible if and
only if $k\leq 2\sqrt{N+\frac14}-1$.
-/
@[category research solved, AMS 11]
theorem erdos_875.variants.deshouillers_freiman :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset ℕ, (A : Set ℕ) ⊆ Set.Icc 1 N →
      IsAdmissible (A : Set ℕ) → (A.card : ℝ) ≤ 2 * Real.sqrt ((N : ℝ) + 1 / 4) - 1 := by
  sorry

end Erdos875
