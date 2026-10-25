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
# Erdős Problem 1194

*References:*
- [erdosproblems.com/1194](https://www.erdosproblems.com/1194)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  6 (1980), 89-115. [PDF](https://www.renyi.hu/~p_erdos/1980-03.pdf)
- [HaRo66] Halberstam, H. and Roth, K. F., *Sequences. Vol. I*. Oxford University Press, Oxford
  (1966), xx+291.
- [Le04] Lev, Vsevolod F., *Reconstructing integer sets from their representation functions*.
  Electron. J. Combin. 11 (2004), Research Paper 78, 6 pp.
  [Link](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v11i1r78)
-/

@[expose] public section

open Filter

namespace Erdos1194

/-- `IsPerfectDifferenceSetInt A` says that `A` is a set of positive integers such that every
nonzero integer is $a - b$ for exactly one pair `(a, b)` of distinct elements of `A`. This is the
notion over $\mathbb{Z}$ of [Er80] and [Le04], that is, `IsPerfectDifferenceSet A 0`
(as `ZMod 0 = ℤ`). -/
def IsPerfectDifferenceSetInt (A : Set ℕ) : Prop :=
  0 ∉ A ∧ IsPerfectDifferenceSet A 0

/-- `IsLargerElement A n a` says that `a` is the larger element of a representation
$n = a - b$ with $a, b \in A$. If `A` is a perfect difference set and $n \geq 1$, there is exactly
one such `a`, and it is the element $a_n$ of the problem (not the $n$th element of `A`). -/
def IsLargerElement (A : Set ℕ) (n a : ℕ) : Prop :=
  a ∈ A ∧ ∃ b ∈ A, a = b + n

/-- `HasLargeElement A f` says that $a_n \geq f(n)$ for infinitely many $n$, where $a_n$ is the
larger element of the representation of $n$ as a difference of two elements of `A`. -/
def HasLargeElement (A : Set ℕ) (f : ℕ → ℝ) : Prop :=
  ∃ᶠ n in atTop, ∃ a, IsLargerElement A n a ∧ f n ≤ a

/-- In a perfect difference set every $n \geq 1$ has a representation $n = a - b$, so some `a`
satisfies `IsLargerElement A n a`. -/
@[category API, AMS 5 11]
theorem IsPerfectDifferenceSetInt.exists_isLargerElement {A : Set ℕ}
    (hA : IsPerfectDifferenceSetInt A) {n : ℕ} (hn : 0 < n) : ∃ a, IsLargerElement A n a := by
  have hn' : (n : ZMod 0) ∈ {x : ZMod 0 | x ≠ 0} := by
    simpa [ZMod.natCast_eq_zero_iff] using hn.ne'
  obtain ⟨⟨a, b⟩, ⟨ha, hb, -⟩, hab⟩ := hA.2.surjOn hn'
  refine ⟨a, ha, b, hb, ?_⟩
  have h : ((a : ℤ) - b : ℤ) = n := hab
  omega

/-- In a perfect difference set the larger element of the representation of $n \geq 1$ is
unique, so $a_n$ is well defined. -/
@[category API, AMS 5 11]
theorem IsLargerElement.unique {A : Set ℕ} {n a a' : ℕ} (hA : IsPerfectDifferenceSetInt A)
    (hn : 0 < n) (h : IsLargerElement A n a) (h' : IsLargerElement A n a') : a = a' := by
  obtain ⟨ha, b, hb, rfl⟩ := h
  obtain ⟨ha', b', hb', rfl⟩ := h'
  have h1 : (b + n, b) ∈ A.offDiag := Set.mem_offDiag.2 ⟨ha, hb, (show b + n ≠ b by omega)⟩
  have h2 : (b' + n, b') ∈ A.offDiag := Set.mem_offDiag.2 ⟨ha', hb', (show b' + n ≠ b' by omega)⟩
  have e := hA.2.injOn h1 h2 (by simp)
  exact congrArg Prod.fst e

/-- The larger element of a representation of $n$ is at least $n$, so $a_n / n \geq 1$. -/
@[category API, AMS 5 11]
theorem IsLargerElement.le_self {A : Set ℕ} {n a : ℕ} (h : IsLargerElement A n a) : n ≤ a := by
  obtain ⟨-, b, -, hab⟩ := h
  omega

def erdos_1194.answer : Set (ℕ → ℝ) := sorry

/--
Let $A\subset\mathbb{N}$ be such that every integer $n\geq 1$ can be written uniquely as
$a_n-b_n$ for some $a_n,b_n\in A$. How fast must $a_n/n$ increase?

A question of Erdős [Er80, p. 100]. Here $a_n$ is the larger element of the representation of
$n$, not the $n$th element of $A$. We read "must increase" as: the answer is the set of
non-decreasing $G$ such that every such $A$ has $a_n \geq c\,n\,G(n)$ for infinitely many $n$,
for some $c>0$ depending on $A$.
-/
@[category research open, question value, AMS 5 11]
theorem erdos_1194 :
    {G : ℕ → ℝ | Monotone G ∧ ∀ A : Set ℕ, IsPerfectDifferenceSetInt A →
      ∃ c > (0 : ℝ), HasLargeElement A (fun n ↦ c * G n * n)} = erdos_1194.answer := by
  sorry

/--
Such a set is called a perfect difference set; they can be constructed, for example, by a greedy
approach (as detailed by Lev [Le04]).

Erdős [Er80, p. 100] remarks that it is easy to construct such a sequence, and [Le04, Section 3]
constructs a perfect difference set $A\subseteq\mathbb{N}$ (positive integers) greedily.
-/
@[category research solved, AMS 5 11]
theorem erdos_1194.variants.exists_perfect_difference_set :
    ∃ A : Set ℕ, IsPerfectDifferenceSetInt A := by
  sorry

/--
The greedy construction achieves $a_n\ll n^3$.

[Le04, Section 3] shows that the $n$th element of the set built greedily is $O(n^3)$. Each step
represents the least positive integer not yet a difference, so $n$ is represented within the
first $n+1$ steps, which gives $a_n\ll n^3$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1194.variants.greedy_upper_bound :
    ∃ A : Set ℕ, IsPerfectDifferenceSetInt A ∧ ∃ C : ℝ, ∀ n : ℕ, 0 < n →
      ∀ a, IsLargerElement A n a → (a : ℝ) ≤ C * (n : ℝ) ^ 3 := by
  sorry

/--
Erdős [Er80, p. 100] wrote it is 'easy to see' that
$$\limsup_{n\to \infty}\frac{a_n}{n}=\infty.$$
Indeed, since $A$ must be a Sidon set, if $a_n \leq f(n)n$ for all $n$, then all differences in
$[1,x/f(x)]$ can be realised by differences from $A\cap [1,x]$, and hence
$\lvert A\cap [1,x]\rvert^2 \gg x/f(x)$. Erdős (see for example [HaRo66]) proved that for
infinitely many $x$ $\lvert A\cap [1,x]\rvert \ll (x/\log x)^{1/2}$, which is a contradiction for
a suitable choice of $f$.

Formally: for every perfect difference set $A$ and every $C$, $a_n \geq Cn$ for infinitely many
$n$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1194.variants.limsup_eq_top :
    ∀ A : Set ℕ, IsPerfectDifferenceSetInt A → ∀ C : ℝ, HasLargeElement A (fun n ↦ C * n) := by
  sorry

end Erdos1194
