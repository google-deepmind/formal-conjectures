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
# Ben Green's Open Problem 31

Write $F(N)$ for the largest Sidon subset of $[N]$.
Improve, at least for infinitely many $N$, the bounds $N^{1/2} + O(1) \le F(N) \le N^{1/2} + N^{1/4} + O(1)$.

Note: the upper bound was improved to $N^{1/2} + 0.98183 N^{1/4} + O(1)$ in [CHO25], and then to
$N^{1/2} + 0.94349\ldots N^{1/4} + O(1)$ in [HZ26].

Related to Erdős Problem 30.

*References:*
- [Gr24] [Ben Green's Open Problem 31](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.7 Problem 31)
- [Gr01] Green, Ben. "The number of squares and $ B_h [g] $ sets."
  Acta Arithmetica 100.4 (2001): 365-390.
- [BFR23] Balogh, József, Zoltán Füredi, and Souktik Roy. "An upper bound on the size of Sidon sets."
  The American Mathematical Monthly 130.5 (2023): 437-445.
- [CHO25] Carter, Daniel, Zach Hunter, and Kevin O’Bryant. "On the diameter of finite Sidon sets."
  Acta Mathematica Hungarica 175.1 (2025): 108-126.
- [HZ26] Hou, Jianfeng, and Hongbin Zhao. "An Improved Upper Bound for Finite Sidon Sets via
  Vector-Valued Smoothing." [arXiv:2607.01169](https://arxiv.org/abs/2607.01169) (2026).
- [ET41] Erdos, Paul, and Pál Turán. "On a problem of Sidon in additive number theory, and on some
  related problems." J. London Math. Soc 16.4 (1941): 212-215.
- [Li69] Lindström, Bernt. “A remark on B4-Sequences.” Journal of Combinatorial Theory,
  Series A 7 (1969): 276-277.
- [CLZ01] Cohen, G.D., Litsyn, S., & Zémor, G. (2001). Binary B2-Sequences : A New Upper Bound.
  J. Comb. Theory A, 94, 152-155.
- [BS85] Babai, László, and Vera T. Sós. "Sidon sets in groups and induced subgraphs of Cayley
  graphs." European Journal of Combinatorics 6.2 (1985): 101-114.
  [doi:10.1016/S0195-6698(85)80001-9](https://doi.org/10.1016/S0195-6698%2885%2980001-9)
-/

@[expose] public section

namespace Green31

open Filter

/-- Let $F(N)$ be the largest Sidon subset of $[N]$. -/
noncomputable def F (N : ℕ) : ℝ := Finset.maxSidonSubsetCard (Finset.Icc 1 N)

/-- Can we improve the lower bound $N^{1/2} + O(1)$, at least for infinitely many $N$? -/
@[category research open, AMS 5 11]
theorem green_31.lower :
    let ans := (answer(sorry) : ℕ → ℝ)
    Filter.Tendsto (fun N ↦ ans N - Real.sqrt (N : ℝ)) atTop atTop ∧ -- Break the O(1) barrier
    ∃ᶠ N in atTop, ans N ≤ F N := by
  sorry

/-- Can we improve the lower bound $N^{1/2} + O(1)$, for all sufficiently large $N$? -/
@[category research open, AMS 5 11]
theorem green_31.variants.lower_eventually :
    let ans := (answer(sorry) : ℕ → ℝ)
    Filter.Tendsto (fun N ↦ ans N - Real.sqrt (N : ℝ)) atTop atTop ∧ -- Break the O(1) barrier
    ∀ᶠ N in atTop, ans N ≤ F N := by
  sorry

/--
Can we improve the upper bound $N^{1/2} + 0.94349 N^{1/4} + O(1)$ [HZ26], at least for infinitely
many $N$?
-/
@[category research open, AMS 5 11]
theorem green_31.upper :
    let ans := (answer(sorry) : ℕ → ℝ)
    (∃ᶠ N in atTop, F N ≤ ans N) ∧
    ∃ c < (0.94349 : ℝ), ∃ C : ℝ, ∀ᶠ N in atTop, ans N - Real.sqrt (N : ℝ) ≤ c * (N : ℝ) ^ (4⁻¹ : ℝ) + C := by
  sorry

/--
Can we improve the upper bound $N^{1/2} + 0.94349 N^{1/4} + O(1)$ [HZ26], for all sufficiently
large $N$?
-/
@[category research open, AMS 5 11]
theorem green_31.variants.upper_eventually :
    let ans := (answer(sorry) : ℕ → ℝ)
    (∀ᶠ N in atTop, F N ≤ ans N) ∧
    ∃ c < (0.94349 : ℝ), ∃ C : ℝ, ∀ᶠ N in atTop, ans N - Real.sqrt (N : ℝ) ≤ c * (N : ℝ) ^ (4⁻¹ : ℝ) + C := by
  sorry

/-- [Li69] proved $F(n) \le n^{1/2} + n^{1/4} + O(1)$. -/
@[category research solved, AMS 5 11]
theorem green_31.variants.upper_li69 :
    ∃ C : ℝ, ∀ᶠ N in atTop, F N ≤ Real.sqrt (N : ℝ) + (N : ℝ) ^ (4⁻¹ : ℝ) + C := by
  sorry

/--
[BFR23] obtained a small improvement, getting an upper bound of $F(N) \le N^{1/2} + 0.998 N^{1/4}$
for large $N$.
-/
@[category research solved, AMS 5 11]
theorem green_31.variants.upper_bfr23 :
    ∀ᶠ N in atTop, F N ≤ Real.sqrt (N : ℝ) + (0.998 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  sorry

/-- The upper bound was further improved to $N^{1/2} + 0.98183 N^{1/4} + O(1)$ [CHO25]. -/
@[category research solved, AMS 5 11]
theorem green_31.variants.upper_cho25 :
    ∃ C : ℝ, ∀ᶠ N in atTop, F N ≤ Real.sqrt (N : ℝ) + (0.98183 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) + C := by
  sorry

/--
[HZ26] improved the upper bound to $N^{1/2} + \gamma_0 N^{1/4} + O(1)$ with
$\gamma_0 = 0.94349\ldots < 0.9435$.
-/
@[category research solved, AMS 5 11]
theorem green_31.variants.upper_hz26 :
    ∃ C : ℝ, ∀ᶠ N in atTop, F N ≤ Real.sqrt (N : ℝ) + (0.9435 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) + C := by
  sorry

/--
It is not known whether or not there exists a Sidon subset of $\mathbb{Z}/p\mathbb{Z}$ of size
$(1 + o(1))\sqrt{p}$, for all $p$ [Gr24].
-/
@[category research open, AMS 5 11]
theorem green_31.variants.zmod_p : answer(sorry) ↔
    ∃ S : (n : ℕ) → Finset (ZMod n),
    ∃ o : ℕ → ℝ,
      (o =o[atTop] fun _ : ℕ ↦ (1 : ℝ)) ∧
      (∀ p, p.Prime → IsSidon (S p : Set (ZMod p))) ∧
      (∀ p, p.Prime → ((S p).card : ℝ) = (1 + o p) * Real.sqrt (p : ℝ)) := by
  sorry

/--
A subset $S$ of an abelian group is a Sidon set of the first kind in the sense of Babai and Sós
[BS85] if $a + b = c + d$ with $a, b, c, d \in S$ implies $|\{a, b, c, d\}| \le 2$.

Unlike `IsSidon`, this allows $a + a = b + b$ with $a \ne b$.
-/
def IsGroupSidon {G : Type*} [AddCommGroup G] (S : Set G) : Prop :=
  ∀ ⦃a b c d : G⦄, a ∈ S → b ∈ S → c ∈ S → d ∈ S → a + b = c + d →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨ (a = b ∧ c = d)

@[category API, AMS 5 11]
theorem isGroupSidon_of_isSidon {G : Type*} [AddCommGroup G] {S : Set G} (hS : IsSidon S) :
    IsGroupSidon S := by
  intro a b c d ha hb hc hd h
  rcases hS a ha c hc b hb d hd h with h | h
  · exact .inl h
  · exact .inr (.inl h)

/--
The two notions agree in a group where $2a = 2b$ implies $a = b$, such as a group of odd order.
-/
@[category API, AMS 5 11]
theorem isGroupSidon_iff_isSidon {G : Type*} [AddCommGroup G]
    (hG : Function.Injective fun a : G ↦ a + a) {S : Set G} : IsGroupSidon S ↔ IsSidon S := by
  refine ⟨fun hS a ha c hc b hb d hd h ↦ ?_, isGroupSidon_of_isSidon⟩
  rcases hS ha hb hc hd h with h' | h' | ⟨rfl, rfl⟩
  · exact .inl h'
  · exact .inr h'
  · exact .inl ⟨hG h, hG h⟩

/-- In a group of exponent $2$ an `IsSidon` set has at most one element. -/
@[category API, AMS 5 11]
theorem subsingleton_of_isSidon_of_exponent_two {G : Type*} [AddCommGroup G]
    (hG : ∀ a : G, a + a = 0) {S : Set G} (hS : IsSidon S) : S.Subsingleton := by
  intro a ha b hb
  rcases hS a ha b hb a ha b hb (by rw [hG a, hG b]) with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h

/-- Three points of the Klein four-group form a Sidon set in the sense of Babai and Sós. -/
@[category test, AMS 5 11]
theorem isGroupSidon_klein :
    IsGroupSidon ({(0, 0), (1, 0), (0, 1)} : Set (ZMod 2 × ZMod 2)) := by
  rintro a b c d (rfl | rfl | rfl) (rfl | rfl | rfl) (rfl | rfl | rfl) (rfl | rfl | rfl) <;> decide

/--
The whole Klein four-group is not a Sidon set in the sense of Babai and Sós, since
$(0, 0) + (1, 1) = (1, 0) + (0, 1)$.
-/
@[category test, AMS 5 11]
theorem not_isGroupSidon_klein_univ : ¬ IsGroupSidon (Set.univ : Set (ZMod 2 × ZMod 2)) :=
  fun h ↦ absurd (h (a := (0, 0)) (b := (1, 1)) (c := (1, 0)) (d := (0, 1)) trivial trivial
    trivial trivial (by decide)) (by decide)

/--
It is not known whether, if $G$ is an abelian group of size $n$, there always exists a Sidon subset
of $G$ of size $0.01\sqrt{n}$ [Gr24].

Green defines a Sidon set by $r_A(n) \le 1$ [Gr24, Section 4]. Read literally, this forbids
$a + a = b + b$ with $a \ne b$, and the answer is trivially negative: a Sidon subset of a group
of exponent $2$ then has at most one element. We use the definition of Babai and Sós [BS85]
instead, see `IsGroupSidon`.
-/
@[category research open, AMS 5 11]
theorem green_31.variants.abelian : answer(sorry) ↔
    ∀ (G : Type) [AddCommGroup G] [Fintype G],
      ∃ S : Finset G, IsGroupSidon (S : Set G) ∧
        0.01 * Real.sqrt (Fintype.card G) ≤ S.card := by
  sorry

/--
A set of binary vectors is Sidon if its pairwise sums, taken coordinatewise in `ℕ`, determine the
unordered pair of summands.
-/
def IsBinarySidon {n : ℕ} (S : Set (𝔽₂ n)) : Prop :=
  ∀ ⦃a b c d : 𝔽₂ n⦄, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    (fun i ↦ (a i).val + (b i).val) = (fun i ↦ (c i).val + (d i).val) →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/--
Another very nice old problem is whether there is a Sidon subset of $\{0, 1\}^n$ of size $N^{0.51}$,
where $N = 2^n$ [Gr24].
-/
@[category research open, AMS 5 11]
theorem green_31.variants.sidon_01n : answer(sorry) ↔
    ∃ S : (n : ℕ) → Finset (𝔽₂ n),
      (∀ n, IsBinarySidon (S n : Set (𝔽₂ n))) ∧
      ∀ᶠ n in atTop, ((2 : ℝ) ^ n) ^ (0.51 : ℝ) ≤ (S n).card := by
  sorry

/--
The best-known upper bound for a Sidon subset of $\{0, 1\}^n$ ($N = 2^n$) is $N^{0.5753}$ [CLZ01].
-/
@[category research solved, AMS 5 11]
theorem green_31.variants.sidon_01n_clz01 :
    ∃ C : ℝ, ∀ n, ∀ S : Finset (𝔽₂ n),
      IsBinarySidon (S : Set (𝔽₂ n)) →
        (S.card : ℝ) ≤ C * ((2 : ℝ) ^ n) ^ (0.5753 : ℝ) := by
  sorry

end Green31
