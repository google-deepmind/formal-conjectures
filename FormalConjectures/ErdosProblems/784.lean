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
# Erdős Problem 784

*References:*
- [erdosproblems.com/784](https://www.erdosproblems.com/784)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [ErRu80] Erdős, P. and Ruzsa, I. Z., *On the small sieve. I. Sifting by primes*. J. Number Theory
  (1980), 385--394.
- [Ru82] Ruzsa, Imre Z., *On the small sieve. {II}. Sifting by composite numbers*. J. Number Theory
  (1982), 260--268.
- [Sa98] Saias, Eric, *Applications des entiers \`a{} diviseurs denses*. Acta Arith. (1998), 225--240.
- [ScSz59] Schinzel, A. and Szekeres, G., *Sur un probl\`{e}me de M. Paul Erdős*. Acta Sci. Math.
  (Szeged) (1959), 221-229.
- [We25] Weingartner, Andreas, *The Schinzel-Szekeres function*. Res. Number Theory (2025), Paper
  No. 63, 32.
-/

open Filter Asymptotics Real Finset

namespace Erdos784

/--
$H_C(x)$ is the minimum of $\#\{ m\leq x : a\nmid m\textrm{ for all }a\in A\}$ as $A$ ranges over
all subsets of $\{2,\ldots,\lfloor x\rfloor\}$ with $\sum_{n\in A}\frac{1}{n}\leq C$.

For $C\geq 0$ the empty set is admissible, so this is the minimum of a nonempty set of natural
numbers. (If $C<0$ there are no admissible sets and `sInf` returns $0$.)
-/
noncomputable def H (C : ℝ) (x : ℕ) : ℕ :=
  sInf {(avoidsDivisors A x).card | (A : Finset ℕ) (_ : A ⊆ Finset.Icc 2 x)
    (_ : A.reciprocalSum ≤ C)}

/--
The bound asked in the boxed problem: some $c=c(C)>0$ such that
$H_C(x)\gg x/(\log x)^c$ for all sufficiently large $x$.
-/
def BoundHolds (C : ℝ) : Prop :=
  ∃ c > (0 : ℝ), ∃ K > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
    K * (x : ℝ) / (log x) ^ c ≤ H C x

/-- For `C ≥ 0` the empty sieve is admissible, so `H C x ≤ x`. -/
@[category API, AMS 11]
lemma H_le_self {C : ℝ} (hC : 0 ≤ C) (x : ℕ) : H C x ≤ x := by
  refine Nat.sInf_le ⟨∅, empty_subset _, by simpa [reciprocalSum_empty] using hC,
    card_avoidsDivisors_empty x⟩

/-- Enlarging `C` can only shrink `H` when `C ≥ 0` (empty sieve is admissible). -/
@[category API, AMS 11]
lemma H_anti {C C' : ℝ} (hC : 0 ≤ C) (h : C ≤ C') (x : ℕ) : H C' x ≤ H C x := by
  classical
  let S : Set ℕ := {(avoidsDivisors A x).card | (A : Finset ℕ) (_ : A ⊆ Icc 2 x)
    (_ : A.reciprocalSum ≤ C)}
  let S' : Set ℕ := {(avoidsDivisors A x).card | (A : Finset ℕ) (_ : A ⊆ Icc 2 x)
    (_ : A.reciprocalSum ≤ C')}
  have hsub : S ⊆ S' := by
    rintro _ ⟨A, hA, hsum, rfl⟩
    exact ⟨A, hA, hsum.trans h, rfl⟩
  have hne : S.Nonempty :=
    ⟨x, ∅, empty_subset _, by simpa [reciprocalSum_empty] using hC, card_avoidsDivisors_empty x⟩
  exact csInf_le_csInf' hne hsub

/-- Any admissible sieve witnesses an upper bound on `H C x`. -/
@[category API, AMS 11]
lemma H_le_avoidsDivisors_card {C : ℝ} {A : Finset ℕ} {x : ℕ}
    (hA : A ⊆ Icc 2 x) (hsum : A.reciprocalSum ≤ C) :
    H C x ≤ (avoidsDivisors A x).card :=
  Nat.sInf_le ⟨A, hA, hsum, rfl⟩

/-- If `C < 0` there are no admissible sets (reciprocal sums are nonnegative), so `H C x = 0`. -/
@[category API, AMS 11]
lemma H_eq_zero_of_neg {C : ℝ} (hC : C < 0) (x : ℕ) : H C x = 0 := by
  classical
  have hempty :
      {(avoidsDivisors A x).card | (A : Finset ℕ) (_ : A ⊆ Icc 2 x)
        (_ : A.reciprocalSum ≤ C)} = ∅ := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨A, _hA, hsum, rfl⟩
    exact not_lt_of_ge (reciprocalSum_nonneg A) (lt_of_le_of_lt hsum hC)
  change sInf _ = 0
  rw [hempty, Nat.sInf_empty]


/-- If `0 ≤ C < 1/x` (and `x ≥ 1`) then only the empty sieve is admissible, so `H C x = x`. -/
@[category API, AMS 11]
lemma H_eq_self_of_lt_inv {C : ℝ} {x : ℕ} (hx : 1 ≤ x) (hC0 : 0 ≤ C)
    (hC : C < (1 : ℝ) / x) : H C x = x := by
  classical
  let S : Set ℕ := {(avoidsDivisors A x).card | (A : Finset ℕ) (_ : A ⊆ Icc 2 x)
    (_ : A.reciprocalSum ≤ C)}
  have hempty_mem : x ∈ S :=
    ⟨∅, empty_subset _, by simpa [reciprocalSum_empty] using hC0, card_avoidsDivisors_empty x⟩
  have honly : S = {x} := by
    ext n
    constructor
    · rintro ⟨A, hA, hsum, rfl⟩
      have hAempty : A = ∅ := by
        by_contra hne
        have hAne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
        obtain ⟨a, ha⟩ := hAne
        have haI := mem_Icc.mp (hA ha)
        have hx2 : 2 ≤ x := le_trans haI.1 haI.2
        have hge : (1 : ℝ) / x ≤ A.reciprocalSum :=
          le_reciprocalSum_of_subset_Icc_two hA ⟨a, ha⟩ hx2
        exact (not_le_of_gt hC) (hge.trans hsum)
      subst hAempty
      simp [card_avoidsDivisors_empty]
    · intro hn
      simp only [Set.mem_singleton_iff] at hn
      subst hn
      exact hempty_mem
  change sInf S = x
  simp [honly, csInf_singleton]



/-- Special case `C = 0`: only the empty sieve is admissible for `x ≥ 1`, so `H 0 x = x`. -/
@[category API, AMS 11]
lemma H_zero_eq_self {x : ℕ} (hx : 1 ≤ x) : H (0 : ℝ) x = x :=
  H_eq_self_of_lt_inv hx le_rfl <|
    one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega)))

/-- For `x = 0` the survivor set is empty, so `H C 0 = 0` for every `C`. -/
@[simp, category API, AMS 11]
lemma H_of_x_zero (C : ℝ) : H C 0 = 0 := by
  classical
  by_cases hC : (0 : ℝ) ≤ C
  · have hle : H C 0 ≤ 0 := by
      simpa [card_avoidsDivisors_empty] using
        (H_le_avoidsDivisors_card (A := (∅ : Finset ℕ)) (x := 0) (empty_subset _)
          (by simpa [reciprocalSum_empty] using hC))
    exact Nat.eq_zero_of_le_zero hle
  · exact H_eq_zero_of_neg (lt_of_not_ge hC) 0

/-- Singleton sieve `{a}` with `2 ≤ a ≤ x` and `1/a ≤ C` gives `H C x ≤ x - ⌊x/a⌋`. -/
@[category API, AMS 11]
lemma H_le_card_singleton_sieve {C : ℝ} {a x : ℕ} (ha : 2 ≤ a) (hax : a ≤ x)
    (hsum : (1 : ℝ) / a ≤ C) :
    H C x ≤ x - x / a := by
  have hA : ({a} : Finset ℕ) ⊆ Icc 2 x := by
    intro y hy
    simp only [mem_singleton] at hy
    subst hy
    exact mem_Icc.mpr ⟨ha, hax⟩
  have hsum' : ({a} : Finset ℕ).reciprocalSum ≤ C := by
    simpa [reciprocalSum_singleton] using hsum
  simpa [card_avoidsDivisors_singleton] using H_le_avoidsDivisors_card hA hsum'

/-- Sieving by `{a}` leaves `x - ⌊x/a⌋` survivors. -/
@[category test, AMS 11]
theorem erdos_784.variants.card_singleton_sieve (a x : ℕ) :
    (avoidsDivisors {a} x).card = x - x / a :=
  card_avoidsDivisors_singleton a x

/--
Let $C>0$. Does there exist a $c>0$ (depending on $C$) such that, for all sufficiently large $x$,
if $A\subseteq [1,x]$ has $\sum_{n\in A}\frac{1}{n}\leq C$ then
$$\#\{ m\leq x : a\nmid m\textrm{ for all }a\in A\}\gg\frac{x}{(\log x)^c}?$$

In the comments jif has noted that the answer is trivially no for every $C\geq 1$ with $A=\{1\}$.
Presumably (as is usual in these kind of questions) the assumption that $1\not\in A$ is intended.

Together these answer the given question (positively for $0<C\leq 1$ and negatively for $C>1$).
-/
@[category research solved, AMS 11]
theorem erdos_784 (C : ℝ) (hC : 0 < C) : BoundHolds C ↔ C ≤ 1 := by
  sorry

/--
For $C=1$ it is known that
$$H_1(x)\asymp \frac{x}{\log x}.$$
The lower bound is due to Ruzsa [Ru82], and the upper bound is due to Saias [Sa98].
-/
@[category research solved, AMS 11]
theorem erdos_784.variants.C_eq_one :
    (fun x : ℕ ↦ (H 1 x : ℝ)) =Θ[atTop] (fun x : ℕ ↦ (x : ℝ) / log x) := by
  sorry

/--
For fixed $C>1$ Ruzsa answered this question in the negative. (In [Er80] Erdős states that Ruzsa's
construction shows his 'intuition completely misled' him.) In fact
$$H_C(x)=x^{e^{1-C}+o(1)}.$$
This was improved by Weingartner [We25] who proved (for any fixed $C>1$)
$$H_C(x)\asymp \frac{x^{e^{1-C}}}{\log x}.$$
-/
@[category research solved, AMS 11]
theorem erdos_784.variants.weingartner (C : ℝ) (hC : 1 < C) :
    (fun x : ℕ ↦ (H C x : ℝ)) =Θ[atTop]
      (fun x : ℕ ↦ (x : ℝ) ^ exp (1 - C) / log x) := by
  sorry

/--
On the other hand, if $A$ is restricted to sets of primes then Erdős and Ruzsa [ErRu80] proved that
there are always $\gg_C x$ many $n\leq x$ not divisible by any $p\in A$.
-/
@[category research solved, AMS 11]
theorem erdos_784.variants.primes (C : ℝ) (hC : 0 < C) :
    ∃ K > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 x → (∀ p ∈ A, p.Prime) → A.reciprocalSum ≤ C →
        K * (x : ℝ) ≤ (avoidsDivisors A x).card := by
  sorry

/--
jif also notes that a lower bound of $(1-C)x$ is trivial by the union bound if $0<C<1$.
-/
@[category textbook, AMS 11]
theorem erdos_784.variants.union_bound (C : ℝ) (hC : 0 < C) (_hC1 : C < 1) :
    ∀ᶠ x : ℕ in atTop, (1 - C) * x ≤ H C x := by
  refine Eventually.of_forall fun x ↦ ?_
  simp only [H]
  have hne : Set.Nonempty
      {(avoidsDivisors A x).card | (A : Finset ℕ) (_ : A ⊆ Icc 2 x)
        (_ : A.reciprocalSum ≤ C)} :=
    ⟨x, ∅, empty_subset _, by simpa [reciprocalSum_empty] using hC.le,
      card_avoidsDivisors_empty x⟩
  have hmem := Nat.sInf_mem hne
  simp only [Set.mem_ofPred_eq] at hmem
  obtain ⟨A, h₁, h₂, heq⟩ := hmem
  have hsum : A.reciprocalSum ≤ C := by
    clear * - h₁ h₂; first | exact h₁ | exact h₂
  rw [← heq]
  exact le_card_avoidsDivisors_of_reciprocalSum_le A x hsum

/-- Sieving by `{1}` empties `{1, …, x}`; this motivates excluding `1` from admissible `A` in `H`. -/
@[category test, AMS 11]
theorem erdos_784.variants.sieving_by_one (x : ℕ) :
    avoidsDivisors ({1} : Finset ℕ) x = ∅ :=
  avoidsDivisors_eq_empty_of_one_mem (by simp) x

/-- Empty sieve: `#(avoidsDivisors ∅ x) = x`. -/
@[category test, AMS 11]
theorem erdos_784.variants.card_empty_sieve (x : ℕ) :
    (avoidsDivisors (∅ : Finset ℕ) x).card = x :=
  card_avoidsDivisors_empty x

/-- Union of sieves is intersection of survivors. -/
@[category test, AMS 11]
theorem erdos_784.variants.sieve_union (A B : Finset ℕ) (x : ℕ) :
    avoidsDivisors (A ∪ B) x = avoidsDivisors A x ∩ avoidsDivisors B x :=
  avoidsDivisors_union A B x

end Erdos784
