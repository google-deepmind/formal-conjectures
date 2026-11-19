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
# Erdős Problem 1183

*References:*
- [erdosproblems.com/1183](https://www.erdosproblems.com/1183)
- [Er78] Erdős, P., *Problems and results in combinatorial analysis and combinatorial number
  theory*. Proceedings of the Ninth Southeastern Conference on Combinatorics, Graph Theory, and
  Computing (Florida Atlantic Univ., Boca Raton, Fla., 1978) (1978), 29-40.
  [PDF](https://www.renyi.hu/~p_erdos/1978-36.pdf)
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos1183

/-- A family `ℱ` of subsets is monochromatic for the colouring `c` if all its members have the
same colour. -/
def IsMonochromatic {n : ℕ} (c : Finset (Fin n) → Bool) (ℱ : Finset (Finset (Fin n))) : Prop :=
  ∃ b : Bool, ∀ A ∈ ℱ, c A = b

/-- $f(n)$: the largest $m$ such that every $2$-colouring `c` of the subsets of
$\{1,\ldots,n\}$ has a monochromatic family of at least $m$ sets that is closed under unions and
intersections (`IsSublattice`).

The ground set is `Fin n`, and the subsets are `Finset (Fin n)`, the empty set included. The set
of such $m$ contains $0$ and is bounded by $2^n$, so `sSup` is a true maximum. A family with
$m \geq 1$ members is nonempty. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ c : Finset (Fin n) → Bool, ∃ ℱ : Finset (Finset (Fin n)),
    m ≤ ℱ.card ∧ IsMonochromatic c ℱ ∧ IsSublattice (ℱ : Set (Finset (Fin n)))}

/-- $F(n)$: the same as $f(n)$, except that the family is only required to be closed under
unions (`SupClosed`; the supremum of two finsets is their union). -/
noncomputable def F (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ c : Finset (Fin n) → Bool, ∃ ℱ : Finset (Finset (Fin n)),
    m ≤ ℱ.card ∧ IsMonochromatic c ℱ ∧ SupClosed (ℱ : Set (Finset (Fin n)))}

def erdos_1183.parts.i.answer : ℕ → ℝ := sorry

/--
Let $f(n)$ be maximal such that in any $2$-colouring of the subsets of $\{1,\ldots,n\}$ there is
always a monochromatic family of at least $f(n)$ sets which is closed under taking unions and
intersections. Estimate $f(n)$.

Let $F(n)$ be defined similarly, except that we only require the family be closed under taking
unions. Estimate $F(n)$. In particular, is it true that $F(n)\geq n^{\omega(n)}$ for some
$\omega(n)\to \infty$ as $n\to \infty$, and $F(n)<(1+o(1))^n$?

This is the first part, a problem of Erdős and Ulam [Er78, p. 39]. We read "estimate" as
$f(n)=\Theta(\text{answer})$.
-/
@[category research open, question value, AMS 5]
theorem erdos_1183.parts.i :
    (fun n : ℕ ↦ (f n : ℝ)) =Θ[atTop] erdos_1183.parts.i.answer := by
  sorry

def erdos_1183.parts.ii.answer : ℕ → ℝ := sorry

/--
Let $f(n)$ be maximal such that in any $2$-colouring of the subsets of $\{1,\ldots,n\}$ there is
always a monochromatic family of at least $f(n)$ sets which is closed under taking unions and
intersections. Estimate $f(n)$.

Let $F(n)$ be defined similarly, except that we only require the family be closed under taking
unions. Estimate $F(n)$. In particular, is it true that $F(n)\geq n^{\omega(n)}$ for some
$\omega(n)\to \infty$ as $n\to \infty$, and $F(n)<(1+o(1))^n$?

This is the second part. We read "estimate" as $F(n)=\Theta(\text{answer})$.
-/
@[category research open, question value, AMS 5]
theorem erdos_1183.parts.ii :
    (fun n : ℕ ↦ (F n : ℝ)) =Θ[atTop] erdos_1183.parts.ii.answer := by
  sorry

/--
Let $f(n)$ be maximal such that in any $2$-colouring of the subsets of $\{1,\ldots,n\}$ there is
always a monochromatic family of at least $f(n)$ sets which is closed under taking unions and
intersections. Estimate $f(n)$.

Let $F(n)$ be defined similarly, except that we only require the family be closed under taking
unions. Estimate $F(n)$. In particular, is it true that $F(n)\geq n^{\omega(n)}$ for some
$\omega(n)\to \infty$ as $n\to \infty$, and $F(n)<(1+o(1))^n$?

This is the third part, the "in particular" question: both conjuncts must hold. We state it as
printed in [Er78, p. 39]: $F(n) > n^c$ for every $c$ if $n > n_0(c)$, and
$F(n) < (1+\varepsilon)^n$ for every $\varepsilon > 0$ if $n > n_0(\varepsilon)$.
-/
@[category research open, question, AMS 5]
theorem erdos_1183.parts.iii :
    (∀ c : ℝ, ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ c < (F n : ℝ)) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (F n : ℝ) < (1 + ε) ^ n := by
  sorry

/--
It is trivial that $f(n)\geq \frac{n+1}{2}$, since there is a sequence of $n+1$ many nested
subsets.
-/
@[category textbook, AMS 5]
theorem erdos_1183.variants.f_ge (n : ℕ) : ((n : ℝ) + 1) / 2 ≤ (f n : ℝ) := by
  classical
  -- The chain of initial segments `C k = {i | i < k}` for `0 ≤ k ≤ n`.
  let C : ℕ → Finset (Fin n) := fun k => Finset.univ.filter fun i => (i : ℕ) < k
  have hmono : ∀ j k, j ≤ k → C j ⊆ C k := fun j k hjk i hi => by
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    omega
  have hinj : Set.InjOn C (Finset.range (n + 1) : Set ℕ) := by
    intro j hj k hk hjk
    simp only [Finset.coe_range, Set.mem_Iio] at hj hk
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have hmem : (⟨j, by omega⟩ : Fin n) ∈ C k := by simp [C, h]
      rw [← hjk] at hmem
      simp [C] at hmem
    · have hmem : (⟨k, by omega⟩ : Fin n) ∈ C j := by simp [C, h]
      rw [hjk] at hmem
      simp [C] at hmem
  -- Half of the chain, rounded up, is a lower bound for `f n`.
  have hf : (n + 2) / 2 ≤ f n := by
    unfold f
    refine le_csSup ⟨Fintype.card (Finset (Fin n)), fun m hm => ?_⟩ fun c => ?_
    · obtain ⟨ℱ, h, -⟩ := hm fun _ => true
      exact h.trans (Finset.card_le_univ ℱ)
    · set 𝒞 : Finset (Finset (Fin n)) := (Finset.range (n + 1)).image C with h𝒞
      have hcard : 𝒞.card = n + 1 := by
        rw [h𝒞, Finset.card_image_of_injOn hinj, Finset.card_range]
      have hsplit := Finset.card_filter_add_card_filter_not (s := 𝒞) (fun A => c A = true)
      -- Any subfamily of the chain is a sublattice.
      have hsub : ∀ ℱ : Finset (Finset (Fin n)), ℱ ⊆ 𝒞 →
          IsSublattice (ℱ : Set (Finset (Fin n))) := by
        intro ℱ hℱ
        have hchain : ∀ A ∈ ℱ, ∀ B ∈ ℱ, A ≤ B ∨ B ≤ A := by
          intro A hA B hB
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (hℱ hA)
          obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp (hℱ hB)
          rcases le_total j k with h | h
          · exact Or.inl (hmono j k h)
          · exact Or.inr (hmono k j h)
        refine ⟨fun A hA B hB => ?_, fun A hA B hB => ?_⟩
        · rcases hchain A hA B hB with h | h
          · rwa [sup_eq_right.mpr h]
          · rwa [sup_eq_left.mpr h]
        · rcases hchain A hA B hB with h | h
          · rwa [inf_eq_left.mpr h]
          · rwa [inf_eq_right.mpr h]
      by_cases hbig : (n + 2) / 2 ≤ (𝒞.filter fun A => c A = true).card
      · exact ⟨_, hbig, ⟨true, fun A hA => (Finset.mem_filter.mp hA).2⟩,
          hsub _ (Finset.filter_subset _ _)⟩
      · exact ⟨𝒞.filter fun A => ¬ c A = true, by omega,
          ⟨false, fun A hA => by simpa using (Finset.mem_filter.mp hA).2⟩,
          hsub _ (Finset.filter_subset _ _)⟩
  have h2 : n + 1 ≤ 2 * f n := by omega
  have h2' : (n : ℝ) + 1 ≤ 2 * (f n : ℝ) := by exact_mod_cast h2
  linarith

end Erdos1183
