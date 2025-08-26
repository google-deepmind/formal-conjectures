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

import FormalConjectures.Util.ProblemImports

/-!
# Gromov's theorem on groups of polynomial growth

*Reference:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Gromov%27s_theorem_on_groups_of_polynomial_growth)
-/

/-
Note: this was obtained in work with Kasia Jankiewicz and Catherine Pfaff, and using
Claude 4.0 Sonnet: https://claude.ai/share/918bb269-bd28-4c09-b84e-cab579c836e8
-/

namespace GromovPolynomialGrowth

/-- The `CayleyBall` is the ball of radius `n` in the Cayley graph of a group `G` with generating
    set `S`. -/
def CayleyBall {G : Type*} [Group G] (S : Set G) (n : ℕ) : Set G :=
  {g : G | ∃ (l : List G), l.length ≤ n ∧ (∀ s ∈ l, s ∈ S ∨ s⁻¹ ∈ S) ∧ l.prod = g}

/-- The `GrowthFunction` of a group `G` with respect to a set `S` counts the number
    of group elements that can be reached by words of length at most `n` in `S`. -/
noncomputable def GrowthFunction {G : Type*} [Group G] (S : Set G) (n : ℕ) : ℕ :=
  (CayleyBall S n).ncard

-- Basic properties of CayleyBall and GrowthFunction (Claude generated statements, human proofs)

/-- The identity is always in the Cayley ball of radius n for any n ≥ 0. -/
@[category API, AMS 20]
lemma one_mem_CayleyBall {G : Type*} [Group G] (S : Set G) (n : ℕ) :
    1 ∈ CayleyBall S n := by
  simp only [CayleyBall, Set.mem_setOf_eq]
  use ∅
  simp

/-- The Cayley ball is monotonic in radius. -/
@[category API, AMS 20]
lemma CayleyBall_monotone {G : Type*} [Group G] (S : Set G) {m n : ℕ} (h : m ≤ n) :
    CayleyBall S m ⊆ CayleyBall S n := by
  simp only [CayleyBall, Set.setOf_subset_setOf, forall_exists_index, and_imp]
  exact fun g l lLength LSubS lProdG ↦ ⟨l, by linarith, LSubS, lProdG⟩

/-- Closure property: if g, h ∈ CayleyBall S m, CayleyBall S n respectively,
    then gh ∈ CayleyBall S (m + n). -/
@[category API, AMS 20]
lemma CayleyBall_mul {G : Type*} [Group G] (S : Set G) {g h : G} {m n : ℕ}
    (hg : g ∈ CayleyBall S m) (hh : h ∈ CayleyBall S n) :
    g * h ∈ CayleyBall S (m + n) := by
  simp only [CayleyBall, Set.mem_setOf_eq] at hg hh ⊢
  obtain ⟨lg, lgLength, lgSubS, lgProd⟩ := hg
  obtain ⟨lh, lhLength, lhSubS, lhProd⟩ := hh
  refine ⟨lg ++ lh, ?_, ?_, by simp [lhProd, lgProd]⟩
  · simp only [List.length_append]
    linarith
  · intro s sIn
    simp only [List.mem_append] at sIn
    cases sIn with
    | inl h => simp [lgSubS s h]
    | inr h => simp [lhSubS s h]

/-- If `g ∈ CayleyBall S n`, then `g⁻¹ ∈ CayleyBall S n`. -/
@[category API, AMS 20]
lemma CayleyBall_inv {G : Type*} [Group G] (S : Set G) {g : G} {n : ℕ}
    (hg : g ∈ CayleyBall S n) :
    g⁻¹ ∈ CayleyBall S n := by
  simp only [CayleyBall, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨lg, lgLength, lgSubS, lgProd⟩ := hg
  refine ⟨lg.reverse.map (·⁻¹), by simp [lgLength], ?_,
    by simp [List.prod_inv_reverse, lgProd.symm]⟩
  intro s sIn
  simp only [List.map_reverse, List.mem_reverse, List.mem_map, inv_involutive,
    Function.Involutive.exists_mem_and_apply_eq_iff] at sIn
  have := lgSubS s⁻¹ sIn
  simp only [inv_inv] at this
  exact this.symm

/-- A group `HasPolynomialGrowth` if there exists a finite generating set such that
    the growth function is bounded above by a polynomial. -/
def HasPolynomialGrowth (G : Type*) [Group G] : Prop :=
  ∃ (S : Set G), Set.Finite S ∧ Subgroup.closure S = ⊤ ∧
    ∃ (C : ℝ) (d : ℕ), C > 0 ∧
    ∀ n : ℕ, (GrowthFunction S n : ℝ) ≤ C * (n : ℝ) ^ d

/-- **Gromov's Polynomial Growth Theorem** : A finitely generated group has
    polynomial growth if and only if it is virtually nilpotent. -/
@[category research solved, AMS 20]
theorem GromovPolynomialGrowthTheorem (G : Type*) [Group G] [Group.FG G] :
    HasPolynomialGrowth G ↔ Group.IsVirtuallyNilpotent G := by
  sorry

end GromovPolynomialGrowth
