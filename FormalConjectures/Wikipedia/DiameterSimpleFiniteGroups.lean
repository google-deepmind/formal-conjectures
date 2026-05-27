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

import FormalConjectures.Util.ProblemImports

/-!
# Babai–Seress Conjectures on the Diameter of Finite Groups

*References:*
- [Wikipedia, *Diameter (group theory)*](https://en.wikipedia.org/wiki/Diameter_(group_theory))
- [H. A. Helfgott and Á. Seress, *On the diameter of permutation groups*](https://arxiv.org/abs/1109.3550)
- [L. Babai and Á. Seress, *On the diameter of permutation groups*,
  European Journal of Combinatorics 13 (1992), 231–243](https://doi.org/10.1016/S0195-6698(05)80029-0)

This file contains two conjectures from the Babai–Seress paper:

- **Conjecture 1.5**: $\operatorname{diam}(A_n) < n^C$ for some absolute constant $C$,
  where $A_n$ is the alternating group on $n$ elements.

- **Conjecture 1.7**: $\operatorname{diam}(G) < (\log |G|)^C$ for some absolute constant $C$,
  where $G$ ranges over all non-abelian finite simple groups.

Conjecture 1.7 generalises Conjecture 1.5, since for $G = A_n$ we have
$\log |A_n| \approx n \log n$, so a polylogarithmic bound in $|G|$ implies a polynomial
bound in $n$.
-/

namespace BabaiSeressConjectures

/-- The (undirected) Cayley graph of a group $G$ with respect to a generating set $S$.
Two elements $g, h \in G$ are adjacent iff $g \neq h$ and
$g^{-1} h \in S$ or $h^{-1} g \in S$.

This is constructed using `SimpleGraph.fromRel`, which takes the relation
$g \sim h \iff g^{-1} h \in S$ and automatically symmetrizes it (via disjunction with the
reverse relation) and enforces irreflexivity (via $g \neq h$). In particular, this definition
effectively uses the symmetrization $S \cup S^{-1}$, so it produces a standard undirected
Cayley graph even when $S$ is not itself symmetric. -/
def cayleyGraph {G : Type*} [Group G] (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun g h => g⁻¹ * h ∈ S)

/-- The diameter of a finite group $G$, defined as the maximum diameter of the Cayley graphs
$\Gamma(G, A)$ over all generating sets $A$ of $G$.
-/
noncomputable def groupDiam (G : Type*) [Group G] [Fintype G] : ℕ :=
  sSup { d : ℕ | ∃ S : Set G, Subgroup.closure S = ⊤ ∧ (cayleyGraph S).diam = d }

/-- For the trivial group (with one element), the group diameter is zero, since
every Cayley graph has only one vertex and hence diameter zero. -/
@[category test, AMS 20]
theorem groupDiam_fin_one : groupDiam (alternatingGroup (Fin 0)) = 0 := by
  unfold groupDiam
  apply Nat.le_zero.mp
  apply csSup_le
  · exact ⟨0, Set.univ, Subgroup.closure_univ,
      SimpleGraph.diam_eq_zero.mpr (Or.inr inferInstance)⟩
  · rintro d ⟨S, _, hd⟩
    exact Nat.le_zero.mpr (hd ▸ SimpleGraph.diam_eq_zero.mpr (Or.inr inferInstance))

/-- The alternating group $A_3 \cong \mathbb{Z}/3\mathbb{Z}$ has group diameter $1$: every
non-trivial generating set produces a complete Cayley graph $K_3$, since any single non-identity
element and its inverse already reach the entire group. -/
@[category test, AMS 20]
theorem groupDiam_alternating_three : groupDiam (alternatingGroup (Fin 3)) = 1 := by
  have hnt : Nontrivial ↥(alternatingGroup (Fin 3)) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by decide)
  -- Key: for any generating set S of A₃, cayleyGraph S is the complete graph
  have key : ∀ S : Set ↥(alternatingGroup (Fin 3)),
      Subgroup.closure S = ⊤ → cayleyGraph S = ⊤ := by
    intro S hS
    rw [SimpleGraph.eq_top_iff_forall_ne_adj]
    intro u v hne
    simp only [cayleyGraph, SimpleGraph.fromRel_adj]
    refine ⟨hne, ?_⟩
    -- S must contain a non-identity element
    obtain ⟨y, hy, hy1⟩ : ∃ y ∈ S, y ≠ 1 := by
      by_contra! h
      have : Subgroup.closure S ≤ ⊥ :=
        (Subgroup.closure_le _).mpr fun x hx => Subgroup.mem_bot.mpr (h x hx)
      exact absurd (le_antisymm this bot_le |>.symm ▸ hS) bot_ne_top
    -- In A₃ (order 3), any two non-identity elements are equal or inverses
    have h3 : ∀ x y : ↥(alternatingGroup (Fin 3)), x ≠ 1 → y ≠ 1 → x = y ∨ x = y⁻¹ := by
      decide
    have hg1 : u⁻¹ * v ≠ 1 := by rwa [ne_eq, inv_mul_eq_one]
    rcases h3 (u⁻¹ * v) y hg1 hy1 with rfl | h
    · exact Or.inl hy
    · exact Or.inr (by rwa [show v⁻¹ * u = (u⁻¹ * v)⁻¹ from by group, h, inv_inv])
  -- The set of diameters equals {1}, so sSup = 1
  unfold groupDiam
  have h_eq : { d | ∃ S : Set ↥(alternatingGroup (Fin 3)),
      Subgroup.closure S = ⊤ ∧ (cayleyGraph S).diam = d } = {1} := by
    ext d; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]; constructor
    · rintro ⟨S, hS, rfl⟩; rw [key S hS, SimpleGraph.diam_top]
    · rintro rfl
      exact ⟨Set.univ, Subgroup.closure_univ, by rw [key _ Subgroup.closure_univ,
        SimpleGraph.diam_top]⟩
  rw [h_eq, csSup_singleton]

/-- The symmetric group $S_2 \cong \mathbb{Z}/2\mathbb{Z}$ has group diameter $1$: the unique
generating set $\{(01)\}$ produces the complete graph $K_2$, since the single non-identity
element and its inverse (which are equal) cover the only other vertex. -/
@[category test, AMS 20]
theorem groupDiam_perm_two : groupDiam (Equiv.Perm (Fin 2)) = 1 := by
  have hnt : Nontrivial (Equiv.Perm (Fin 2)) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by decide)
  have key : ∀ S : Set (Equiv.Perm (Fin 2)),
      Subgroup.closure S = ⊤ → cayleyGraph S = ⊤ := by
    intro S hS
    rw [SimpleGraph.eq_top_iff_forall_ne_adj]
    intro u v hne
    simp only [cayleyGraph, SimpleGraph.fromRel_adj]
    refine ⟨hne, ?_⟩
    obtain ⟨y, hy, hy1⟩ : ∃ y ∈ S, y ≠ 1 := by
      by_contra! h
      have : Subgroup.closure S ≤ ⊥ :=
        (Subgroup.closure_le _).mpr fun x hx => Subgroup.mem_bot.mpr (h x hx)
      exact absurd (le_antisymm this bot_le |>.symm ▸ hS) bot_ne_top
    have h2 : ∀ x y : Equiv.Perm (Fin 2), x ≠ 1 → y ≠ 1 → x = y ∨ x = y⁻¹ := by decide
    have hg1 : u⁻¹ * v ≠ 1 := by rwa [ne_eq, inv_mul_eq_one]
    rcases h2 (u⁻¹ * v) y hg1 hy1 with rfl | h
    · exact Or.inl hy
    · exact Or.inr (by rwa [show v⁻¹ * u = (u⁻¹ * v)⁻¹ from by group, h, inv_inv])
  unfold groupDiam
  have h_eq : { d | ∃ S : Set (Equiv.Perm (Fin 2)),
      Subgroup.closure S = ⊤ ∧ (cayleyGraph S).diam = d } = {1} := by
    ext d; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]; constructor
    · rintro ⟨S, hS, rfl⟩; rw [key S hS, SimpleGraph.diam_top]
    · rintro rfl
      exact ⟨Set.univ, Subgroup.closure_univ, by rw [key _ Subgroup.closure_univ,
        SimpleGraph.diam_top]⟩
  rw [h_eq, csSup_singleton]

/-- **Babai–Seress Conjecture (Conjecture 1.5)**: There exists an absolute constant $C$ such
that the diameter of the alternating group $A_n$ satisfies
$$\operatorname{diam}(A_n) \leq n^C.$$

*Reference:* [L. Babai and Á. Seress, *On the diameter of permutation groups*,
European Journal of Combinatorics 13 (1992), Conjecture 1.5](https://doi.org/10.1016/S0195-6698(05)80029-0) -/
@[category research open, AMS 5 20 68]
theorem babai_seress_conjecture_alternating :
    ∃ C : ℕ, ∀ n : ℕ,
    (groupDiam (alternatingGroup (Fin n)) : ℝ) ≤ (n : ℝ) ^ C := by
  sorry

/-- **Babai–Seress Conjecture (Conjecture 1.7)**: There exists an absolute constant $C$ such
that every finite simple non-abelian group $G$ satisfies
$$\operatorname{diam}(G) \leq (\log |G|)^C.$$

*Reference:* [L. Babai and Á. Seress, *On the diameter of permutation groups*,
European Journal of Combinatorics 13 (1992), Conjecture 1.7](https://doi.org/10.1016/S0195-6698(05)80029-0) -/
@[category research open, AMS 5 20 68]
theorem babai_seress_conjecture :
    ∃ C : ℕ,
    ∀ (G : Type) [Group G] [Fintype G] [IsSimpleGroup G],
    (∃ a b : G, a * b ≠ b * a) →
    (groupDiam G : ℝ) ≤ (Real.log (Fintype.card G : ℝ)) ^ C := by
  sorry

end BabaiSeressConjectures
