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
# Erdős Problem 644

*References:*
- [erdosproblems.com/644](https://www.erdosproblems.com/644)
- [EFKT92] Erdős, P. and Fon-Der-Flaass, D. and Kostochka, A. V. and Tuza, Zs., Small transversals in
  uniform hypergraphs. Siberian Adv. Math. (1992), 82-88.
-/

@[expose] public section

namespace Erdos644

open Filter Asymptotics

/-- For $r \geq 3$, the transversal bound satisfies $f(k,r) \leq 2k$. -/
@[category textbook, AMS 5]
theorem erdos_644.variants.elementary_upper_bound (k r : ℕ) (hr : 3 ≤ r) :
    Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞) := by
  classical
  unfold Hypergraph.subfamilyTransversalBound
  refine iInf_le_of_le (2 * k) (iInf_le_of_le ?_ le_rfl)
  intro V F hu hl
  have hthree {e f g : Finset V} (he : e ∈ F) (hf : f ∈ F) (hg : g ∈ F)
      (hef : Disjoint e f) (heg : Disjoint e g) (hfg : Disjoint f g) : False := by
    obtain ⟨S, hS, hhit⟩ := hl {e, f, g} (by
      simpa only [Finset.coe_insert, Finset.coe_singleton, Set.insert_subset_iff,
        Set.singleton_subset_iff] using And.intro he (And.intro hf hg))
      (Finset.card_le_three.trans hr)
    obtain ⟨x, hxS, hxe⟩ := hhit e (by simp)
    obtain ⟨y, hyS, hyf⟩ := hhit f (by simp)
    obtain ⟨z, hzS, hzg⟩ := hhit g (by simp)
    have hxy : x ≠ y := fun h ↦ Finset.disjoint_left.mp hef hxe (h.symm ▸ hyf)
    have hxz : x ≠ z := fun h ↦ Finset.disjoint_left.mp heg hxe (h.symm ▸ hzg)
    have hyz : y ≠ z := fun h ↦ Finset.disjoint_left.mp hfg hyf (h.symm ▸ hzg)
    have := Finset.card_le_card (show {x, y, z} ⊆ S by
      simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
        And.intro hxS (And.intro hyS hzS))
    simp [hxy, hxz, hyz] at this
    omega
  by_cases hF : F.Nonempty
  · obtain ⟨e, he⟩ := hF
    by_cases hall : ∀ f ∈ F, ¬ Disjoint e f
    · refine ⟨e, by rw [hu e he]; omega, ?_⟩
      intro f hf
      simpa [Finset.not_disjoint_iff] using hall f hf
    · push Not at hall
      obtain ⟨f, hf, hef⟩ := hall
      refine ⟨e ∪ f, (Finset.card_union_le e f).trans (by rw [hu e he, hu f hf]; omega), ?_⟩
      intro g hg
      by_contra h
      have heg : Disjoint e g := Finset.disjoint_left.mpr (by
        intro x hxe hxg
        exact h ⟨x, Finset.mem_union_left f hxe, hxg⟩)
      have hfg : Disjoint f g := Finset.disjoint_left.mpr (by
        intro x hxf hxg
        exact h ⟨x, Finset.mem_union_right e hxf, hxg⟩)
      exact hthree he hf hg hef heg hfg
  · exact ⟨∅, by simp, fun e he ↦ (hF ⟨e, he⟩).elim⟩

/-- The extremal parameter is finite, so its conversion to $\mathbb{N}$ loses no value. -/
@[category test, AMS 5]
theorem transversalBound_lt_top (k r : ℕ) (hr : 3 ≤ r) :
    Hypergraph.subfamilyTransversalBound k r 2 < ⊤ :=
  lt_of_le_of_lt (erdos_644.variants.elementary_upper_bound k r hr)
    (ENat.natCast_lt_top (2 * k))

/--
Let $f(k,r)$ be minimal such that if $A_1,A_2,\ldots$ is a family of sets, all of size $k$, such
that for every collection of $r$ of the $A_is$ there is some pair $\{x,y\}$ which intersects all of
the $A_j$, then there is some set of size $f(k,r)$ which intersects all of the sets $A_i$. Is it
true that
$$f(k,7)=(1+o(1))\frac{3}{4}k?$$
-/
@[category research open, question, AMS 5]
theorem erdos_644.parts.i :
    (fun k ↦ ((Hypergraph.subfamilyTransversalBound k 7 2).toNat : ℝ)) ~[atTop]
      (fun k ↦ (3 / 4 : ℝ) * k) := by
  sorry

/--
Is it true that for any $r\geq 3$ there exists some constant $c_r$ such that
$$f(k,r)=(1+o(1))c_rk?$$
-/
@[category research open, question, AMS 5]
theorem erdos_644.parts.ii :
    ∀ r : ℕ, 3 ≤ r → ∃ c : ℝ, 0 < c ∧
    (fun k ↦ ((Hypergraph.subfamilyTransversalBound k r 2).toNat : ℝ)) ~[atTop]
      (fun k ↦ c * k) := by
  sorry

end Erdos644
