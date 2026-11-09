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
# Infinite finitely presented simple amenable groups

Is there an infinite group that is finitely presented, simple and amenable? Juschenko and Monod
gave the first infinite finitely generated simple amenable groups [JM13]; the finitely presented
question is recorded by Button [Bu10, p. 729] and raised again in [JM13, p. 776].

*References:*
- [Bu10] J. O. Button, *Largeness of LERF and 1-relator groups*, Groups Geom. Dyn. 4 (2010),
  709–738.
- [JM13] K. Juschenko and N. Monod, *Cantor systems, piecewise translations and simple
  amenable groups*, Ann. of Math. 178 (2013), 775–787.
- [OAI26] OpenAI, *An infinite finitely presented simple amenable group*. OpenAI Math Release
  preprint (2026).
  https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf
-/

@[expose] public section

open scoped symmDiff

namespace SimpleAmenableGroup

/-- A discrete group is *amenable* if it satisfies the Følner condition: for every finite
`K ⊆ G` and every `ε > 0` there is a nonempty finite `D ⊆ G` with `|gD ∆ D| < ε |D|` for all
`g ∈ K`. -/
noncomputable def FolnerAmenable (G : Type*) [Group G] : Prop := by
  classical
  exact ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
    ∃ D : Finset G, D.Nonempty ∧ ∀ g ∈ K,
      (((D.image (fun d => g * d)) ∆ D).card : ℝ) < ε * D.card

/--
**There is an infinite finitely presented simple amenable group.**

This was proved by an internal OpenAI model in September 2026 [OAI26]. The group is an
alternating subgroup of a polygon exchange group.
-/
@[category research solved, AMS 20 43]
theorem simple_amenable_group : ∃ (G : Type) (_ : Group G),
    Infinite G ∧ Group.IsFinitelyPresented G ∧ IsSimpleGroup G ∧ FolnerAmenable G := by
  sorry

/-- **Juschenko–Monod.** There is an infinite finitely generated simple amenable group: the
derived subgroup of the topological full group of a minimal subshift [JM13, Corollary B]. -/
@[category research solved, AMS 20 43]
theorem simple_amenable_group.variants.finitely_generated : ∃ (G : Type) (_ : Group G),
    Infinite G ∧ Group.FG G ∧ IsSimpleGroup G ∧ FolnerAmenable G := by
  sorry

/-- A finitely presented example is in particular finitely generated. -/
@[category test, AMS 20 43]
theorem finitely_generated_of_simple_amenable_group (h : type_of% simple_amenable_group) :
    type_of% simple_amenable_group.variants.finitely_generated := by
  obtain ⟨G, _, hinf, ⟨n, φ, hφ, -⟩, hsimple, hamen⟩ := h
  exact ⟨G, inferInstance, hinf, Group.fg_of_surjective hφ, hsimple, hamen⟩

end SimpleAmenableGroup
