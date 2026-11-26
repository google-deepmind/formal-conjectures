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
# The finitistic dimension conjecture

The *little finitistic dimension* of a ring `A` is the supremum of the projective dimensions of
the finitely generated `A`-modules of finite projective dimension; the *big finitistic dimension*
allows all modules. The finitistic dimension conjecture, publicised by Bass [Ba60], asserts that
the little finitistic dimension of every finite-dimensional algebra over a field is finite.
Huisgen-Zimmermann showed that the little and big dimensions can differ [HZ92]. The conjecture is
known for monomial algebras [GKK91], for algebras with radical cube zero [GH91], and for algebras
of representation dimension at most three [IT05].

*References:*
- [Ba60] H. Bass, *Finitistic dimension and a homological generalization of semi-primary rings*,
  Trans. Amer. Math. Soc. 95 (1960), 466–488.
- [GH91] E. L. Green and B. Zimmermann Huisgen, *Finitistic dimension of Artinian rings with
  vanishing radical cube*, Math. Z. 206 (1991), 505–526.
- [GKK91] E. L. Green, E. E. Kirkman and J. Kuzmanovich, *Finitistic dimensions of finite
  dimensional monomial algebras*, J. Algebra 136 (1991), 37–50.
- [HZ92] B. Zimmermann Huisgen, *Homological domino effects and the first finitistic dimension
  conjecture*, Invent. Math. 108 (1992), 369–383.
- [IT05] K. Igusa and G. Todorov, *On the finitistic global dimension conjecture for Artin
  algebras*, in *Representations of algebras and related topics*, Fields Inst. Commun. 45,
  Amer. Math. Soc. (2005), 201–204.
- [OAI26] OpenAI, *An algebra of infinite little finitistic dimension*. OpenAI Math Release
  preprint (2026).
  https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf
-/

@[expose] public section

open CategoryTheory

namespace FinitisticDimensionConjecture

universe u

/-- The little finitistic dimension of `A`: the supremum of `projectiveDimension M` over the
finitely generated `A`-modules `M` of finite projective dimension. -/
noncomputable def littleFinitisticDimension (A : Type u) [Ring A] : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{u} A) (_ : Module.Finite A M) (_ : projectiveDimension M < ⊤),
    projectiveDimension M

/-- The big finitistic dimension of `A`: the supremum of `projectiveDimension M` over all
`A`-modules `M` of finite projective dimension. -/
noncomputable def bigFinitisticDimension (A : Type u) [Ring A] : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{u} A) (_ : projectiveDimension M < ⊤), projectiveDimension M

/--
**The finitistic dimension conjecture is false.** Not every finite-dimensional algebra over a
field has finite little finitistic dimension.

This was proved by an internal OpenAI model in September 2026 [OAI26], with a
finite-dimensional complex algebra that has, for every `m ≥ 1`, a finitely generated module of
finite projective dimension at least `2m - 2`.
-/
@[category research solved, AMS 16 18]
theorem finitistic_dimension_conjecture : ¬ ∀ (k : Type) [Field k] (A : Type) [Ring A]
    [Algebra k A] [FiniteDimensional k A], littleFinitisticDimension A < ⊤ := by
  sorry

/-- The same algebra has infinite big finitistic dimension, so the big version of the
conjecture fails too [OAI26]. -/
@[category research solved, AMS 16 18]
theorem finitistic_dimension_conjecture.variants.big : ¬ ∀ (k : Type) [Field k] (A : Type)
    [Ring A] [Algebra k A] [FiniteDimensional k A], bigFinitisticDimension A < ⊤ := by
  sorry

/-- **Huisgen-Zimmermann.** The little and big finitistic dimensions of a finite-dimensional
algebra can differ [HZ92]. -/
@[category research solved, AMS 16 18]
theorem finitistic_dimension_conjecture.variants.little_lt_big : ∃ (k : Type) (_ : Field k)
    (A : Type) (_ : Ring A) (_ : Algebra k A), FiniteDimensional k A ∧
      littleFinitisticDimension A < bigFinitisticDimension A := by
  sorry

/-- The little finitistic dimension is at most the big one. -/
@[category API, AMS 16 18]
theorem littleFinitisticDimension_le_big (A : Type u) [Ring A] :
    littleFinitisticDimension A ≤ bigFinitisticDimension A :=
  iSup_le fun M => iSup_le fun _ => iSup_le fun h => le_iSup₂_of_le M h le_rfl

/-- The little counterexample is also a big counterexample. -/
@[category test, AMS 16 18]
theorem big_of_finitistic_dimension_conjecture
    (h : type_of% finitistic_dimension_conjecture) :
    type_of% finitistic_dimension_conjecture.variants.big :=
  fun hbig => h fun k _ A _ _ _ => (littleFinitisticDimension_le_big A).trans_lt (hbig k A)

end FinitisticDimensionConjecture
