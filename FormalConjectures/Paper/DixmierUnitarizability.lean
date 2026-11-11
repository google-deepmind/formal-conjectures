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
# Dixmier's unitarizability problem

A discrete group is *unitarizable* if every uniformly bounded representation of it on a complex
Hilbert space is similar to a unitary representation. Day and Dixmier proved that amenable groups
are unitarizable [Da50, Di50], and Dixmier asked whether the converse holds [Di50, §5, p. 221].
Groups containing a nonabelian free subgroup are not unitarizable [PS86, Pi05], and Monod and
Ozawa found further non-unitarizable groups among lamplighters and Burnside groups [MO10].

*References:*
- [Da50] M. M. Day, *Means for the bounded functions and ergodicity of the bounded
  representations of semi-groups*, Trans. Amer. Math. Soc. 69 (1950), 276–291.
- [Di50] J. Dixmier, *Les moyennes invariantes dans les semi-groupes et leurs applications*,
  Acta Sci. Math. (Szeged) 12 (1950), 213–227.
- [MO10] N. Monod and N. Ozawa, *The Dixmier problem, lamplighters and Burnside groups*,
  J. Funct. Anal. 258 (2010), 255–259.
- [Pi05] G. Pisier, *Are unitarizable groups amenable?*, in *Infinite groups: geometric,
  combinatorial and dynamical aspects*, Progr. Math., Birkhäuser (2005), 323–362.
- [PS86] T. Pytlik and R. Szwarc, *An analytic family of uniformly bounded representations of
  free groups*, Acta Math. 157 (1986), 287–309.
- [OAI26] OpenAI, *Unitarizability implies amenability for discrete groups*. OpenAI Math
  Release preprint (2026).
  https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/Unitarizability-Implies-Amenability-for-Countable-Groups-September-23-2026/paper.pdf
-/

@[expose] public section

namespace DixmierUnitarizability

open scoped BoundedContinuousFunction

universe u v

/-- Left translation `x ↦ f (g⁻¹ * x)` of a bounded function on a discrete group. -/
noncomputable def leftTranslate {G : Type*} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (g : G) (f : G →ᵇ ℂ) : G →ᵇ ℂ :=
  f.compContinuous ⟨fun x => g⁻¹ * x, continuous_of_discreteTopology⟩

/-- A discrete group is *amenable* if it has a left-invariant mean: a positive linear functional
on bounded functions, equal to `1` on the constant function `1` and invariant under left
translation. -/
def Amenable (G : Type*) [Group G] [TopologicalSpace G] [DiscreteTopology G] : Prop :=
  ∃ m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ,
    m (BoundedContinuousFunction.const G 1) = 1 ∧
    (∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) ∧
    ∀ (g : G) (f : G →ᵇ ℂ), m (leftTranslate g f) = m f

/-- A representation `π` of `G` by bounded operators is *similar to a unitary representation*
if some invertible `S` makes every `S π(g) S⁻¹` an isometry (hence unitary, since `π(g)` is
invertible). -/
def SimilarToUnitary {G : Type*} [Group G] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (π : G →* (H →L[ℂ] H)) : Prop :=
  ∃ S : H ≃L[ℂ] H, ∀ (g : G) (x : H), ‖S (π g (S.symm x))‖ = ‖x‖

/-- `G` is *unitarizable* if every uniformly bounded representation of `G` on a complex Hilbert
space in the universe `v` is similar to a unitary representation. The statements below take `v`
to be the universe of `G`, which contains `ℓ²(G)`. -/
def Unitarizable (G : Type u) [Group G] : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G →* (H →L[ℂ] H)), (∃ C : ℝ, ∀ g, ‖π g‖ ≤ C) → SimilarToUnitary π

/--
**Dixmier's unitarizability problem.** Every unitarizable discrete group is amenable.

This was proved by an internal OpenAI model in September 2026 [OAI26].
-/
@[category research solved, AMS 20 22 43]
theorem dixmier_unitarizability : ∀ (G : Type u) [Group G] [TopologicalSpace G]
    [DiscreteTopology G], Unitarizable.{u, u} G → Amenable G := by
  sorry

/-- **Day, Dixmier.** Every amenable discrete group is unitarizable [Da50, Di50]. -/
@[category research solved, AMS 20 22 43]
theorem dixmier_unitarizability.variants.amenable : ∀ (G : Type u) [Group G]
    [TopologicalSpace G] [DiscreteTopology G], Amenable G → Unitarizable.{u, u} G := by
  sorry

/-- A group containing a free group on two generators is not unitarizable: the free group has
uniformly bounded representations that are not similar to unitary ones (for instance [PS86]),
and these induce up to the whole group [Pi05]. -/
@[category research solved, AMS 20 22 43]
theorem dixmier_unitarizability.variants.free_subgroup : ∀ (G : Type u) [Group G],
    (∃ f : FreeGroup (Fin 2) →* G, Function.Injective f) → ¬ Unitarizable.{u, u} G := by
  sorry

/-- Sanity check: a representation by isometries is similar to a unitary one, with `S = id`. -/
@[category test, AMS 20 22]
theorem similarToUnitary_of_isometry {G H : Type*} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (π : G →* (H →L[ℂ] H)) (hπ : ∀ g x, ‖π g x‖ = ‖x‖) :
    SimilarToUnitary π :=
  ⟨ContinuousLinearEquiv.refl ℂ H, fun g x => by simpa using hπ g x⟩

/-- Sanity check: a finite group is amenable, with the uniform average as the mean. -/
@[category test, AMS 20 43]
theorem amenable_of_finite (G : Type*) [Group G] [Finite G] [TopologicalSpace G]
    [DiscreteTopology G] : Amenable G := by
  classical
  cases nonempty_fintype G
  let c : ℝ := (Fintype.card G : ℝ)⁻¹
  let m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => (c : ℂ) * ∑ x, f x
      map_add' := fun f g => by simp [Finset.sum_add_distrib, mul_add]
      map_smul' := fun a f => by
        simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul, RingHom.id_apply,
          ← Finset.mul_sum]
        ring }
  refine ⟨m, ?_, fun f hf => ?_, fun g f => ?_⟩
  · simp [m, c, Fintype.card_ne_zero]
  · simp only [m, LinearMap.coe_mk, AddHom.coe_mk, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul, Complex.re_sum, Complex.im_sum]
    refine ⟨mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => (hf x).1), ?_⟩
    simp [fun x => (hf x).2]
  · simp only [m, LinearMap.coe_mk, AddHom.coe_mk, leftTranslate,
      BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun x => rfl

end DixmierUnitarizability
