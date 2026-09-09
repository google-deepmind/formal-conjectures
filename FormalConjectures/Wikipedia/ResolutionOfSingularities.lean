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
# Resolution of singularities

A variety $X$ over a field $k$ admits a resolution of singularities if there is a smooth
$k$-variety $Y$ and a proper birational morphism $Y \to X$. Hironaka proved that every variety
over a field of characteristic zero admits one. In positive characteristic this is known only in
dimension at most three, and is open in general.

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Resolution_of_singularities)
* [Hir1964] H. Hironaka, Resolution of singularities of an algebraic variety over a field of
  characteristic zero, [I](https://doi.org/10.2307/1970486) and
  [II](https://doi.org/10.2307/1970547), Ann. of Math. 79 (1964), 109--203 and 205--326.
* [Kol2007] J. Kollár, [Resolution of singularities -- Seattle
  lecture](https://arxiv.org/abs/math/0508332), Theorem 36.
* [Hau2010] H. Hauser, [On the problem of resolution of singularities in positive characteristic
  (or: a proof we are still waiting for)](https://doi.org/10.1090/S0273-0979-09-01274-9),
  Bull. Amer. Math. Soc. 47 (2010), 1--30.
* [Lip1978] J. Lipman, [Desingularization of two-dimensional
  schemes](https://doi.org/10.2307/1971141), Ann. of Math. 107 (1978), 151--207.
* [CP2008] V. Cossart and O. Piltant, [Resolution of singularities of threefolds in positive
  characteristic I](https://doi.org/10.1016/j.jalgebra.2008.03.032), J. Algebra 320 (2008),
  1051--1082.
* [CP2009] V. Cossart and O. Piltant, [Resolution of singularities of threefolds in positive
  characteristic II](https://doi.org/10.1016/j.jalgebra.2008.11.030), J. Algebra 321 (2009),
  1836--1976.
* [CP2019] V. Cossart and O. Piltant, [Resolution of singularities of arithmetical
  threefolds](https://doi.org/10.1016/j.jalgebra.2019.02.017), J. Algebra 529 (2019), 268--535.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry

/--
A scheme `X` over a base `S` with structure morphism `sX : X ⟶ S` admits a *resolution of
singularities* if there is an integral scheme `Y`, smooth over `S`, together with a proper
morphism `f : Y ⟶ X` that is birational over `X`, i.e. that restricts to an isomorphism between
dense open subschemes of `Y` and of `X`.
-/
def Scheme.HasResolution {S X : Scheme.{u}} (sX : X ⟶ S) : Prop :=
  ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
    IsIntegral Y ∧ IsProper f ∧ Smooth (f ≫ sX) ∧ Scheme.BirationalOver f (𝟙 X)

/-- A scheme that is already smooth over the base is its own resolution. -/
@[category test, AMS 14]
theorem Scheme.hasResolution_of_smooth {S X : Scheme.{u}} (sX : X ⟶ S) [IsIntegral X]
    [Smooth sX] : Scheme.HasResolution sX :=
  ⟨X, 𝟙 X, ‹_›, inferInstance, by rwa [Category.id_comp], .refl _⟩

/--
A proper birational morphism onto a scheme is surjective. In particular a resolution of
singularities is onto, which is what rules out the inclusion of the smooth locus of `X` as a
trivial solution.
-/
@[category API, AMS 14]
theorem Scheme.surjective_of_birationalOver_id {X Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f]
    (hf : Scheme.BirationalOver f (𝟙 X)) : Function.Surjective f.base := by
  obtain ⟨g, hg⟩ := hf
  have hfg : ∀ u, f.base (g.source.ι.base u) = g.target.ι.base (g.iso.hom.base u) := fun u => by
    simpa using (congrArg (fun m : (g.source : Scheme) ⟶ X => m.base u) hg).symm
  have hdense : Dense (Set.range f.base) := by
    refine g.dense_target.mono ?_
    rintro x hx
    obtain ⟨u, hu⟩ := g.iso.hom.homeomorph.surjective ⟨x, hx⟩
    exact ⟨g.source.ι.base u, by rw [hfg u]; exact congrArg Subtype.val hu⟩
  rw [← Set.range_eq_univ, ← f.isClosedMap.isClosed_range.closure_eq, hdense.closure_eq]

/--
**Resolution of singularities in positive characteristic.**
Let $k$ be a perfect field of characteristic $p > 0$ and let $X$ be an integral scheme that is
separated and of finite type over $k$. Then there is an integral scheme $Y$ that is smooth over
$k$ together with a proper birational morphism $Y \to X$.

This is open from dimension four on; see [Hau2010]. Perfectness of $k$ is needed for the
conclusion as stated: if $k$ is imperfect and $a \in k \setminus k^p$, then
$\operatorname{Spec} k(a^{1/p})$ satisfies all the hypotheses, but every scheme birational to
it has function field $k(a^{1/p})$, which is inseparable over $k$, so none of them is smooth
over $k$.
-/
@[category research open, AMS 14]
theorem resolution_of_singularities (k : Type u) [Field k] [PerfectField k] (p : ℕ)
    [Fact p.Prime] [CharP k p] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] [IsSeparated sX] :
    Scheme.HasResolution sX := by
  sorry

/--
**Hironaka's theorem.** Every integral scheme that is separated and of finite type over a field
of characteristic zero admits a resolution of singularities. This is the main theorem of
[Hir1964]; see [Kol2007], Theorem 36, for a statement in the generality used here.
-/
@[category research solved, AMS 14]
theorem resolution_of_singularities_of_charZero (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsSeparated sX] :
    Scheme.HasResolution sX := by
  sorry

/--
Resolution of singularities holds in dimension at most three over any perfect field. In
characteristic zero this is [Hir1964]. In positive characteristic, dimension at most two is
[Lip1978] and dimension three is due to Cossart and Piltant: [CP2008] and [CP2009] prove it for
quasi-projective varieties over a field that is differentially finite over a perfect subfield,
and [CP2019], Theorem 1.1, removes both restrictions, resolving every reduced separated
Noetherian quasi-excellent scheme of dimension at most three in any characteristic. That theorem
gives an everywhere regular source, which over a perfect field is the same as a smooth one. The
problem is open in positive characteristic from dimension four on.
-/
@[category research solved, AMS 14]
theorem resolution_of_singularities_of_topologicalKrullDim_le_three (k : Type u) [Field k]
    [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] [IsSeparated sX]
    (hX : topologicalKrullDim X ≤ 3) :
    Scheme.HasResolution sX := by
  sorry

end AlgebraicGeometry
