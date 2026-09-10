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
over a field of characteristic zero admits one. In positive characteristic this is known over a
perfect field in dimension at most three, and is open from dimension four on. Perfectness of $k$
cannot be dropped from the statement in this form: over an imperfect field it fails already in
dimension zero, for the reason recorded in the docstring of `resolution_of_singularities` below.
Over an arbitrary field one asks instead that $Y$ be regular.

We also state resolution by a finite sequence of blowups in smooth centers contained
in the successive singular loci, and its refinement by requiring normal flatness along
each center. These are separate conjectures in positive characteristic. The theorem
in dimension at most three below concerns proper birational resolution; it does not
assert resolution by permissible blowups.

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Resolution_of_singularities)
* [Hir1964] H. Hironaka, Resolution of singularities of an algebraic variety over a field of
  characteristic zero, [I](https://doi.org/10.2307/1970486) and
  [II](https://doi.org/10.2307/1970547), Ann. of Math. 79 (1964), 109--203 and 205--326.
* [Kol2007] J. Kollár, [Resolution of singularities -- Seattle
  lecture](https://arxiv.org/abs/math/0508332), Theorem 36.
* [Wlo2016] J. Włodarczyk, [Singular implicit and inverse function theorems.
  Strong resolution with normally flat centers](https://arxiv.org/abs/1510.03480),
  Theorem 8.1.1.
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

/-- A smooth closed center over `S` containing no smooth point of `X` over `S`.
For a locally finitely presented structure morphism, the stalk condition says that
the support of the center is disjoint from `sX.smoothLocus`. -/
def Scheme.IsSmoothBlowupCenter {S X : Scheme.{u}} (sX : X ⟶ S)
    (I : X.IdealSheafData) : Prop :=
  Smooth (I.subschemeι ≫ sX) ∧
    ∀ x ∈ I.support, ¬ (sX.stalkMap x).hom.FormallySmooth

/-- A smooth center in the non-smooth locus along which the ambient scheme is
normally flat. No exceptional-divisor boundary is included in this definition. -/
def Scheme.IsPermissibleBlowupCenter {S X : Scheme.{u}} (sX : X ⟶ S)
    (I : X.IdealSheafData) : Prop :=
  Scheme.IsSmoothBlowupCenter sX I ∧ I.IsNormallyFlat

/-- For a locally finitely presented morphism, the center condition is exactly
smoothness of the center and disjointness from the smooth locus of the ambient scheme. -/
@[category API, AMS 14]
theorem Scheme.isSmoothBlowupCenter_iff {S X : Scheme.{u}} (sX : X ⟶ S)
    [LocallyOfFinitePresentation sX] (I : X.IdealSheafData) :
    Scheme.IsSmoothBlowupCenter sX I ↔ Smooth (I.subschemeι ≫ sX) ∧
      Disjoint (I.support : Set X) (sX.smoothLocus : Set X) := by
  rw [Set.disjoint_left]
  exact ⟨fun h => ⟨h.1, fun x hx hs => h.2 x hx hs⟩,
    fun h => ⟨h.1, fun x hx hs => h.2 hx hs⟩⟩

/-- A smooth ambient scheme has no nonempty center satisfying the singular-locus condition. -/
@[category test, AMS 14]
theorem Scheme.IsSmoothBlowupCenter.eq_top {S X : Scheme.{u}} {sX : X ⟶ S}
    [Smooth sX] {I : X.IdealSheafData} (hI : Scheme.IsSmoothBlowupCenter sX I) : I = ⊤ := by
  apply I.support_eq_bot_iff.mp
  have h := (Scheme.isSmoothBlowupCenter_iff sX I).mp hI |>.2
  simpa [sX.smoothLocus_eq_top] using h

/-- A resolution whose morphism is a finite composite of blowups with centers
satisfying `P`. The composite is required to be a proper birational resolution. -/
def Scheme.HasResolutionByBlowups {S X : Scheme.{u}} (sX : X ⟶ S)
    (P : ∀ X : Scheme.{u}, (X ⟶ S) → X.IdealSheafData → Prop) : Prop :=
  ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsIntegral Y ∧ IsProper f ∧ Smooth (f ≫ sX) ∧
    Scheme.BirationalOver f (𝟙 X) ∧ Scheme.BlowupSequence P sX f

/-- Resolution by smooth centers contained in the successive non-smooth loci. -/
def Scheme.HasResolutionBySmoothBlowups {S X : Scheme.{u}} (sX : X ⟶ S) : Prop :=
  Scheme.HasResolutionByBlowups sX (fun _ s I => Scheme.IsSmoothBlowupCenter s I)

/-- Resolution by smooth centers in the successive non-smooth loci, with normal
flatness along every center. -/
def Scheme.HasResolutionByPermissibleBlowups {S X : Scheme.{u}} (sX : X ⟶ S) : Prop :=
  Scheme.HasResolutionByBlowups sX (fun _ s I => Scheme.IsPermissibleBlowupCenter s I)

/-- Resolution by a prescribed class of blowups gives a proper birational resolution. -/
@[category API, AMS 14]
theorem Scheme.HasResolutionByBlowups.hasResolution {S X : Scheme.{u}} {sX : X ⟶ S}
    {P : ∀ X : Scheme.{u}, (X ⟶ S) → X.IdealSheafData → Prop}
    (h : Scheme.HasResolutionByBlowups sX P) : Scheme.HasResolution sX := by
  obtain ⟨Y, f, hY, hf, hs, hb, _⟩ := h
  exact ⟨Y, f, hY, hf, hs, hb⟩

/-- A resolution by blowups remains one after weakening the conditions on centers. -/
@[category API, AMS 14]
theorem Scheme.HasResolutionByBlowups.mono {S X : Scheme.{u}} {sX : X ⟶ S}
    {P Q : ∀ X : Scheme.{u}, (X ⟶ S) → X.IdealSheafData → Prop}
    (h : Scheme.HasResolutionByBlowups sX P)
    (hPQ : ∀ (X : Scheme.{u}) (sX : X ⟶ S) (I : X.IdealSheafData),
      P X sX I → Q X sX I) : Scheme.HasResolutionByBlowups sX Q := by
  obtain ⟨Y, f, hY, hf, hs, hb, hseq⟩ := h
  exact ⟨Y, f, hY, hf, hs, hb, hseq.mono hPQ⟩

/-- Forgetting normal flatness gives a resolution by smooth-center blowups. -/
@[category API, AMS 14]
theorem Scheme.HasResolutionByPermissibleBlowups.hasResolutionBySmoothBlowups
    {S X : Scheme.{u}} {sX : X ⟶ S} (h : Scheme.HasResolutionByPermissibleBlowups sX) :
    Scheme.HasResolutionBySmoothBlowups sX :=
  Scheme.HasResolutionByBlowups.mono h (fun _ _ _ hI => hI.1)

/-- A resolution by smooth-center blowups is a proper birational resolution. -/
@[category API, AMS 14]
theorem Scheme.HasResolutionBySmoothBlowups.hasResolution {S X : Scheme.{u}}
    {sX : X ⟶ S} (h : Scheme.HasResolutionBySmoothBlowups sX) :
    Scheme.HasResolution sX :=
  Scheme.HasResolutionByBlowups.hasResolution h

/-- A smooth scheme resolves by the sequence of length zero for any center condition. -/
@[category test, AMS 14]
theorem Scheme.hasResolutionByBlowups_of_smooth {S X : Scheme.{u}} (sX : X ⟶ S)
    [IsIntegral X] [Smooth sX]
    (P : ∀ X : Scheme.{u}, (X ⟶ S) → X.IdealSheafData → Prop) :
    Scheme.HasResolutionByBlowups sX P :=
  ⟨X, 𝟙 X, ‹_›, inferInstance, by rwa [Category.id_comp], .refl _, .nil sX⟩

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
**Resolution by smooth-center blowups in positive characteristic.** Every integral
separated scheme of finite type over a perfect field of characteristic $p > 0$ admits
a resolution by a finite sequence of blowups in smooth centers contained in the
successive singular loci. See [Hau2010].
-/
@[category research open, AMS 14]
theorem resolution_of_singularities_by_smooth_blowups (k : Type u) [Field k]
    [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsSeparated sX] :
    Scheme.HasResolutionBySmoothBlowups sX := by
  sorry

/--
**Resolution by permissible blowups in positive characteristic.** In addition to
smooth centers in the successive singular loci, require normal flatness along each
center. This is the Hironaka-permissible refinement, without a prescribed boundary;
see [CP2019], Remark 1.4. The permissible-blowup problem remains open even in
dimension three, unlike the proper birational resolution theorem stated below.
-/
@[category research open, AMS 14]
theorem resolution_of_singularities_by_permissible_blowups (k : Type u) [Field k]
    [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsSeparated sX] :
    Scheme.HasResolutionByPermissibleBlowups sX := by
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

/-- Hironaka's theorem gives resolution by smooth-center blowups in characteristic
zero, with centers in the successive singular loci; see [Hir1964] and [Wlo2016],
Theorem 8.1.1. Stop the sequence when the variety first becomes smooth. -/
@[category research solved, AMS 14]
theorem resolution_of_singularities_by_smooth_blowups_of_charZero (k : Type u)
    [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] [IsSeparated sX] :
    Scheme.HasResolutionBySmoothBlowups sX := by
  sorry

/-- Hironaka's characteristic-zero resolution can be obtained with normal flatness
along the smooth centers in the successive singular loci; see [Hir1964] and
[Wlo2016], Theorem 8.1.1(a)--(c). Stop when the variety first becomes smooth,
before the further blowups that arrange the exceptional divisor. -/
@[category research solved, AMS 14]
theorem resolution_of_singularities_by_permissible_blowups_of_charZero (k : Type u)
    [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] [IsSeparated sX] :
    Scheme.HasResolutionByPermissibleBlowups sX := by
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
