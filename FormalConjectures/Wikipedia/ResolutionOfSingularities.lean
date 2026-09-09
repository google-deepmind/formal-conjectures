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
* [Hau2010] H. Hauser, [On the problem of resolution of singularities in positive characteristic
  (or: a proof we are still waiting for)](https://doi.org/10.1090/S0273-0979-09-01274-9),
  Bull. Amer. Math. Soc. 47 (2010), 1--30.
* [CP2008] V. Cossart and O. Piltant, [Resolution of singularities of threefolds in positive
  characteristic I](https://doi.org/10.1016/j.jalgebra.2008.03.032), J. Algebra 320 (2008),
  1051--1082.
* [CP2009] V. Cossart and O. Piltant, [Resolution of singularities of threefolds in positive
  characteristic II](https://doi.org/10.1016/j.jalgebra.2008.11.030), J. Algebra 321 (2009),
  1836--1976.
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
[Hir1964].
-/
@[category research solved, AMS 14]
theorem resolution_of_singularities_of_charZero (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsSeparated sX] :
    Scheme.HasResolution sX := by
  sorry

/--
Resolution of singularities holds in dimension at most three over any perfect field. In
characteristic zero this is [Hir1964]; in positive characteristic, dimension at most two is
classical and dimension three is due to Cossart and Piltant, see [CP2008] and [CP2009]. It is
open in positive characteristic from dimension four on.
-/
@[category research solved, AMS 14]
theorem resolution_of_singularities_of_topologicalKrullDim_le_three (k : Type u) [Field k]
    [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] [IsSeparated sX]
    (hX : topologicalKrullDim X ≤ 3) :
    Scheme.HasResolution sX := by
  sorry

end AlgebraicGeometry
