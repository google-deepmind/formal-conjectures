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
# Local uniformization

Let $F$ be a finitely generated field extension of a field $k$ and let $\mathcal{O}$ be a
valuation ring of $F$ containing $k$. *Local uniformization* asks for an affine model of
$F \mid k$ on which the centre of $\mathcal{O}$ is a regular point: a finitely generated
$k$-subalgebra $A \subseteq \mathcal{O}$ with fraction field $F$ such that $A_\mathfrak{p}$ is
regular, where $\mathfrak{p} = \mathfrak{m}_\mathcal{O} \cap A$ is the centre.

This is the local form of resolution of singularities, one valuation at a time. Zariski
introduced it and proved it in characteristic zero, and deduced resolution of singularities in
dimension at most three from it. In positive characteristic it is known in dimension at most
three and is open from dimension four on.

The conclusion here asks that the centre be a regular point, not a smooth one. Over a perfect
field the two agree; over an imperfect field regularity is the right condition, since already
$k(a^{1/p}) \mid k$ for $a \in k \setminus k^p$ has no model that is smooth over $k$.

For a field extension, `Algebra.EssFiniteType k F` says that $F$ is finitely generated as a
field over $k$, and `Algebra.trdeg k F` is the transcendence degree, the dimension of a model.

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Local_uniformization_theorem)
* [Zar1940] O. Zariski, [Local uniformization on algebraic
  varieties](https://doi.org/10.2307/1968864), Ann. of Math. 41 (1940), 852--896.
* [Abh1956] S. Abhyankar, [Local uniformization on algebraic surfaces over ground fields of
  characteristic $p \neq 0$](https://doi.org/10.2307/1970014), Ann. of Math. 63 (1956), 491--526.
* [Abh1966] S. Abhyankar, Resolution of singularities of embedded algebraic surfaces, Monographs
  in Pure and Applied Mathematics 24, Academic Press, 1966; three-dimensional birational
  resolution over a ground field of characteristic $p > 5$.
* [Cut2009] S. D. Cutkosky, [Resolution of singularities for 3-folds in positive
  characteristic](https://doi.org/10.1353/ajm.0.0036), Amer. J. Math. 131 (2009), 59--127.
* [CP2019] V. Cossart and O. Piltant, [Resolution of singularities of arithmetical
  threefolds](https://doi.org/10.1016/j.jalgebra.2019.02.017), J. Algebra 529 (2019), 268--535.
* [KK2005] H. Knaf and F.-V. Kuhlmann, [Abhyankar places admit local uniformization in any
  characteristic](https://doi.org/10.1016/j.ansens.2005.09.001), Ann. Sci. École Norm. Sup. 38
  (2005), 833--846.
* [KK2009] H. Knaf and F.-V. Kuhlmann, [Every place admits local uniformization in a finite
  extension of the function field](https://doi.org/10.1016/j.aim.2008.12.009), Adv. Math. 221
  (2009), 428--453.
* [Tem2013] M. Temkin, [Inseparable local
  uniformization](https://doi.org/10.1016/j.jalgebra.2012.09.023), J. Algebra 373 (2013), 65--119.
-/

open IsLocalRing

namespace ValuationSubring

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra k F]

/--
The *centre* of a valuation subring `𝒪` of `F` on a `k`-subalgebra `A` of `F` contained in `𝒪`:
the prime ideal `𝔪_𝒪 ∩ A` of `A`.
-/
def centerOn (𝒪 : ValuationSubring F) (A : Subalgebra k F) (hA : ∀ a : A, (a : F) ∈ 𝒪) :
    Ideal A :=
  (maximalIdeal 𝒪).comap (A.val.toRingHom.codRestrict 𝒪 hA)

instance (𝒪 : ValuationSubring F) (A : Subalgebra k F) (hA : ∀ a : A, (a : F) ∈ 𝒪) :
    (𝒪.centerOn A hA).IsPrime :=
  Ideal.IsPrime.comap _

/-- The centre of `𝒪` on `A` consists of the elements of `A` of valuation less than one. -/
@[category API, AMS 12 13]
theorem mem_centerOn_iff (𝒪 : ValuationSubring F) (A : Subalgebra k F)
    (hA : ∀ a : A, (a : F) ∈ 𝒪) (a : A) :
    a ∈ 𝒪.centerOn A hA ↔ 𝒪.valuation (a : F) < 1 := by
  rw [centerOn, Ideal.mem_comap, valuation_lt_one_iff]
  rfl

/--
A valuation subring `𝒪` of `F` *admits local uniformization over* `k` if some affine model of
`F` over `k` inside `𝒪` is regular at the centre of `𝒪`: there is a finitely generated `k`-subalgebra
`A` of `F` with `A ⊆ 𝒪` and fraction field `F` whose localisation at the centre of `𝒪` is a
regular local ring.
-/
def HasLocalUniformization (𝒪 : ValuationSubring F) (k : Type*) [Field k] [Algebra k F] : Prop :=
  ∃ (A : Subalgebra k F) (hA : ∀ a : A, (a : F) ∈ 𝒪),
    Algebra.FiniteType k A ∧ IsFractionRing A F ∧
      IsRegularLocalRing (Localization.AtPrime (𝒪.centerOn A hA))

/-- A regular affine model of `F` over `k` inside `𝒪` uniformizes `𝒪`. -/
@[category API, AMS 12 13 14]
theorem hasLocalUniformization_of_isRegularRing (𝒪 : ValuationSubring F) (A : Subalgebra k F)
    (hA : ∀ a : A, (a : F) ∈ 𝒪) [Algebra.FiniteType k A] [IsFractionRing A F]
    [IsRegularRing A] : 𝒪.HasLocalUniformization k :=
  ⟨A, hA, ‹_›, ‹_›, IsRegularRing.isRegularLocalRing_localization _⟩

/--
The trivial valuation subring of a function field is uniformized by any affine model, since its
centre is the generic point.
-/
@[category test, AMS 12 13 14]
theorem hasLocalUniformization_top (A : Subalgebra k F) [Algebra.FiniteType k A]
    [IsFractionRing A F] : (⊤ : ValuationSubring F).HasLocalUniformization k := by
  have hA : ∀ a : A, (a : F) ∈ (⊤ : ValuationSubring F) := fun a => mem_top _
  refine ⟨A, hA, ‹_›, ‹_›, ?_⟩
  have hbot : (⊤ : ValuationSubring F).centerOn A hA = ⊥ := by
    rw [centerOn, maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ fun x y h => Subtype.ext congr(($h : F))
  have hcompl : ((⊤ : ValuationSubring F).centerOn A hA).primeCompl = nonZeroDivisors A := by
    ext a
    rw [Ideal.mem_primeCompl_iff, hbot, Ideal.mem_bot, mem_nonZeroDivisors_iff_ne_zero]
  have : IsFractionRing A
      (Localization.AtPrime ((⊤ : ValuationSubring F).centerOn A hA)) := by
    show IsLocalization (nonZeroDivisors A) _
    rw [← hcompl]
    infer_instance
  let _ : Field (Localization.AtPrime ((⊤ : ValuationSubring F).centerOn A hA)) :=
    IsFractionRing.toField A
  infer_instance

end ValuationSubring

namespace LocalUniformization

/--
**Local uniformization in positive characteristic.**
Let $k$ be a field of characteristic $p > 0$, let $F$ be a finitely generated field extension of
$k$, and let $\mathcal{O}$ be a valuation ring of $F$ containing $k$. Then $\mathcal{O}$ admits
local uniformization over $k$.

This is open from dimension four on: it is known when the transcendence degree of $F \mid k$ is
at most three, see `local_uniformization_of_trdeg_le_three`.
-/
@[category research open, AMS 12 13 14]
theorem local_uniformization (k F : Type*) [Field k] [Field F] [Algebra k F]
    [Algebra.EssFiniteType k F] (p : ℕ) [Fact p.Prime] [CharP k p] (𝒪 : ValuationSubring F)
    (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    𝒪.HasLocalUniformization k := by
  sorry

/--
**Zariski's local uniformization theorem.** Every valuation ring of a finitely generated field
extension $F \mid k$ that contains a field $k$ of characteristic zero admits local uniformization
over $k$. This is the main theorem of [Zar1940].
-/
@[category research solved, AMS 12 13 14]
theorem local_uniformization_of_charZero (k F : Type*) [Field k] [Field F] [Algebra k F]
    [Algebra.EssFiniteType k F] [CharZero k] (𝒪 : ValuationSubring F)
    (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    𝒪.HasLocalUniformization k := by
  sorry

/--
Local uniformization holds in transcendence degree at most three over any field. In
characteristic zero this is [Zar1940]. In positive characteristic, surfaces are [Abh1956],
threefolds in characteristic $p > 5$ are [Abh1966], simplified in [Cut2009], and the remaining
characteristics $2, 3, 5$ are due to Cossart and Piltant. It follows in the generality stated
here from [CP2019], Theorem 1.1, which resolves the singularities of every reduced separated
Noetherian quasi-excellent scheme of dimension at most three in any characteristic: the centre
of $\mathcal{O}$ on a resolution of a proper model of $F \mid k$ is a regular point.
-/
@[category research solved, AMS 12 13 14]
theorem local_uniformization_of_trdeg_le_three (k F : Type*) [Field k] [Field F] [Algebra k F]
    [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F)
    (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3) :
    𝒪.HasLocalUniformization k := by
  sorry

/--
**Local uniformization after a finite extension.** Every valuation ring of a finitely generated
field extension $F \mid k$ that contains $k$ admits local uniformization over $k$ after a finite
extension $E$ of $F$, in any characteristic. This is the main theorem of [KK2009]. Compare
[Tem2013], where the extension of $F$ is purely inseparable but the ground field is extended too.
-/
@[category research solved, AMS 12 13 14]
theorem local_uniformization_after_finite_extension (k F : Type*) [Field k] [Field F]
    [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F)
    (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    ∃ (E : IntermediateField F (AlgebraicClosure F)) (_ : FiniteDimensional F E)
      (𝒪' : ValuationSubring E),
      𝒪'.comap (algebraMap F E) = 𝒪 ∧ 𝒪'.HasLocalUniformization k := by
  sorry

end LocalUniformization
