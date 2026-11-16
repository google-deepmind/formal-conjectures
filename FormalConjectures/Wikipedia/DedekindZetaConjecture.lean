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
# Dedekind's Conjecture on Zeta Quotients

Given any number field $K$, both $\zeta_K(s)$ and the classical zeta series $\zeta(s)$ continue
meromorphically across $\mathbb{C}$ with a unique first-order pole at $s = 1$. Richard Dedekind
conjectured that $\zeta_K(s) / \zeta(s)$ always admits a holomorphic continuation to all of
$\mathbb{C}$—more generally, that $\zeta_L(s) / \zeta_K(s)$ is entire whenever $L / K$ is an
extension of number fields. Hideo Aramata [Ar33] and Richard Brauer [Br47] settled the Galois case,
and Koji Uchida [Uc75] and Robert van der Waall [vdW75] independently handled subfields inside a
solvable Galois closure; the general case remains open (and is implied by Artin's holomorphy
conjecture).

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Dedekind_zeta_function#Dedekind_conjecture)
- [Ar33] H. Aramata, *Über die Teilbarkeit der Dedekindschen Zetafunktionen*, Proc. Imp. Acad.
  Tokyo **9** (1933), no. 2, 31–34.
- [Br47] R. Brauer, *On the zeta-functions of algebraic number fields*, Amer. J. Math. **69**
  (1947), 243–250.
- [Uc75] K. Uchida, *On Artin L-functions*, Tohoku Math. J. (2) **27** (1975), 75–81.
- [vdW75] R. W. van der Waall, *On a conjecture of Dedekind on zeta functions*, Indag. Math.
  **37** (1975), 83–86.
-/

@[expose] public section

namespace DedekindZetaConjecture

open Ideal NumberField

/-- Given a number field $K$, the ratio $\zeta_K(s) / \zeta(s)$ continues to an entire function on
$\mathbb{C}$: equivalently, by analytic continuation out of the convergence half-plane
$\operatorname{Re}(s) > 1$ of `NumberField.dedekindZeta`, some entire
$f : \mathbb{C} \to \mathbb{C}$ satisfies $\zeta_K(s) = f(s) \zeta(s)$ whenever
$\operatorname{Re}(s) > 1$. -/
def DedekindZetaQuotientEntire (K : Type*) [Field K] [NumberField K] : Prop :=
  ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
    ∀ s : ℂ, 1 < s.re → NumberField.dedekindZeta K s = f s * riemannZeta s

/-- Relative form for number fields $K$ and $L$: some entire $f : \mathbb{C} \to \mathbb{C}$
satisfies $\zeta_L(s) = f(s) \zeta_K(s)$ on $\operatorname{Re}(s) > 1$. -/
def DedekindZetaRelQuotientEntire (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] : Prop :=
  ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
    ∀ s : ℂ, 1 < s.re → NumberField.dedekindZeta L s = f s * NumberField.dedekindZeta K s

/-- On the convergence half-plane $\operatorname{Re}(s) > 1$, `NumberField.dedekindZeta ℚ` agrees
with `riemannZeta`. -/
@[category API, AMS 11]
theorem dedekindZeta_rat_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta ℚ s = riemannZeta s := by
  rw [NumberField.dedekindZeta, ← LSeries_one_eq_riemannZeta hs]
  refine LSeries_congr (fun {n} _ => ?_) s
  suffices hcard : Nat.card {I : Ideal (𝓞 ℚ) // absNorm I = n} = 1 by simp [hcard]
  let φ := Rat.ringOfIntegersEquiv
  have hmap (I : Ideal (𝓞 ℚ)) : absNorm (Ideal.map φ I) = absNorm I :=
    Nat.card_congr (Ideal.quotientEquiv I _ φ rfl).toEquiv.symm
  have hsurj (J : Ideal ℤ) : Ideal.map φ (Ideal.comap φ J) = J :=
    Ideal.map_comap_of_surjective _ φ.surjective J
  let e : {I : Ideal (𝓞 ℚ) // absNorm I = n} ≃ {J : Ideal ℤ // absNorm J = n} :=
    ⟨fun ⟨I, hI⟩ => ⟨Ideal.map φ I, (hmap I).trans hI⟩,
      fun ⟨J, hJ⟩ => ⟨Ideal.comap φ J, by rw [← hmap, hsurj, hJ]⟩,
      fun ⟨I, _⟩ => Subtype.ext <| Ideal.comap_map_of_bijective _ φ.bijective,
      fun ⟨J, _⟩ => Subtype.ext <| hsurj J⟩
  rw [Nat.card_congr e]
  let : Unique {J : Ideal ℤ // absNorm J = n} :=
    { default := ⟨Ideal.span {(n : ℤ)}, by simp⟩
      uniq := fun ⟨J, hJ⟩ => Subtype.ext <| by
        dsimp only; rw [← hJ, Int.ideal_span_absNorm_eq_self] }
  exact Nat.card_unique

/-- On $\operatorname{Re}(s) > 1$, `riemannZeta s` is nonzero, so any two witnesses factoring
`NumberField.dedekindZeta K` through `riemannZeta` agree on $\{1 < \operatorname{Re}(s)\}$. -/
@[category API, AMS 11]
theorem entire_quotient_unique_on_right_half_plane {K : Type*} [Field K] [NumberField K]
    {f g : ℂ → ℂ}
    (hf : ∀ s : ℂ, 1 < s.re → NumberField.dedekindZeta K s = f s * riemannZeta s)
    (hg : ∀ s : ℂ, 1 < s.re → NumberField.dedekindZeta K s = g s * riemannZeta s)
    {s : ℂ} (hs : 1 < s.re) :
    f s = g s :=
  mul_right_cancel₀ (riemannZeta_ne_zero_of_one_lt_re hs) <|
    (hf s hs).symm.trans (hg s hs)

/-- Unconditional sanity check for $K = \mathbb{Q}$: `DedekindZetaQuotientEntire ℚ` holds (witnessed
by $f \equiv 1$), every witness evaluates to $1$ at $s = 2$, and `DedekindZetaRelQuotientEntire ℚ L`
agrees with `DedekindZetaQuotientEntire L`. -/
@[category test, AMS 11]
theorem dedekindZetaQuotientEntire_rat_and_rel_iff (L : Type*) [Field L] [NumberField L] :
    DedekindZetaQuotientEntire ℚ ∧
      (∀ f : ℂ → ℂ,
        (∀ s : ℂ, 1 < s.re → NumberField.dedekindZeta ℚ s = f s * riemannZeta s) → f 2 = 1) ∧
      (DedekindZetaRelQuotientEntire ℚ L ↔ DedekindZetaQuotientEntire L) := by
  have h1 : ∀ s : ℂ, 1 < s.re → NumberField.dedekindZeta ℚ s = (fun _ => 1) s * riemannZeta s :=
    fun s hs => by simpa using dedekindZeta_rat_eq_riemannZeta hs
  refine ⟨⟨fun _ => 1, differentiable_const 1, h1⟩, fun f hf => ?_, ?_⟩
  · exact entire_quotient_unique_on_right_half_plane hf h1 (by norm_num : 1 < (2 : ℂ).re)
  · refine ⟨fun ⟨f, hf, hrel⟩ => ⟨f, hf, fun s hs => ?_⟩,
      fun ⟨f, hf, habs⟩ => ⟨f, hf, fun s hs => ?_⟩⟩
    · rw [← dedekindZeta_rat_eq_riemannZeta hs]; exact hrel s hs
    · rw [dedekindZeta_rat_eq_riemannZeta hs]; exact habs s hs

/--
Aramata–Brauer theorem [Ar33, Br47]: whenever $K / \mathbb{Q}$ is a Galois number field, the ratio
$\zeta_K(s) / \zeta(s)$ continues holomorphically across $\mathbb{C}$.
-/
@[category research solved, AMS 11]
theorem aramata_brauer_galois_zeta_quotient_entire (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] :
    DedekindZetaQuotientEntire K := by
  sorry

/--
Uchida–van der Waall theorem [Uc75, vdW75]: if a number field $K$ embeds into a Galois number field
$M / \mathbb{Q}$ whose Galois group is solvable, then $\zeta_K(s) / \zeta(s)$ continues
holomorphically across $\mathbb{C}$.
-/
@[category research solved, AMS 11]
theorem uchida_van_der_waall_solvable_zeta_quotient_entire (K M : Type*) [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M] [IsGalois ℚ M] [Group.IsSolvable (M ≃ₐ[ℚ] M)] :
    DedekindZetaQuotientEntire K := by
  sorry

/--
Dedekind's conjecture: given any number field $K$, the ratio $\zeta_K(s) / \zeta(s)$ continues
holomorphically across $\mathbb{C}$.
-/
@[category research open, AMS 11]
theorem dedekind_zeta_quotient_entire_conjecture (K : Type*) [Field K] [NumberField K] :
    DedekindZetaQuotientEntire K := by
  sorry

/--
Relative Dedekind conjecture: given number fields $K$ and $L$ with $L$ a $K$-algebra, the ratio
$\zeta_L(s) / \zeta_K(s)$ continues holomorphically across $\mathbb{C}$.
-/
@[category research open, AMS 11]
theorem dedekind_zeta_quotient_entire_conjecture.variants.relative (K L : Type*) [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    DedekindZetaRelQuotientEntire K L := by
  sorry

end DedekindZetaConjecture
