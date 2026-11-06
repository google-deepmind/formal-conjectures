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
# The Kervaire–Laudenbach conjecture

Kervaire's conjecture asserts that if $G$ is a nontrivial group, then the free product
$G * \mathbb{Z}$ is not the normal closure of a single element. A stronger form, sometimes also
called the Kervaire–Laudenbach conjecture, asserts that every *unimodular* equation over $G$
(one whose exponent sum in the unknown is $\pm 1$) has a solution in some group containing $G$;
equivalently, $G$ embeds in $(G * \mathbb{Z}) / \langle\langle w \rangle\rangle$ for every
unimodular $w \in G * \mathbb{Z}$.

*References:*
- [GR62] M. Gerstenhaber and O. S. Rothaus, *The solution of sets of equations in groups*,
  Proc. Natl. Acad. Sci. USA 48 (1962), 1531–1533.
- [Kl93] A. A. Klyachko, *A funny property of sphere and equations over groups*,
  Comm. Algebra 21 (1993), 2555–2575.
- [Kl05] A. A. Klyachko, *The Kervaire–Laudenbach conjecture and presentations of simple
  groups*, Algebra and Logic 44 (2005), 219–242.
- [OAI26] OpenAI, *The Kervaire theorem for groups*. OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Kervaire-Theorem-for-Groups-September-24-2026/The-Kervaire-Theorem-for-Groups-September-24-2026.pdf
-/

@[expose] public section

namespace KervaireConjecture

universe u

/-- The free product $G * \mathbb{Z}$, with $\mathbb{Z}$ written multiplicatively. -/
abbrev FreeProductZ (G : Type*) [Group G] := Monoid.Coprod G (Multiplicative ℤ)

/-- The exponent sum of `w` in the generator of $\mathbb{Z}$. -/
def exponentSum {G : Type*} [Group G] (w : FreeProductZ G) : ℤ :=
  Multiplicative.toAdd (Monoid.Coprod.snd w)

/-- The map $G \to (G * \mathbb{Z}) / \langle\langle w \rangle\rangle$. -/
def coefficientMap {G : Type*} [Group G] (w : FreeProductZ G) :
    G →* FreeProductZ G ⧸ Subgroup.normalClosure ({w} : Set (FreeProductZ G)) :=
  (QuotientGroup.mk' _).comp Monoid.Coprod.inl

/--
**Kervaire's conjecture.** If $G$ is a nontrivial group, then no element $w$ normally generates
$G * \mathbb{Z}$.

Gerstenhaber and Rothaus proved it for finite groups [GR62] and Klyachko for torsion-free
groups [Kl93]. An internal OpenAI model proved it for all groups in September 2026 [OAI26],
through the stronger statement `kervaire_conjecture.variants.unimodular`.
-/
@[category research solved, AMS 20]
theorem kervaire_conjecture (G : Type*) [Group G] [Nontrivial G] (w : FreeProductZ G) :
    Subgroup.normalClosure ({w} : Set (FreeProductZ G)) ≠ ⊤ := by
  sorry

/--
**Unimodular equations are solvable** [OAI26]. If the exponent sum of $w \in G * \mathbb{Z}$
is $\pm 1$, then $G$ embeds in $(G * \mathbb{Z}) / \langle\langle w \rangle\rangle$.
-/
@[category research solved, AMS 20]
theorem kervaire_conjecture.variants.unimodular (G : Type*) [Group G] (w : FreeProductZ G)
    (hw : exponentSum w = 1 ∨ exponentSum w = -1) :
    Function.Injective (coefficientMap w) := by
  sorry

/-- Kervaire's conjecture for finite groups [GR62]. -/
@[category research solved, AMS 20]
theorem kervaire_conjecture.variants.finite (G : Type*) [Group G] [Finite G] [Nontrivial G]
    (w : FreeProductZ G) :
    Subgroup.normalClosure ({w} : Set (FreeProductZ G)) ≠ ⊤ := by
  sorry

/-- Kervaire's conjecture for torsion-free groups [Kl93]. -/
@[category research solved, AMS 20]
theorem kervaire_conjecture.variants.torsion_free (G : Type*) [Group G] [Nontrivial G]
    (hG : Monoid.IsTorsionFree G) (w : FreeProductZ G) :
    Subgroup.normalClosure ({w} : Set (FreeProductZ G)) ≠ ⊤ := by
  sorry

/-- If `w` normally generates $G * \mathbb{Z}$, then its exponent sum is $\pm 1$. -/
@[category API, AMS 20]
lemma exponentSum_eq_one_or_neg_one {G : Type*} [Group G] (w : FreeProductZ G)
    (hw : Subgroup.normalClosure ({w} : Set (FreeProductZ G)) = ⊤) :
    exponentSum w = 1 ∨ exponentSum w = -1 := by
  have hsurj : Function.Surjective (Monoid.Coprod.snd : FreeProductZ G →* Multiplicative ℤ) :=
    fun z => ⟨Monoid.Coprod.inr z, DFunLike.congr_fun
      (Monoid.Coprod.snd_comp_inr (M := G) (N := Multiplicative ℤ)) z⟩
  have htop := Subgroup.map_normalClosure {w} _ hsurj
  rw [hw, Subgroup.map_top_of_surjective _ hsurj, Set.image_singleton] at htop
  have hle : Subgroup.normalClosure ({Monoid.Coprod.snd w} : Set (Multiplicative ℤ)) ≤
      Subgroup.zpowers (Monoid.Coprod.snd w) :=
    Subgroup.normalClosure_le_normal (by simp)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (hle (htop ▸ Subgroup.mem_top (Multiplicative.ofAdd (1 : ℤ))))
  have h1 : exponentSum w * k = 1 := by
    rw [mul_comm]
    simpa [exponentSum] using congrArg Multiplicative.toAdd hk
  exact Int.eq_one_or_neg_one_of_mul_eq_one h1

/-- The unimodular form `kervaire_conjecture.variants.unimodular` implies Kervaire's
conjecture. -/
@[category test, AMS 20]
theorem kervaire_conjecture_of_unimodular
    (h : type_of% @kervaire_conjecture.variants.unimodular.{u}) :
    type_of% @kervaire_conjecture.{u} := by
  intro G _ _ w hw
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  apply ha
  apply h G w (exponentSum_eq_one_or_neg_one w hw)
  simp only [map_one, coefficientMap, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, hw, Subgroup.mem_top]

end KervaireConjecture
