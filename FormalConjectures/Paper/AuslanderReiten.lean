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
# The Auslander-Reiten conjecture

**Auslander-Reiten conjecture.** Let $\Lambda$ be an Artin algebra and let $M$ be a finitely
generated $\Lambda$-module with $\operatorname{Ext}^i_\Lambda(M, M) = 0$ and
$\operatorname{Ext}^i_\Lambda(M, \Lambda) = 0$ for all $i > 0$. Then $M$ is projective.

An *Artin algebra* is a ring $\Lambda$ that is an algebra over a commutative Artinian ring $A$
and is finitely generated as an $A$-module.

Auslander and Reiten [AR75] derived this from the generalized Nakayama conjecture. The
commutative version, obtained by replacing $\Lambda$ with a commutative Noetherian ring $R$, is
also open and is what the commutative algebra literature calls the Auslander-Reiten conjecture.
The two hypotheses are together equivalent to
$\operatorname{Ext}^i_R(M, R \oplus M) = 0$ for all $i > 0$.

Known cases of the commutative version include: $R$ a locally excellent Cohen-Macaulay normal
ring containing $\mathbb Q$ [HL04]; $R$ a Gorenstein normal ring [Ar09]; $R$ a Cohen-Macaulay
normal ring [KOT22]; and, most generally, $R$ any normal ring [Ki23]. Auslander, Ding and Solberg
[ADS93] proved it for local complete intersections. The conjecture is open in general, already
for commutative Noetherian local rings.

*References:*
- [AR75] M. Auslander, I. Reiten, *On a generalized version of the Nakayama conjecture*, Proc.
  Amer. Math. Soc. 52 (1975), 69-74.
  [PDF](https://www.ams.org/journals/proc/1975-052-01/S0002-9939-1975-0389977-6/S0002-9939-1975-0389977-6.pdf)
- [Wikipedia, Nakayama conjecture](https://en.wikipedia.org/wiki/Nakayama_conjecture), on the
  generalized Nakayama conjecture of [AR75].
- [ADS93] M. Auslander, S. Ding, Ø. Solberg, *Liftings and weak liftings of modules*, J. Algebra
  156 (1993), 273-317.
- [HL04] C. Huneke, G. J. Leuschke, *On a conjecture of Auslander and Reiten*, J. Algebra 275
  (2004), no. 2, 781-790. [arXiv:math/0305001](https://arxiv.org/abs/math/0305001)
- [Ar09] T. Araya, *The Auslander-Reiten conjecture for Gorenstein rings*, Proc. Amer. Math. Soc.
  137 (2009), 1941-1944.
- [KOT22] K. Kimura, Y. Otake, R. Takahashi, *Maximal Cohen-Macaulay tensor products and
  vanishing of Ext modules*, Bull. Lond. Math. Soc. 54 (2022), no. 6, 2456-2468.
- [Ki23] K. Kimura, *Auslander-Reiten conjecture for normal rings*,
  [arXiv:2304.03956](https://arxiv.org/abs/2304.03956). The statements of the conjecture
  formalised below follow this paper.
-/

open CategoryTheory

namespace AuslanderReiten

universe u

section Converse

variable (Λ : Type u) [Ring Λ] (M : Type u) [AddCommGroup M] [Module Λ M]

/--
The converse of the conjecture is elementary: over any ring, all higher `Ext` out of a projective
module vanish. So the conjecture says that its two `Ext` vanishing hypotheses characterise the
projective modules.
-/
@[category test, AMS 13 18]
theorem subsingleton_ext_of_projective [Module.Projective Λ M] (N : ModuleCat.{u} Λ) (i : ℕ) :
    Subsingleton (Abelian.Ext (ModuleCat.of Λ M) N (i + 1)) :=
  Abelian.Ext.subsingleton_of_projective _ _ _

end Converse

section ArtinAlgebra

variable (Λ : Type u) [Ring Λ] (M : Type u) [AddCommGroup M] [Module Λ M] [Module.Finite Λ M]

/--
**The Auslander-Reiten conjecture** [AR75]. Let $\Lambda$ be an Artin algebra and $M$ a finitely
generated $\Lambda$-module with $\operatorname{Ext}^i_\Lambda(M, \Lambda) = 0$ and
$\operatorname{Ext}^i_\Lambda(M, M) = 0$ for all $i > 0$. Then $M$ is projective.

That $\Lambda$ is an Artin algebra is the hypothesis that it is an algebra over some commutative
Artinian ring `A` and is finitely generated as an `A`-module.
-/
@[category research open, AMS 13 16 18]
theorem auslander_reiten (A : Type u) [CommRing A] [IsArtinianRing A] [Algebra A Λ]
    [Module.Finite A Λ]
    (hMΛ : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of Λ M) (ModuleCat.of Λ Λ) i))
    (hMM : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of Λ M) (ModuleCat.of Λ M) i)) :
    Module.Projective Λ M := by
  sorry

end ArtinAlgebra

section Commutative

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]

/--
**The Auslander-Reiten conjecture for commutative Noetherian rings** [Ki23]. If $R$ is a
commutative Noetherian ring and $M$ is a finitely generated $R$-module with
$\operatorname{Ext}^i_R(M, R \oplus M) = 0$ for all $i > 0$, then $M$ is projective.
-/
@[category research open, AMS 13 18]
theorem auslander_reiten.variants.commutative
    (hMR : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R R) i))
    (hMM : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R M) i)) :
    Module.Projective R M := by
  sorry

/--
Over a Noetherian local ring a finitely generated projective module is free, so the conjecture
takes the following form there. It is open in this case too.
-/
@[category research open, AMS 13 18]
theorem auslander_reiten.variants.local_free [IsLocalRing R]
    (hMR : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R R) i))
    (hMM : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R M) i)) :
    Module.Free R M := by
  sorry

/--
The conjecture holds for normal rings [Ki23, Corollary 1.2]. Stated here for normal domains,
since Mathlib does not currently have a standalone class for normal rings, which are the rings
whose localizations at all primes are normal domains.
-/
@[category research solved, AMS 13 18]
theorem auslander_reiten.variants.normal [IsDomain R] [IsIntegrallyClosed R]
    (hMR : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R R) i))
    (hMM : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R M) i)) :
    Module.Projective R M := by
  sorry

omit [IsNoetherianRing R] in
/--
Over a regular local ring the conjecture is standard: every finitely generated module has finite
projective dimension $p$, and if $p > 0$ then $\operatorname{Ext}^p_R(M, R) \ne 0$. Only the
vanishing of $\operatorname{Ext}^i_R(M, R)$ is used, and the conclusion is freeness.
-/
@[category textbook, AMS 13 18]
theorem auslander_reiten.variants.regular_local [IsRegularLocalRing R]
    (hMR : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R R) i)) :
    Module.Free R M := by
  sorry

end Commutative

end AuslanderReiten
