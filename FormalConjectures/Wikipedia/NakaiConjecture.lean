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
# The Nakai conjecture on rings of differential operators

Let $R$ be a finitely generated commutative integral domain over $\mathbb{C}$, representing the
coordinate ring of an irreducible complex affine algebraic variety $V$. Inside
$\operatorname{End}_{\mathbb{C}}(R)$, Grothendieck's filtration
$\mathcal{D}^k_{\mathbb{C}}(R)$ of algebraic linear differential operators is defined by taking
$\mathcal{D}^0_{\mathbb{C}}(R)$ to be the left $R$-multiplications $x \mapsto r x$ and
$\mathcal{D}^{k+1}_{\mathbb{C}}(R)$ to be the $\mathbb{C}$-linear maps $P : R \to R$ with
$[P, L_r] \in \mathcal{D}^k_{\mathbb{C}}(R)$ for all $r \in R$.

Grothendieck [Gr67, §16.11.2] proved that when $R$ is regular ($V$ is smooth), the differential
operator ring $\mathcal{D}_{\mathbb{C}}(R) = \bigcup_{k \ge 0} \mathcal{D}^k_{\mathbb{C}}(R)$ is
generated over $R$ by the $\mathbb{C}$-derivations $\operatorname{Der}_{\mathbb{C}}(R, R)$.
Nakai [Na61] conjectured the converse: if $\mathcal{D}_{\mathbb{C}}(R)$ is generated over $R$ by
$\operatorname{Der}_{\mathbb{C}}(R, R)$, then $R$ is regular. Mount and Villamayor [MV73] proved
Nakai's conjecture for curves ($\dim R = 1$).

*References:*
- [Wikipedia: Nakai conjecture](https://en.wikipedia.org/wiki/Nakai_conjecture)
- [Na61] Y. Nakai, *On the theory of differentials in commutative rings*, J. Math. Soc. Japan
  **13** (1961), 63–84.
- [Gr67] A. Grothendieck, *Éléments de géométrie algébrique. IV. Étude locale des schémas et des
  morphismes de schémas (Quatrième partie)*, Publ. Math. IHÉS **32** (1967), §16.11.2.
- [MV73] K. R. Mount and O. E. Villamayor, *On a conjecture of Y. Nakai*, Osaka J. Math. **10**
  (1973), 325–327.
-/

@[expose] public section

namespace NakaiConjecture

/-- Grothendieck's order-$k$ filtration $\mathcal{D}^k_{\mathbb{C}}(R) \subseteq
\operatorname{End}_{\mathbb{C}}(R)$ of algebraic linear differential operators on a commutative
$\mathbb{C}$-algebra $R$. -/
def grothendieckDiffOps (R : Type*) [CommRing R] [Algebra ℂ R] : ℕ → Set (Module.End ℂ R)
  | 0 => Set.range (LinearMap.mulLeft ℂ : R → Module.End ℂ R)
  | k + 1 =>
      {P : Module.End ℂ R | ∀ r : R,
        P.comp (LinearMap.mulLeft ℂ r) - (LinearMap.mulLeft ℂ r).comp P ∈
          grothendieckDiffOps R k}

/-- Predicate that $\bigcup_{k \ge 0} \mathcal{D}^k_{\mathbb{C}}(R)$ is generated as a subring
of $\operatorname{End}_{\mathbb{C}}(R)$ by left $R$-multiplications and $\mathbb{C}$-linear
derivations of $R$ (i.e. generated as an $R$-algebra by $\operatorname{Der}_{\mathbb{C}}(R, R)$). -/
def IsDiffOpsGeneratedByDerivations (R : Type*) [CommRing R] [Algebra ℂ R] : Prop :=
  (⋃ k : ℕ, grothendieckDiffOps R k) ⊆
    (Subring.closure
      (Set.range (LinearMap.mulLeft ℂ : R → Module.End ℂ R) ∪
        Set.range (Derivation.toLinearMap : Derivation ℂ R R → Module.End ℂ R)) :
      Set (Module.End ℂ R))

/-- Every $\mathbb{C}$-linear derivation $\delta \in \operatorname{Der}_{\mathbb{C}}(R, R)$ lies
in $\mathcal{D}^1_{\mathbb{C}}(R)$ since $[\delta, L_r] = L_{\delta(r)}$. -/
@[category test, AMS 13 14]
theorem derivation_mem_grothendieckDiffOps_one
    (R : Type*) [CommRing R] [Algebra ℂ R] (δ : Derivation ℂ R R) :
    δ.toLinearMap ∈ grothendieckDiffOps R 1 := by
  intro r
  refine ⟨δ r, ?_⟩
  ext x
  simp [Derivation.leibniz]
  ring

/-- A $\mathbb{C}$-linear endomorphism of $R$ commutes with all left $R$-multiplications
precisely when it belongs to $\mathcal{D}^0_{\mathbb{C}}(R)$. -/
@[category API, AMS 13 14]
theorem centralizer_mulLeft_eq_grothendieckDiffOps_zero
    (R : Type*) [CommRing R] [Algebra ℂ R] (P : Module.End ℂ R) :
    (∀ r : R, P.comp (LinearMap.mulLeft ℂ r) - (LinearMap.mulLeft ℂ r).comp P = 0) ↔
      P ∈ grothendieckDiffOps R 0 := by
  constructor
  · intro h
    refine ⟨P 1, ?_⟩
    ext r
    have hr := LinearMap.congr_fun (sub_eq_zero.mp (h r)) 1
    simpa [mul_comm] using hr.symm
  · rintro ⟨a, rfl⟩ r
    ext x
    simp [mul_left_comm]

/-- On $\mathbb{C}[X]$, formal differentiation `Polynomial.derivative` does not belong to
$\mathcal{D}^0_{\mathbb{C}}(\mathbb{C}[X])$, since $[\frac{d}{dX}, L_X](1) = 1 \neq 0$. -/
@[category test, AMS 13 14]
theorem polynomial_derivative_notMem_grothendieckDiffOps_zero :
    (Polynomial.derivative : Module.End ℂ (Polynomial ℂ)) ∉
      grothendieckDiffOps (Polynomial ℂ) 0 := by
  rw [← centralizer_mulLeft_eq_grothendieckDiffOps_zero]
  intro h
  have h1 := LinearMap.congr_fun (h Polynomial.X) 1
  simp at h1

/-- On $R = \mathbb{C}$ itself, every $\mathbb{C}$-linear endomorphism is left multiplication by
$P(1)$, so `IsDiffOpsGeneratedByDerivations ℂ` holds. -/
@[category test, AMS 13 14]
theorem isDiffOpsGeneratedByDerivations_self :
    IsDiffOpsGeneratedByDerivations ℂ := by
  rintro P -
  refine Subring.subset_closure (Or.inl ⟨P 1, ?_⟩)
  ext
  simp

/-- **Grothendieck's theorem** [Gr67, §16.11.2]: for a regular finitely generated commutative
$\mathbb{C}$-domain $R$ (smooth irreducible complex affine variety), the ring of differential
operators $\mathcal{D}_{\mathbb{C}}(R)$ is generated over $R$ by
$\operatorname{Der}_{\mathbb{C}}(R, R)$. -/
@[category textbook, AMS 13 14]
theorem grothendieck_regular_diffOps_generated
    (R : Type*) [CommRing R] [IsDomain R] [Algebra ℂ R] [Algebra.FiniteType ℂ R]
    [IsRegularRing R] :
    IsDiffOpsGeneratedByDerivations R := by
  sorry

/-- **Mount–Villamayor curve theorem** [MV73]: Nakai's conjecture holds for irreducible complex
affine algebraic curves ($\dim R = 1$). -/
@[category research solved, AMS 13 14]
theorem mount_villamayor_curve_theorem
    (R : Type*) [CommRing R] [IsDomain R] [Algebra ℂ R] [Algebra.FiniteType ℂ R]
    (hdim : ringKrullDim R = 1)
    (hgen : IsDiffOpsGeneratedByDerivations R) :
    IsRegularRing R := by
  sorry

/-- **Nakai's conjecture** [Na61]: let $R$ be a finitely generated commutative integral domain
over $\mathbb{C}$. If $\mathcal{D}_{\mathbb{C}}(R)$ is generated over $R$ by
$\operatorname{Der}_{\mathbb{C}}(R, R)$, then $R$ is a regular ring. Because smoothness over
$\mathbb{C}$ (`IsRegularRing R`) and generation of $\mathcal{D}_{\mathbb{C}}$ by derivations are
Zariski-local on finite-type $\mathbb{C}$-schemes, Wikipedia's geometric formulation for complex
algebraic varieties reduces to this irreducible affine coordinate-ring statement. -/
@[category research open, AMS 13 14]
theorem nakai_conjecture
    (R : Type*) [CommRing R] [IsDomain R] [Algebra ℂ R] [Algebra.FiniteType ℂ R]
    (hgen : IsDiffOpsGeneratedByDerivations R) :
    IsRegularRing R := by
  sorry

end NakaiConjecture
