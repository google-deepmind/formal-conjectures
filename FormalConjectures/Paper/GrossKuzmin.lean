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
# The Gross-Kuz'min conjecture

Let $K$ be a number field, $p$ a prime, and $S_p$ the set of primes $\mathfrak{p}$ of
$\mathcal{O}_K$ above $p$. Let $E' = \mathcal{O}_K[1/p]^\times$ be the group of *$p$-units* of
$K$, the elements of $K^\times$ that are units at every prime away from $S_p$. **Gross's
regulator map** sends a $p$-unit to the vector of $p$-adic logarithms of its local norms,
$$\rho : E' \to \bigoplus_{\mathfrak{p} \in S_p} \mathbb{Q}_p, \qquad
x \mapsto \big(\log_p N_{K_\mathfrak{p} / \mathbb{Q}_p}(x)\big)_{\mathfrak{p} \in S_p}.$$

**The Gross-Kuz'min conjecture** states that the image of $\mathbb{Z}_p \otimes E'$ under $\rho$
has $\mathbb{Z}_p$-rank $|S_p| - 1$. This is the largest value it can take: the coordinates of
$\rho(x)$ always sum to $\log_p N_{K/\mathbb{Q}}(x) = \log_p(\pm p^k) = 0$, so the image lies in a
hyperplane. Maksoud [Conjecture 1.3] states the conjecture as the surjectivity of $-\rho$, after
$p$-adic completion, onto this hyperplane, which is the same thing since the hyperplane has rank
$|S_p| - 1$.

The conjecture is the exact analogue for $p$-units of Leopoldt's conjecture for units, which says
that the matrix of $p$-adic logarithms of a fundamental system of units has full rank. Like
Leopoldt's, it is known for $K/\mathbb{Q}$ abelian, by Greenberg building on the $p$-adic Baker
theorem of Ax and Brumer.

## The dictionary

Two things are said differently here than in the sources, both because Mathlib says them that
way and neither changing the content.

* **The local norm is computed with embeddings.** Mathlib `v4.33.1` gives $K_\mathfrak{p}$ no
  $\mathbb{Q}_p$-algebra structure, so $N_{K_\mathfrak{p}/\mathbb{Q}_p}$ is not available. Since
  $K \otimes_\mathbb{Q} \mathbb{Q}_p = \prod_{\mathfrak{p} \in S_p} K_\mathfrak{p}$, the
  embeddings $\sigma : K \to \mathbb{C}_p$ inducing $\mathfrak{p}$ are exactly the embeddings of
  $K_\mathfrak{p}$ restricted to $K$, and $\log_p$ turns the norm into a sum:
  $$\log_p N_{K_\mathfrak{p} / \mathbb{Q}_p}(x) = \sum_{\sigma \mapsto \mathfrak{p}}
  \log_p \sigma(x).$$
  The right-hand side is `logNorm`, and `Induces σ 𝔭` is "$\sigma$ induces $\mathfrak{p}$",
  written as $\mathfrak{p}$ being the pullback along $\sigma$ of the maximal ideal of
  $\mathbb{C}_p$.

  This identification is where the statement rests on mathematics not proved here. That
  distinct primes use disjoint sets of embeddings is `Induces.unique`, and that an induced prime
  lies above $p$ is `mem_asIdeal_of_induces`. Two further facts are used only informally, and
  they are not equally out of reach. First, that **every** $\mathfrak{p} \in S_p$ is induced by
  at least one embedding: this is the one that matters for soundness, since if some
  $\mathfrak{p}$ had no embedding over it then `logNorm` would be `0` at that coordinate and the
  conjecture below would state something weaker than it should. It is within reach of Mathlib
  `v4.33.1` — pass to the Galois closure, where the Galois group acts transitively on the primes
  above $p$, and restrict — but it is not done here. Second, that $\mathfrak{p}$ is induced by
  **exactly** $[K_\mathfrak{p} : \mathbb{Q}_p]$ embeddings, which is what makes `logNorm` the
  local norm on the nose: this one does need $K_\mathfrak{p}$ as a finite
  $\mathbb{Q}_p$-algebra, the same missing structure that makes
  $N_{K_\mathfrak{p}/\mathbb{Q}_p}$ unavailable. Until both are available, a reader should check
  `logNorm` against the displayed formula by hand.

* **The rank is a $\mathbb{C}_p$-dimension.** The $\mathbb{Z}_p$-rank of the image of
  $\mathbb{Z}_p \otimes E'$ in $\mathbb{Q}_p^{S_p}$ is the $\mathbb{Q}_p$-dimension of the span of
  $\rho(E')$, and extending scalars to $\mathbb{C}_p$ does not change it. Taking the span inside
  $\mathbb{C}_p^{S_p}$ avoids having to see that the local norms are rational.
  `FormalConjectures.Wikipedia.LeopoldtConjecture` states Leopoldt's conjecture the same way,
  as `Matrix.rank` of a matrix over $\mathbb{C}_p$.

The remaining objects match the sources directly.

*References:*
- A. Maksoud, *On the rank of Leopoldt's and Gross's regulator maps*, Doc. Math. **28** (2023),
  1441-1471, [arXiv:2201.08203](https://arxiv.org/abs/2201.08203), (2) and Conjecture 1.3: the
  statement formalised here, as the surjectivity of Gross's regulator map onto the hyperplane.
- B. H. Gross, *$p$-adic $L$-series at $s = 0$*, J. Fac. Sci. Univ. Tokyo Sect. IA Math. **28**
  (1981), 979-994: Gross's formulation of the conjecture.
- L. V. Kuz'min, *The Tate module of algebraic number fields*, Izv. Akad. Nauk SSSR Ser. Mat.
  **36** (1972), 267-327: the original class field theoretic statement.
- R. Greenberg, *On a certain l-adic representation*, Invent. Math. **21** (1973), 117-124: the
  conjecture for abelian $K/\mathbb{Q}$.
-/

open IsDedekindDomain NumberField

open scoped NumberField

namespace GrossKuzmin

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/- ## The primes above `p` -/

/-- $S_p$ as a set of primes, the shape `Set.unit` wants for the $p$-units. -/
abbrev primesAboveSet : Set (HeightOneSpectrum (𝓞 K)) := {v | (p : 𝓞 K) ∈ v.asIdeal}

instance : Finite (PrimesAbove K p) :=
  ((Ideal.finite_factors (I := Ideal.span {(p : 𝓞 K)}) (by simp [NeZero.ne p])).subset
    fun _ ↦ Ideal.dvd_span_singleton.2).to_subtype

@[category API, AMS 11]
theorem nonempty_primesAbove : Nonempty (PrimesAbove K p) := by
  obtain ⟨⟨Q, hQprime, hQover⟩⟩ : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) :=
    inferInstance
  exact ⟨⟨⟨Q, hQprime, Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)})
    (by simp [NeZero.ne p]) Q⟩, by simpa [hQover.over] using Ideal.mem_span_singleton_self (p : ℤ)⟩⟩

/- ## The `p`-units -/

/-- $E' = \mathcal{O}_K[1/p]^\times$, the group of $p$-units of `K`: the elements of $K^\times$
whose valuation is `1` at every prime away from $S_p$. This is the unit group of the ring
$\mathcal{O}_K[1/p]$ of $S_p$-integers by `Set.unitEquivUnitsInteger`. -/
noncomputable
abbrev pUnits : Subgroup Kˣ := (primesAboveSet K p).unit K

/- ## Gross's regulator map -/

/-- `Induces σ v` says that the prime `v` of $\mathcal{O}_K$ is the one induced by the embedding
$\sigma : K \to \mathbb{C}_p$, that is, the pullback along $\sigma$ of the maximal ideal
$\{z : \|z\| < 1\}$ of $\mathbb{C}_p$. An embedding induces at most one prime
(`Induces.unique`), and a prime it induces lies above `p` (`mem_asIdeal_of_induces`). That every
$\sigma$ induces one is true, but is not proved here; see the module docstring. -/
def Induces {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] (σ : K →+* ℂ_[p])
    (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ y : 𝓞 K, y ∈ v.asIdeal ↔ ‖σ (y : K)‖ < 1

@[category API, AMS 11]
theorem mem_asIdeal_of_induces {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {σ : K →+* ℂ_[p]} {v : HeightOneSpectrum (𝓞 K)} (h : Induces σ v) : (p : 𝓞 K) ∈ v.asIdeal := by
  refine (h (p : 𝓞 K)).2 ?_
  simpa [map_natCast] using PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one

@[category API, AMS 11]
theorem Induces.unique {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {σ : K →+* ℂ_[p]} {v w : HeightOneSpectrum (𝓞 K)} (hv : Induces σ v) (hw : Induces σ w) :
    v = w := HeightOneSpectrum.ext (Ideal.ext fun y ↦ (hv y).trans (hw y).symm)

open scoped Classical in
/-- $\log_p N_{K_\mathfrak{p} / \mathbb{Q}_p}(x)$, computed as $\sum_\sigma \log_p \sigma(x)$
over the embeddings $\sigma : K \to \mathbb{C}_p$ inducing $\mathfrak{p}$. See the module
docstring for why the local norm is spelled out this way. -/
noncomputable
def logNorm (x : K) (v : HeightOneSpectrum (𝓞 K)) : ℂ_[p] :=
  ∑ σ ∈ Finset.univ.filter fun σ : K →+* ℂ_[p] ↦ Induces σ v, PadicIwasawaLog.iwasawaLog p (σ x)

/-- Every summand of `logNorm` at a $p$-unit, hence every summand of `grossRegulator`, is a
genuine Iwasawa logarithm rather than the junk value: a $p$-unit is a nonzero element of `K` and
an embedding $\sigma : K \to \mathbb{C}_p$ is injective, so
$\sigma(x) \in \mathbb{C}_p^\times$ lies in the domain of `iwasawaLog`
(`PadicIwasawaLog.PadicComplex.hasIwasawaLog_iff`). -/
@[category API, AMS 11]
theorem hasIwasawaLog_embedding (x : pUnits K p) (σ : K →+* ℂ_[p]) :
    PadicIwasawaLog.HasIwasawaLog p (σ ((x : Kˣ) : K)) :=
  PadicIwasawaLog.PadicComplex.hasIwasawaLog_iff.2
    fun h => (x : Kˣ).ne_zero (σ.injective (h.trans (map_zero σ).symm))

/-- **Gross's regulator map** $\rho : E' \to \bigoplus_{\mathfrak{p} \in S_p} \mathbb{Q}_p$,
$x \mapsto (\log_p N_{K_\mathfrak{p}/\mathbb{Q}_p}(x))_\mathfrak{p}$, with $\mathbb{C}_p$ in
place of $\mathbb{Q}_p$. -/
noncomputable
def grossRegulator (x : pUnits K p) (v : PrimesAbove K p) : ℂ_[p] :=
  logNorm K p ((x : Kˣ) : K) v.1

/-- The $\mathbb{C}_p$-span of the image of Gross's regulator map. Its dimension is the
$\mathbb{Z}_p$-rank of the image of $\mathbb{Z}_p \otimes E'$ that the conjecture is about; see
the module docstring for why the span is taken over $\mathbb{C}_p$ rather than $\mathbb{Q}_p$. -/
noncomputable
def regulatorSpan : Submodule ℂ_[p] (PrimesAbove K p → ℂ_[p]) :=
  Submodule.span ℂ_[p] (Set.range (grossRegulator K p))

/- ## The conjecture -/

/-- **The Gross-Kuz'min conjecture.** Let $K$ be a number field, $p$ a prime, $S_p$ the set of
primes of $K$ above $p$ and $E' = \mathcal{O}_K[1/p]^\times$ the $p$-units. Then the image of
Gross's regulator map
$$\rho : E' \to \bigoplus_{\mathfrak{p} \in S_p} \mathbb{Q}_p, \qquad
x \mapsto \big(\log_p N_{K_\mathfrak{p} / \mathbb{Q}_p}(x)\big)_\mathfrak{p}$$
spans a subspace of dimension $|S_p| - 1$.

This is the maximum possible: the coordinates of $\rho(x)$ sum to
$\log_p N_{K/\mathbb{Q}}(x) = 0$, so the image lies in the hyperplane $\sum_\mathfrak{p} = 0$,
and the conjecture says that the image spans it [Maksoud, Conjecture 1.3]. -/
@[category research open, AMS 11]
theorem gross_kuzmin_conjecture :
    Module.finrank ℂ_[p] (regulatorSpan K p) = Nat.card (PrimesAbove K p) - 1 := by
  sorry

/-- **Greenberg's theorem.** The Gross-Kuz'min conjecture holds when $K$ is an abelian extension of
$\mathbb{Q}$. -/
@[category research solved, AMS 11]
theorem gross_kuzmin_conjecture.variants.abelian [IsAbelianGalois ℚ K] :
    Module.finrank ℂ_[p] (regulatorSpan K p) = Nat.card (PrimesAbove K p) - 1 := by
  sorry

end GrossKuzmin
