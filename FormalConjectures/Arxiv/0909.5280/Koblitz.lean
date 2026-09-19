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
# Koblitz's conjecture

This file states the refined Koblitz conjecture [Zyw09, Conjecture 1.2] over number fields.
The original conjecture [Zyw09, Conjecture 1.1] is recorded as false at the end of the file.

We use integral Weierstrass equations with elliptic generic fiber. Every elliptic curve over a
number field admits such an equation. We count over all nonzero prime ideals, represented by
Mathlib's `HeightOneSpectrum`. Outside the finitely many primes dividing the discriminant,
`reductionOrder` is the order of the elliptic curve over the residue field. Including the
exceptional primes changes the counts by a bounded amount and preserves the asymptotic,
local densities, and finiteness assertion.

The constants are defined using reduction-count densities. By Chebotarev and [Zyw09, (2.2)],
`localDensity E t m` is the density $\delta_{E,t}(tm)$. Thus `koblitzConstant` is exactly the
constant of [Zyw09, Definition 2.1], including dependencies between distinct torsion fields.
The limits defining these constants exist under the stated hypotheses by [Zyw09, Section 2].

*References:*

* [Zyw09] D. Zywina, *A refinement of Koblitz's conjecture*.
  https://arxiv.org/abs/0909.5280
-/

namespace Arxiv.«0909.5280»

open IsDedekindDomain
open scoped BigOperators NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The number of nonsingular points of the reduced equation, including infinity.
When the discriminant is nonzero modulo $\mathfrak p$, this is $\#E(\mathbb{F}_{\mathfrak p})$. -/
noncomputable def reductionOrder (E : WeierstrassCurve (𝓞 K))
    (𝔭 : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Nat.card (E.map (Ideal.Quotient.mk 𝔭.asIdeal)).toAffine.Point

/-- The number of nonzero prime ideals of norm at most $N$. -/
noncomputable def primeIdealCount (K : Type*) [Field K] [NumberField K] (N : ℕ) : ℕ :=
  Nat.card {𝔭 : HeightOneSpectrum (𝓞 K) // 𝔭.asIdeal.absNorm ≤ N}

/-- The number of nonzero prime ideals of norm at most $N$ for which the reduction order divided by
$t$ is a prime integer. Divisibility is required before taking the natural-number quotient. -/
noncomputable def primeOrderCount (E : WeierstrassCurve (𝓞 K)) (t N : ℕ) : ℕ :=
  Nat.card {𝔭 : HeightOneSpectrum (𝓞 K) // 𝔭.asIdeal.absNorm ≤ N ∧
    t ∣ reductionOrder E 𝔭 ∧ (reductionOrder E 𝔭 / t).Prime}

/-- The number of nonzero prime ideals of norm at most $N$ for which the reduction order divided by
$t$ is an integer relatively prime to $m$. -/
noncomputable def coprimeOrderCount (E : WeierstrassCurve (𝓞 K)) (t m N : ℕ) : ℕ :=
  Nat.card {𝔭 : HeightOneSpectrum (𝓞 K) // 𝔭.asIdeal.absNorm ≤ N ∧
    t ∣ reductionOrder E 𝔭 ∧ Nat.Coprime (reductionOrder E 𝔭 / t) m}

/-- For positive $t,m$ and elliptic generic fiber, the density $\delta_{E,t}(tm)$ of
[Zyw09, (2.2)]. The limit exists by Chebotarev. -/
noncomputable def localDensity (E : WeierstrassCurve (𝓞 K)) (t m : ℕ) : ℝ :=
  Filter.limUnder Filter.atTop
    (fun N : ℕ ↦ (coprimeOrderCount E t m N : ℝ) / (primeIdealCount K N : ℝ))

/-- The density of integers relatively prime to the product of primes at most $Q$. -/
noncomputable def sieveDensity (Q : ℕ) : ℝ :=
  ∏ ℓ ∈ Nat.primesLE Q, (1 - (ℓ : ℝ)⁻¹)

/-- The refined constant $C_{E,t}$ of [Zyw09, Definition 2.1]. Joint congruence densities
are taken before dividing by the elementary sieve density. -/
noncomputable def koblitzConstant (E : WeierstrassCurve (𝓞 K)) (t : ℕ) : ℝ :=
  Filter.limUnder Filter.atTop
    (fun Q : ℕ ↦ localDensity E t (primorial Q) / sieveDensity Q)

/-- The normalized counting function $P_{E,t}(N)(\log N)^2/N$. -/
noncomputable def normalizedPrimeOrderCount (E : WeierstrassCurve (𝓞 K)) (t N : ℕ) : ℝ :=
  (primeOrderCount E t N : ℝ) * (Real.log (N : ℝ)) ^ 2 / (N : ℝ)

/-- **The refined Koblitz conjecture** [Zyw09, Conjecture 1.2]. For an elliptic curve over a
number field and a positive integer $t$, the constant $C_{E,t}$ is nonnegative. If it is positive,
then $P_{E,t}(N) \sim C_{E,t}N/(\log N)^2$. If it is zero, $P_{E,t}$ is bounded, equivalently
only finitely many good primes have prime quotient order. -/
@[category research open, AMS 11 14]
theorem conjecture_1_2 (E : WeierstrassCurve (𝓞 K)) [(E.baseChange K).IsElliptic]
    (t : ℕ) (ht : 0 < t) :
    0 ≤ koblitzConstant E t ∧
      (koblitzConstant E t = 0 → ∃ B : ℕ, ∀ N : ℕ, primeOrderCount E t N ≤ B) ∧
      (0 < koblitzConstant E t →
        Filter.Tendsto (normalizedPrimeOrderCount E t) Filter.atTop
          (nhds (koblitzConstant E t))) := by sorry

/-- The thirteen rational CM $j$-invariants. -/
private def cmJInvariants : Finset ℚ :=
  {0, 1728, -3375, 8000, -32768, 54000, 287496, -884736,
    -12288000, 16581375, -884736000, -147197952000, -262537412640768000}

/-- The generic fiber has no complex multiplication over $\overline{\mathbb{Q}}$. -/
def IsNonCM (E : WeierstrassCurve (𝓞 ℚ)) [(E.baseChange ℚ).IsElliptic] : Prop :=
  (E.baseChange ℚ).j ∉ cmJInvariants

/-- No rational prime divides all reduction orders at sufficiently large norms. By Katz's criterion
[Zyw09, Theorem 3.2], for elliptic generic fiber this is equivalent to having no nontrivial
rational torsion on any curve in the rational isogeny class. -/
def HasNoIsogenyTorsion (E : WeierstrassCurve (𝓞 ℚ)) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ∀ B : ℕ,
    ∃ 𝔭 : HeightOneSpectrum (𝓞 ℚ), B < 𝔭.asIdeal.absNorm ∧ ¬ ℓ ∣ reductionOrder E 𝔭

/-- Koblitz's original constant, which multiplies the single-prime densities independently
[Zyw09, Remark 2.9]. This can differ from the refined constant. -/
noncomputable def originalConstant (E : WeierstrassCurve (𝓞 ℚ)) : ℝ :=
  Filter.limUnder Filter.atTop
    (fun Q : ℕ ↦ ∏ ℓ ∈ Nat.primesLE Q,
      localDensity E 1 ℓ / (1 - (ℓ : ℝ)⁻¹))

/-- The original assertion of [Zyw09, Conjecture 1.1]. -/
def OriginalConjecture : Prop :=
  ∀ (E : WeierstrassCurve (𝓞 ℚ)) [(E.baseChange ℚ).IsElliptic],
    IsNonCM E → HasNoIsogenyTorsion E →
      0 < originalConstant E ∧
        Filter.Tendsto (normalizedPrimeOrderCount E 1) Filter.atTop (nhds (originalConstant E))

/-- **The original Koblitz conjecture is false** [Zyw09, Section 1.1]. The curve
$y^2 = x^3 + 9x + 18$ satisfies its hypotheses but has composite reduction order for every
rational prime $p > 5$. -/
@[category research solved, AMS 11 14]
theorem conjecture_1_1 : answer(False) ↔ OriginalConjecture := by sorry

end Arxiv.«0909.5280»
