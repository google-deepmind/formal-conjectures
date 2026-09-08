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

# Buchsbaum Eisenbud Horrocks Conjecture

-/

namespace Arxiv.«1702.02560»

universe u

open CategoryTheory RingTheory.Sequence

variable (R : Type u) [CommRing R] [ConnectedSpace (PrimeSpectrum R)]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M]
    (P : ProjectiveResolution M) (fin : ∃ n, ∀ i > n, Limits.IsZero (P.complex.X i))
    (c : ℕ) (ceq : c = Ideal.height (Module.annihilator R M))

/-- The `Buchsbaum-Eisenbud-Horrocks Conjecture` about lower bound of Betti number. -/
@[category research open, AMS 13]
theorem BuchsbaumEisenbudHorrocksConjecture [IsNoetherianRing R] :
    ∀ i, c.choose i ≤ Module.rank R (P.complex.X i) := by
  sorry

/-- The direct corollary of `Buchsbaum-Eisenbud-Horrocks Conjecture`, by taking sum. -/
@[category research open, AMS 13]
theorem TotalRankConjecture [IsNoetherianRing R] :
    2 ^ c ≤ ∑ i ∈ Finset.range (c + 1), (Module.rank R (P.complex.X i)) := by
  sorry

class IsCompleteIntersectionLocalRing (R : Type u) [CommRing R] extends
    IsLocalRing R, IsNoetherianRing R where
  is_quotient : ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S)
    (f : S →+* (AdicCompletion (IsLocalRing.maximalIdeal R) R)) (rs : List S),
      Function.Surjective f ∧ RingHom.ker f = Ideal.ofList rs ∧ IsRegular S rs

class IsLocallyCompleteIntersectionRing (R : Type u) [CommRing R] extends IsNoetherianRing R where
  localization_ci : ∀ (p : Ideal R) (_ : p.IsPrime),
    IsCompleteIntersectionLocalRing (Localization.AtPrime p)

/-- The solved case of `TotalRankConjecture`, assuming the ring is lci. -/
@[category research solved, AMS 13]
theorem TotalRankConjecture_of_ci [IsLocallyCompleteIntersectionRing R]
    (h_torsion : ∀ m : M, m + m = 0 → m = 0) :
    2 ^ c ≤ ∑ i ∈ Finset.range (c + 1), (Module.rank R (P.complex.X i)) := by
  sorry

/-- The solved case of `TotalRankConjecture`, assuming `ℤ⧸pℤ` subring for odd prime. -/
@[category research solved, AMS 13]
theorem TotalRankConjecture_of_subring (p : ℕ) (h : p.Prime) (ne2 : p ≠ 2)
    (f : ℤ ⧸ Ideal.span {(p : ℤ)} →+* R) :
    2 ^ c ≤ ∑ i ∈ Finset.range (c + 1), (Module.rank R (P.complex.X i)) := by
  sorry

end Arxiv.«1702.02560»
