/-
Copyright 2025 The Formal Conjectures Authors.

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

universe u

open CategoryTheory

/-- The `Buchsbaum-Eisenbud-Horrocks Conjecture` about lower bound of Betti number. -/
@[category research open, AMS 13]
theorem BuchsbaumEisenbudHorrocksConjecture (R : Type u) [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M]
    (P : ProjectiveResolution M) (fin : ∃ n, ∀ i > n, Limits.IsZero (P.complex.X i))
    (c : ℕ) (ceq : c = Ideal.height (Module.annihilator R M)) :
    ∀ i, c.choose i ≤ Module.rank R (P.complex.X i) := by
  sorry
