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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 478

*Reference:* [erdosproblems.com/478](https://www.erdosproblems.com/478)

For a prime `p`, let `A_p = {k! mod p : 1 ≤ k < p}`.  Is it true that
`|A_p| ∼ (1 - 1/e) p`?
-/

noncomputable section

namespace Erdos478

open Classical Filter

/-- The residue set `{k! mod p : 1 ≤ k < p}`. -/
def factorialResidues (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (p - 1)).image fun k => Nat.factorial k % p

/-- The conjectured asymptotic size of the factorial residue set modulo primes. -/
def Erdos478Conjecture : Prop :=
  ∀ ε : ℝ,
    0 < ε →
      ∀ᶠ p in atTop,
        Nat.Prime p →
          |((factorialResidues p).card : ℝ) / (p : ℝ) -
              (1 - (Real.exp 1)⁻¹)| < ε

/-- Is `|{k! mod p : 1 ≤ k < p}| ∼ (1 - 1/e) p` along the primes? -/
@[category research open, AMS 11]
theorem erdos_478 : answer(sorry) ↔ Erdos478Conjecture := by
  sorry

end Erdos478

end
