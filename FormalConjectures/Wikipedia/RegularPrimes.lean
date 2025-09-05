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

import FormalConjectures.Util.ProblemImports

/-!
# Infinite Regular Primes

We define the notion of regular primes, which are prime numbers that are coprime with the
cardinality of the class group of the `p`-th cyclotomic field. We also state that there are
infinitely many regular primes.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Regular_prime)
-/

open scoped NumberField

noncomputable section

variable (p : ℕ)

namespace RegularPrimes

/-- TODO: remove this once mathlib is updated as it seems that in this version of mathlib
we need to do this manually. -/
instance [hp : Fact p.Prime]  : NumberField (CyclotomicField ⟨p, hp.out.pos⟩ ℚ) :=
  IsCyclotomicExtension.numberField {⟨p, hp.out.pos⟩} ℚ _

/-- A natural prime number `p` is regular if `p` is coprime with the order of the class group
of the `p`-th cyclotomic field. -/
def IsRegularPrime [hp : Fact p.Prime] : Prop :=
  p.Coprime <| Fintype.card <| ClassGroup (𝓞 <| CyclotomicField ⟨p, hp.out.pos⟩ ℚ)

@[category undergraduate, AMS 11]
theorem not_isRegularPrime_37_first : ¬ @IsRegularPrime 37 (by decide) := by
  sorry

/-- The set of regular primes. -/
def regularPrimes : Set ℕ := { p | ∃ (hp : Nat.Prime p), @IsRegularPrime p ⟨hp⟩ }

/-- The set of irregular primes. -/
def irregularPrimes : Set ℕ := { p | ∃ (hp : Nat.Prime p), ¬ @IsRegularPrime p ⟨hp⟩ }

@[category undergraduate, AMS 11]
lemma small_regular_primes :
    { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31 } ⊆ regularPrimes := by
  sorry

@[category undergraduate, AMS 11]
theorem not_isRegularPrime_37_second : ¬ @IsRegularPrime 37 (by decide) := by
  sorry

/-- An equivanlent definitions of regualr prime `p` is that it does not divide the numerator of the
first `p-3` Bernoulli numbers. Not in Mathlib. -/
@[category graduate, AMS 11]
theorem isRegularPrime_iff_Bernoulli (p : ℕ) [Fact p.Prime] :
    IsRegularPrime p ↔ ∀ k ∈ Finset.Icc 2 (p - 3), ¬ (p : ℤ) ∣ (bernoulli' k).num := by
  sorry

/-- The set of irregular primes is infinite. -/
@[category research solved, AMS 11]
theorem infinitude_of_irregularprimes : irregularPrimes.Infinite := by
  sorry

/-- Conjecture: The set of regular primes is infinite. -/
def RegularPrimeConjecture : Prop :=
  regularPrimes.Infinite

/-- Conjecture: The set of regular primes is infinite. -/
@[category research open, AMS 11]
theorem regularprime_conjecture : RegularPrimeConjecture := by
  sorry

end RegularPrimes
