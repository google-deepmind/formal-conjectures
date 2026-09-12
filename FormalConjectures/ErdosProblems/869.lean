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
# Erdős Problem 869

*References:*
- [erdosproblems.com/869](https://www.erdosproblems.com/869)
- [ErNa88] Erdős, Paul and Nathanson, Melvyn B., *Partitions of bases into disjoint unions of
  bases*. J. Number Theory (1988), 1-9.
- [Ha56] Härtter, Erich, *Ein Beitrag zur Theorie der Minimalbasen*. J. Reine Angew. Math.
  (1956), 170-204.
- [Na74] Nathanson, Melvyn B., *Minimal bases and maximal nonbases in additive number theory*.
  J. Number Theory (1974), 324-333.
-/

open Set

namespace Erdos869

/--
An asymptotic additive basis of order `h` is minimal when removing any element leaves infinitely
many integers not representable as a sum of `h` elements.
-/
def MinAsymptoticAddBasisOfOrder (A : Set ℕ) (h : ℕ) : Prop :=
  IsAsymptoticAddBasisOfOrder A h ∧ ∀ n ∈ A, ¬ IsAsymptoticAddBasisOfOrder (A \ {n}) h

/--
If $A_1,A_2$ are disjoint additive bases of order $2$ (i.e. $A_i+A_i$ contains all large integers)
then must $A=A_1\cup A_2$ contain a minimal additive basis of order $2$ (one such that deleting
any element creates infinitely many $n\not\in A+A$)?
-/
@[category research open, AMS 5 11]
theorem erdos_869 : answer(sorry) ↔
    ∀ (A₁ A₂ : Set ℕ), Disjoint A₁ A₂ →
      IsAsymptoticAddBasisOfOrder A₁ 2 →
      IsAsymptoticAddBasisOfOrder A₂ 2 →
      ∃ B ⊆ A₁ ∪ A₂, MinAsymptoticAddBasisOfOrder B 2 := by
  sorry

/--
Härtter and Nathanson proved that there exist additive bases which do not contain any minimal
additive bases.
-/
@[category research solved, AMS 5 11]
theorem erdos_869.variants.hartter_nathanson :
    ∃ (A : Set ℕ) (h : ℕ), IsAsymptoticAddBasisOfOrder A h ∧
      ∀ B ⊆ A, ¬ MinAsymptoticAddBasisOfOrder B h := by
  sorry

end Erdos869
