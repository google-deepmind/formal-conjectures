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
public import FormalConjectures.Wikipedia.ABC

#click_suggestions
/-!
# $n$-Conjecture
We state the first formulation of the $n$-Conjecture.
If $n ≥ 3$ and $a₁, ..., aₙ$ are integers such that
  (i) $GCD(a₁, ..., aₙ) = 1,$
  (ii) $a₁ + ... + aₙ = 0,$ and
  (iii) no proper subsum of $a₁, ..., aₙ$ equals $0$,
then for every $ε > 0,$ there is a constant $C$ depending on $ε$ and $n$ such that
    $max(|a₁|, ..., |aₙ|) < C · rad(|a₁| ⋯ |aₙ|)^{2n - 5 + ε}.$

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/N_conjecture)
-/

@[expose] public section

open UniqueFactorizationMonoid Real

namespace nConjecture


/--
The $n$-Conjecture is a statement about an integer $n$ greater than or equal to 3
and a sequence of integers $a₁, ..., aₙ$ with the properties that
  (i) $GCD(a₁, ..., aₙ) = 1,$
  (ii) $a₁ + ... + aₙ = 0,$ and
  (iii) no proper subsum of $a₁, ..., aₙ$ equals $0$.
-/

def nConjectureValidInput {ι: Type} [Fintype ι] (a : ι → ℤ) : Prop :=
  Fintype.card ι ≥ 3
  ∧
  Finset.gcd Finset.univ a = 1
  ∧
  ∑ i : ι, a i = 0
  ∧
  ∀ S : Finset ι , S ≠ ι ∧ S ≠ ∅ → ∑ i : S , a i ≠ 0

/--
The $n$-Conjecture: for every $ε > 0,$ there is a constant $C$ depending on $ε$ and $n$ such that
    $max(|a₁|, ..., |aₙ|) < C · rad(|a₁| ⋯ |aₙ|)^{2n - 5 + ε}.$
-/

@[category research open, AMS 11]
theorem n_Conjecture (ε : ℝ) (hε : ε > 0) :
  ∀ m : ℕ, ∃ C : ℝ, ∀ (ι : Type), [Fintype ι] →
  Fintype.card ι = m →
  ∀ (a : ι → ℤ), nConjectureValidInput a →
  Finset.univ.sup (fun i => (a i).natAbs)
    <
    C * radical (∏ i : ι, (a i).natAbs) ^ (2 * (Fintype.card ι) - 5 + ε)
  := by
  sorry

/--
The ABC Conjecture is the $n$-Conjecture for $n = 3$.
-/
@[category test, AMS 11]
theorem generalization_of_ABC :
  (type_of% n_Conjecture) → (type_of% ABC.abc.variants.lt_constant_mul) := by
  sorry



end nConjecture
