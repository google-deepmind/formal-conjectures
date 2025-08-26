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
# Erdős Problem 707: Embedding Sidon Sets in Perfect Difference Sets

*Reference:* [erdosproblems.com/707](https://www.erdosproblems.com/707)

Let `A ⊆ ℕ` be a finite Sidon set. Is there some set `B` with `A ⊆ B` which is a perfect
difference set modulo `p^2 + p + 1` for some prime power `p`?

This problem is related to Erdős Problem 329 about the maximum density of Sidon sets.
If this conjecture is true, it would imply that the maximum density of Sidon sets is 1.
-/

open Function Set

namespace Erdos707

/-- `B` is a perfect difference set modulo `n` if every non-zero residue mod `n` can be uniquely
expressed in the form `a - b`, where `a, b ∈ B`. -/
def IsPerfectDifferenceSetModulo (B : Set ℕ) (n : ℕ) : Prop :=
  B.offDiag.BijOn (fun (a, b) => (a - b : ZMod n)) {x : ZMod n | x ≠ 0}

/--
**Erdős Problem 707**: Any finite Sidon set can be embedded in a perfect difference set modulo
`p^2 + p + 1` for some prime power `p`.
-/
@[category research open, AMS 5 11]
theorem erdos_707 : (∀ (A : Set ℕ) (h : A.Finite), IsSidon A →
    ∃ (B : Set ℕ) (p : ℕ), IsPrimePow p ∧ A ⊆ B ∧
    IsPerfectDifferenceSetModulo B (p^2 + p + 1)) ↔ answer(sorry) := by
  sorry

/--
The smallest prime power `p` for which some finite Sidon set can be embedded in a perfect
difference set modulo `p^2 + p + 1`.
-/
@[category research open, AMS 5 11]
theorem erdos_707.variants.smallest_prime :
    sInf {p : ℕ | IsPrimePow p ∧ ∃ (A : Set ℕ) (B : Set ℕ), A.Finite ∧ IsSidon A ∧
      A ⊆ B ∧ IsPerfectDifferenceSetModulo B (p^2 + p + 1)} =
    answer(sorry) := by
  sorry

/--
A constructive version asking for explicit bounds on the size of `p` in terms of `|A|`.
-/
@[category research open, AMS 5 11]
theorem erdos_707.variants.constructive : (∃ (f : ℕ → ℕ), ∀ (A : Set ℕ) (h : A.Finite),
    IsSidon A → ∃ (B : Set ℕ) (p : ℕ), IsPrimePow p ∧ p ≤ f A.ncard ∧ A ⊆ B ∧
    IsPerfectDifferenceSetModulo B (p^2 + p + 1)) ↔ answer(sorry) := by
  sorry

/--
A weaker version asking for any modulus, not necessarily of the form `p^2 + p + 1`.
-/
@[category research open, AMS 5 11]
theorem erdos_707.variants.weaker : (∀ (A : Set ℕ) (h : A.Finite), IsSidon A →
    ∃ (B : Set ℕ) (n : ℕ), A ⊆ B ∧ IsPerfectDifferenceSetModulo B n) ↔ answer(sorry) := by
  sorry

/-! ## Perfect difference sets and their properties -/

/--
A perfect difference set modulo `n` must have size `≤ √n + 1`.
-/
@[category undergraduate, AMS 5 11]
theorem erdos_707.variants.perfect_difference_set_size_bound (B : Set ℕ) (n : ℕ)
    (hB : IsPerfectDifferenceSetModulo B n) : B.ncard ≤ n.sqrt + 1 := by
  sorry

/--
The Singer construction gives perfect difference sets for `n = p^2 + p + 1` where `p` is a
prime power.
-/
@[category undergraduate, AMS 5 11]
theorem erdos_707.variants.singer_construction (p : ℕ) (hp : IsPrimePow p) :
    ∃ (B : Set ℕ), IsPerfectDifferenceSetModulo B (p^2 + p + 1) ∧ B.ncard = p + 1 := by
  sorry

/-! ## Examples and special cases -/

/--
The set `{1, 2, 4}` is a Sidon set.
-/
@[category undergraduate, AMS 5 11]
theorem erdos_707.variants.example_sidon_set : IsSidon {1, 2, 4} := by
  sorry

/--
The set `{1, 2, 4}` can be embedded in a perfect difference set modulo 7.
-/
@[category undergraduate, AMS 5 11]
theorem erdos_707.variants.example_embedding : ∃ (B : Set ℕ), {1, 2, 4} ⊆ B ∧
    IsPerfectDifferenceSetModulo B 7 := by
  sorry

/--
For small Sidon sets, we can check the conjecture directly.
-/
@[category undergraduate, AMS 5 11]
theorem erdos_707.variants.small_sidon_sets (A : Set ℕ) (hA : A.Finite) (h : A.ncard ≤ 3)
    (hSidon : IsSidon A) : ∃ (B : Set ℕ) (p : ℕ), IsPrimePow p ∧ A ⊆ B ∧
    IsPerfectDifferenceSetModulo B (p^2 + p + 1) := by
  sorry

end Erdos707
