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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 881

*Reference:* [erdosproblems.com/881](https://www.erdosproblems.com/881)
-/

@[expose] public section

open Set

namespace Erdos881

/--
We interpret "additive basis of order `k`" as an asymptotic additive basis of order `k`,
using the predicate `Set.IsAsymptoticAddBasisOfOrder` from additive combinatorics.

A *minimal* additive basis of order `k` is a set `A` such that
* `A` is an asymptotic additive basis of order `k`, and
* for every infinite subset `B ⊆ A`, the complement `A \ B` is *not*
  an asymptotic additive basis of order `k`.
-/
def IsMinimalAsymptoticAddBasisOfOrder (k : ℕ) (A : Set ℕ) : Prop :=
  A.IsAsymptoticAddBasisOfOrder k ∧
    ∀ ⦃B : Set ℕ⦄, B ⊆ A → B.Infinite → ¬ (A \ B).IsAsymptoticAddBasisOfOrder k

/--
Let `A ⊂ ℕ` be an additive basis of order `k` which is minimal in the sense that
if `B ⊂ A` is any infinite set, then `A \ B` is not a basis of order `k`.

Must there exist an infinite `B ⊂ A` such that `A \ B`
is an additive basis of order `k + 1`?
-/
@[category research open, question, AMS 5 11]
theorem erdos_881 :
    ∀ (k : ℕ) (A : Set ℕ),
      IsMinimalAsymptoticAddBasisOfOrder k A →
        ∃ (B : Set ℕ), B ⊆ A ∧ B.Infinite ∧
          (A \ B).IsAsymptoticAddBasisOfOrder (k + 1) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
The case `k = 2` has a positive answer.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/BruceLoveLee000/erdos-lean-proofs/blob/10a88193254999351c81476a304e673291ce1e76/ErdosProofs/Erdos881/K2.lean#L711"]
theorem erdos_881.variants.two :
    ∀ A : Set ℕ, IsMinimalAsymptoticAddBasisOfOrder 2 A →
      ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ (A \ B).IsAsymptoticAddBasisOfOrder 3 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
The case `k = 2` holds without minimality: every asymptotic additive basis of order `2` contains
an infinite set whose removal leaves an asymptotic additive basis of order `3`.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/BruceLoveLee000/erdos-lean-proofs/blob/10a88193254999351c81476a304e673291ce1e76/ErdosProofs/Erdos881/K2.lean#L691"]
theorem erdos_881.variants.two_of_basis :
    ∀ A : Set ℕ, A.IsAsymptoticAddBasisOfOrder 2 →
      ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ (A \ B).IsAsymptoticAddBasisOfOrder 3 := by
  sorry

end Erdos881
