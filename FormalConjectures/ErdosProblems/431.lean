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

/-!
# Erdős Problem 431

*References:*
- [erdosproblems.com/431](https://www.erdosproblems.com/431)
- [OAI26a] OpenAI, *The additive indecomposability of the primes*. OpenAI Math Release preprint
  (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf
-/

@[expose] public section

namespace Erdos431

open scoped Pointwise

open scoped symmDiff

/-- Are there two infinite sets $A$ and $B$ such that $A+B$ agrees with the primes up to finitely
many exceptions?

This was disproved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean
proof. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Ostmann/Complete.lean#L16"]
theorem erdos_431 : answer(False) ↔
    ∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧
      (A + B : Set ℕ) =ᶠ[Filter.cofinite] {n | n.Prime} := by
  sorry

/-- Ostmann's inverse Goldbach conjecture: if $A$ and $B$ each have at least two elements, then
$A+B$ differs from the primes in infinitely many elements.

This was proved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean
proof. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Ostmann/Result.lean#L14"]
theorem erdos_431.variants.ostmann :
    ∀ A B : Set ℕ, A.Nontrivial → B.Nontrivial → ((A + B) ∆ {n | n.Prime}).Infinite := by
  sorry

end Erdos431
