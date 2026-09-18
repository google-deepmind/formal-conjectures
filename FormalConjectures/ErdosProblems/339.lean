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
# Erdős Problem 339

*References:*
- [erdosproblems.com/339](https://www.erdosproblems.com/339)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [HHP03] Hegyvári, N., Hennecart, F. and Plagne, A., *A proof of two Erdős conjectures on
  restricted addition and further results*. J. Reine Angew. Math. 560 (2003), 199-220.
-/

open Function

namespace Erdos339

/-- The set of sums of exactly `r` pairwise distinct elements of `A`. -/
def restrictedSums (r : ℕ) (A : Set ℕ) : Set ℕ :=
  {n | ∃ f : Fin r → ℕ, Injective f ∧ (∀ i, f i ∈ A) ∧ ∑ i, f i = n}

/--
Let $A \subseteq \mathbb{N}$ be a basis of order $r$. Must the set of integers representable as
the sum of exactly $r$ distinct elements from $A$ have positive lower density?

A question of Erdős and Graham [ErGr80, p.52]. The answer is yes, proved by Hegyvári, Hennecart
and Plagne [HHP03].
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos339.lean#L456"]
theorem erdos_339 : answer(True) ↔
    ∀ (A : Set ℕ) (r : ℕ), A.IsAsymptoticAddBasisOfOrder r →
      0 < (restrictedSums r A).lowerDensity := by
  sorry

end Erdos339
