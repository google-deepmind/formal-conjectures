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
# Erdős Problem 2

*References:*
- [erdosproblems.com/2](https://www.erdosproblems.com/2)
- [Ho15] Hough, B., *Solution of the minimum modulus problem for covering systems*. Ann. of Math.
  (2) **181** (2015), 361-382.
- [BBMST22] Balister, P., Bollobás, B., Morris, R., Sahasrabudhe, J. and Tiba, M., *On the Erdős
  Covering Problem: the density of the uncovered set*. Invent. Math. **228** (2022), 377-414.
- [PALOMAR-2026-10-05-000002](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-05-000002&version=1)

Erdős asked whether the smallest modulus in a distinct covering system can be arbitrarily large.
Hough [Ho15] proved that the answer is no, and Balister, Bollobás, Morris, Sahasrabudhe, and Tiba
[BBMST22] later gave a simpler proof with an improved explicit upper bound.
-/

@[expose] public section

namespace Erdos2

/--
Can the smallest modulus of a covering system be arbitrarily large?

This problem has a negative answer: there is a universal bound on the least modulus of any
distinct covering system.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/linrock/math-proofs/blob/7caa4144741e10f96cf79d6f7313a0efd9a18b67/erdos-2/Solution.lean#L44"]
theorem erdos_2 :
    answer(False) ↔
      ∀ B : ℕ, ∃ c : StrictCoveringSystem ℤ, ∀ i, ∃ m : ℕ,
        c.moduli i = Ideal.span {(m : ℤ)} ∧ B < m := by
  sorry

end Erdos2
