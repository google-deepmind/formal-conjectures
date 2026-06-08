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
# Erdős Problem 1214

*References:*
- [erdosproblems.com/1214](https://www.erdosproblems.com/1214)
- [CoSc97] Corrales-Rodrigáñez, Capi and Schoof, René, The support problem and its
  elliptic analogue. J. Number Theory (1997) [Volume 64, Issue 2], 276--290.
-/

namespace Erdos1214

/--
Let $x,y\geq 1$ be integers such that, for all $n\geq 1$, the set of primes dividing $x^{n}-1$ is
equal to the set of primes dividing $y^n-1$. Must $x=y$?

Erdős asked this at a 1988 number theory conference in Banff.

A positive answer was given by Corrales-Rodrigáñez and Schoof [CoSc97].
-/
@[category research solved, AMS 11]
theorem erdos_1214 :
    answer(True) ↔ ∀ x y : ℕ, x ≥ 1 → y ≥ 1 →
      (∀ n : ℕ, n ≥ 1 → { p : ℕ | p.Prime ∧ p ∣ x ^ n - 1 } = { p : ℕ | p.Prime ∧ p ∣ y ^ n - 1 }) →
      x = y := by
  sorry

end Erdos1214
