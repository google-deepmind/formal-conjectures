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
# Erdős Problem 8

*Reference:* [erdosproblems.com/8](https://www.erdosproblems.com/8)
-/

namespace Erdos8

/--
If $\mathbb{Z}$ is finitely coloured, must there exist a covering system - a finite collection of
congruences $a_i \pmod{d_i}$ with distinct moduli that together cover all of $\mathbb{Z}$ - all of
whose moduli $d_i$ have the same colour?

The answer is no. Hough's [Ho15] solution of the minimum modulus problem (cf. `Erdos2`) bounds the
least modulus of any distinct covering system; consequently colouring all integers below $10^{18}$
with distinct colours and all remaining integers with one further colour is a finite colouring for
which no monochromatic covering system exists.

[Ho15] Hough, B., _Solution of the minimum modulus problem for covering systems_.
Ann. of Math. (2) 181 (2015), 361-382.
-/
@[category research solved, AMS 11]
theorem erdos_8 :
    answer(False) ↔
      ∀ (n : ℕ) (color : ℤ → Fin n), ∃ (c : StrictCoveringSystem ℤ) (col : Fin n),
        ∀ i, ∃ m : ℕ, c.moduli i = Ideal.span {(m : ℤ)} ∧ color (m : ℤ) = col := by
  sorry

end Erdos8
