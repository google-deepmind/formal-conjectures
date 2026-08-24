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
# Primes congruent to $\{3, 5, 6\} \pmod 7$

Primes congruent to $3, 5, \text{ or } 6 \pmod 7$.

*References:*
- [A003625](https://oeis.org/A003625)
-/

namespace OeisA3625

/-- A prime $p$ is in A003625 if $p \equiv 3, 5, \text{ or } 6 \pmod 7$. -/
def A (p : ℕ) : Prop :=
  p.Prime ∧ (p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6)

open Polynomial

/-- $3$ is in the sequence A003625. -/
@[category test, AMS 11]
theorem a_3 : A 3 := by
  unfold A
  decide +native

/-- $5$ is in the sequence A003625. -/
@[category test, AMS 11]
theorem a_5 : A 5 := by
  unfold A
  decide +native

/-- $13$ is in the sequence A003625. -/
@[category test, AMS 11]
theorem a_13 : A 13 := by
  unfold A
  decide +native

/-- $17$ is in the sequence A003625. -/
@[category test, AMS 11]
theorem a_17 : A 17 := by
  unfold A
  decide +native

/-- $19$ is in the sequence A003625. -/
@[category test, AMS 11]
theorem a_19 : A 19 := by
  unfold A
  decide +native

/--
Conjecture: Represents primes $p$ where the polynomial $x^2 + x + 2$ is irreducible over $\text{GF}(p)$.
- _Federico Provvedi_, Jul 21 2018
-/
@[category research open, AMS 11 12]
theorem conjecture (p : ℕ) (hp : p.Prime) :
    A p ↔ Irreducible (X ^ 2 + X + 2 : (ZMod p)[X]) := by
  sorry

end OeisA3625
