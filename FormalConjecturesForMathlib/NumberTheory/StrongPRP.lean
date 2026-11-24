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

public import Mathlib.Data.ZMod.Basic

/-!
# Base-2 strong probable primes

This file defines the base-$2$ strong Fermat probable prime predicate `IsStrongBaseTwoPRP`
(Miller–Rabin condition in base $2$, whose composite witnesses form OEIS A001262).
-/

@[expose] public section

/-- Base-$2$ strong probable prime condition on an odd integer $n \ge 3$: writing
$n - 1 = 2^s \cdot d$ with $d$ odd, either $2^d \equiv 1 \pmod{n}$ or $2^{2^r d} \equiv -1
\pmod{n}$ for some $0 \le r < s$. -/
def IsStrongBaseTwoPRP (n : ℕ) : Prop :=
  3 ≤ n ∧ Odd n ∧
    ∃ s d : ℕ, Odd d ∧ n - 1 = 2 ^ s * d ∧
      ((2 : ZMod n) ^ d = 1 ∨ ∃ r < s, (2 : ZMod n) ^ (2 ^ r * d) = -1)

theorem IsStrongBaseTwoPRP.three_le {n : ℕ} (h : IsStrongBaseTwoPRP n) : 3 ≤ n :=
  h.1

theorem IsStrongBaseTwoPRP.odd {n : ℕ} (h : IsStrongBaseTwoPRP n) : Odd n :=
  h.2.1
