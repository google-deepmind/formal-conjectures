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
import FormalConjecturesForMathlib.Data.Set.Density
import FormalConjecturesForMathlib.Combinatorics.AP.Basic

/-!
# Erdős Problem 16

*Reference:* [erdosproblems.com/16](https://www.erdosproblems.com/16)

Erdős [Er50] showed that the set of odd integers not of the form $2^k + p$ (with $p$ prime)
contains an infinite arithmetic progression, and asked whether this set is the union of an
infinite AP and a density-zero set. Chen [Ch23] proved it is not.

[Er50] Erdős, P., _On integers of the form $2^k + p$ and some related problems_. Summa Brasil.
Math. **2** (1950), 113–123.

[Er95] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Combinatorics '94 (1995), 167–189.

[Ch23] Chen, J., _The set of odd integers not of the form $2^k + p$ is not the union of an
infinite arithmetic progression and a density-zero set_ (2023).

OEIS: [A006285](https://oeis.org/A006285) — Odd numbers not of the form $2^k + p$.
-/

namespace Erdos16

/--
The set of odd positive integers that cannot be expressed as $2^k + p$ for any
non-negative integer $k$ and any prime $p$.
-/
def oddNotPowerOfTwoPlusPrime : Set ℕ :=
  {n : ℕ | Odd n ∧ ∀ (k : ℕ) (p : ℕ), Nat.Prime p → n ≠ 2 ^ k + p}

/--
The set of odd integers not of the form $2^k + p$ (where $p$ is prime and $k \geq 0$)
is **not** the union of an infinite arithmetic progression and a set of natural density zero.

Erdős [Er95, p.167] asked whether this set equals $AP \cup D$ for some infinite arithmetic
progression $AP$ and density-zero set $D$, calling the conjecture 'rather silly'. Using covering
congruences, Erdős [Er50] showed this set contains an infinite arithmetic progression.
Chen [Ch23] resolved the question negatively.
-/
@[category research solved, AMS 11]
theorem erdos_16 : answer(False) ↔
    ∃ (AP D : Set ℕ),
      AP.IsAPOfLength ⊤ ∧
      D.HasDensity 0 ∧
      oddNotPowerOfTwoPlusPrime = AP ∪ D := by
  sorry

end Erdos16
