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
import FormalConjecturesForMathlib.NumberTheory.AdditivelyComplete

/-!
# Erdős Problem 246

*Reference:* [erdosproblems.com/246](https://www.erdosproblems.com/246)

Let $a, b \geq 2$ with $\gcd(a, b) = 1$. Then the set of all numbers of the form
$a^k \cdot b^\ell$ (with $k, \ell \geq 0$) is complete: every sufficiently large positive
integer can be written as a sum of distinct elements of this set.

[Er61] Erdős, P.

[Bi59] Birch, B. J., _Note on a problem of Erdős_. Proc. Cambridge Philos. Soc. (1959), 370–373.

[Ca60] Cassels, J. W. S., _On the representation of integers as the sums of distinct summands
taken from a fixed set_. Acta Sci. Math. (Szeged) (1960), 111–124.

[He00b] Hegyvári, N., _On the completeness of an exponential type sequence_. Acta Math. Hungar.
(2000), 127–135.

[FaCh17] Fang, J.-H., Chen, Y.-G., _A quantitative form of the Erdős–Birch theorem_. Acta Arith.
(2017), 301–311.

[Yu24] Yu, W.-X., _On the representation of an exponential type sequence_. Publ. Math. Debrecen
(2024), 253–261.
-/

namespace Erdos246

/-- The set of all natural numbers of the form $a^k \cdot b^\ell$ for $k, \ell \geq 0$. -/
def powerProductSet (a b : ℕ) : Set ℕ :=
  {n : ℕ | ∃ k l : ℕ, n = a ^ k * b ^ l}

/--
Erdős Problem 246 [Er61] (proved by Birch [Bi59]):
Let $a, b \geq 2$ with $\gcd(a, b) = 1$. Then every sufficiently large positive integer
is the sum of distinct integers of the form $a^k \cdot b^\ell$ with $k, \ell \geq 0$.

This also follows from a later more general result of Cassels [Ca60] (see Problem 254).
-/
@[category research solved, AMS 5 11]
theorem erdos_246 :
    ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → Nat.Coprime a b →
      IsAddComplete (powerProductSet a b) := by
  sorry

end Erdos246
