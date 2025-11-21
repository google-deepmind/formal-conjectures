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
import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 972

*Reference:* [erdosproblems.com/972](https://www.erdosproblems.com/972)
-/

namespace Erdos972

/--
The set of primes `p` such that `floor (α * p)` is also prime.
-/
def bothPrimes (α : ℝ) : Set ℕ :=
{p : ℕ | Nat.Prime p ∧ Nat.Prime ((Int.floor (α * p)).toNat)}

/--
Let $\alpha > 1$ be irrational. Are there infinitely many primes $p$
such that $\lfloor p\alpha \rfloor$ is also prime?
-/

@[category research open, AMS 11]
theorem erdos_972 (α : ℝ) : 1 < α → Irrational α → (bothPrimes α).Infinite ↔ answer(sorry) := by
  sorry

end Erdos972
