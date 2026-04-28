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
# Erdős Problem 405

*Reference:* [erdosproblems.com/405](https://www.erdosproblems.com/405)
-/

open scoped Nat

namespace Erdos405

/--
Let $p$ be an odd prime. Is it true that the equation $(p-1)!+a^{p-1}=p^k$ has only finitely many
solutions?
-/
@[category research solved, AMS 11]
theorem erdos_405 :
    Set.Finite { x : ℕ × ℕ × ℕ | let (a, k, p) := x; p.Prime ∧ Odd p ∧
      Nat.factorial (p - 1) + a ^ (p - 1) = p ^ k} := by
  sorry

/--
Yu and Liu showed that the only solutions to (p-1)! + a^(p-1) = p^k
for an odd prime p are:
2! + 1^2 = 3
2! + 5^2 = 3^3
4! + 1^4 = 5^2
-/
@[category research solved, AMS 11]
theorem erdos_405_yu_liu :
    { x : ℕ × ℕ × ℕ | let (a, k, p) := x; p.Prime ∧ Odd p ∧
      Nat.factorial (p - 1) + a ^ (p - 1) = p ^ k } =
    {(1, 1, 3), (5, 3, 3), (1, 2, 5)} := by
  sorry

end Erdos405
