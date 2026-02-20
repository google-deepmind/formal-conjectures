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
# Erdős Problem 1142

*References:*
- [erdosproblems.com/1142](https://www.erdosproblems.com/1142)
- [A039669](https://oeis.org/A039669)
- [Va99] Various, Some of Paul's favorite problems. Booklet produced for the conference "Paul Erdős
  and his mathematics", Budapest, July 1999 (1999).
- [MiWe69] Mientka, W. E. and Weitzenkamp, R. C., On f-plentiful numbers, Journal of
  Combinatorial Theory, Volume 7, Issue 4, December 1969, pages 374-377.

Are there infinitely many $n$ such that $n - 2^k$ is prime for all $k \geq 1$ with $2^k < n$?
The known such $n$ are $4, 7, 15, 21, 45, 75, 105$ (OEIS A039669).
Mientka and Weitzenkamp have proved there are no other such $n \leq 2^{44}$.
-/

open Nat Set

namespace Erdos1142

/--
The property that $n - 2^k$ is prime for all $k \geq 1$ with $2^k < n$.
-/
def Erdos1142Prop (n : ℕ) : Prop :=
  ∀ k, 0 < k → 2 ^ k < n → (n - 2 ^ k).Prime

/--
Are there infinitely many $n > 2$ such that $n - 2^k$ is prime for all $k \geq 1$ with $2^k < n$?

The only known such $n$ are $4, 7, 15, 21, 45, 75, 105$ (OEIS [A039669](https://oeis.org/A039669)).
-/
@[category research open, AMS 11]
theorem erdos_1142 :
    answer(sorry) ↔ Infinite { n | Erdos1142Prop n } := by
  sorry

/--
Mientka and Weitzenkamp [MiWe69] proved that the only $n \leq 2^{44}$ such that $n - 2^k$ is prime
for all $k \geq 1$ with $2^k < n$ are $4, 7, 15, 21, 45, 75, 105$.
-/
@[category research solved, AMS 11]
theorem erdos_1142.variants.mientka_weitzenkamp :
    { n : ℕ | n ≤ 2 ^ 44 ∧ Erdos1142Prop n } = {4, 7, 15, 21, 45, 75, 105} := by
  sorry

/-- $4$ satisfies the Erdős 1142 property: $4 - 2 = 2$ is prime. -/
@[category test, AMS 11]
theorem erdos_1142.test_4 : Erdos1142Prop 4 := by
  intro k hk hlt
  have hle : k ≤ 1 := by
    by_contra h; push_neg at h
    exact absurd (Nat.pow_le_pow_right (by omega : 1 ≤ 2) h) (by omega)
  interval_cases k; simp_all (config := { decide := true })

/-- $7$ satisfies the Erdős 1142 property. -/
@[category test, AMS 11]
theorem erdos_1142.test_7 : Erdos1142Prop 7 := by
  intro k hk hlt
  have hle : k ≤ 2 := by
    by_contra h; push_neg at h
    exact absurd (Nat.pow_le_pow_right (by omega : 1 ≤ 2) h) (by omega)
  interval_cases k <;> simp_all (config := { decide := true })

/-- $105$ satisfies the Erdős 1142 property: the largest known example. -/
@[category test, AMS 11]
theorem erdos_1142.test_105 : Erdos1142Prop 105 := by
  intro k hk hlt
  have hle : k ≤ 6 := by
    by_contra h; push_neg at h
    exact absurd (Nat.pow_le_pow_right (by omega : 1 ≤ 2) h) (by omega)
  interval_cases k <;> simp_all (config := { decide := true })

/-- $106$ does not satisfy the Erdős 1142 property ($106 - 2 = 104 = 8 \times 13$). -/
@[category test, AMS 11]
theorem erdos_1142.test_not_106 : ¬ Erdos1142Prop 106 := by
  intro h
  have := h 1 (by omega) (by omega)
  revert this; decide

end Erdos1142
