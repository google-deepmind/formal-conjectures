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

-/

open Nat Set

namespace Erdos1142

/--
The property that $n > 2$ and $n - 2^k$ is prime for all $k \geq 1$ with $2^k < n$.

Following the OEIS [A039669](https://oeis.org/A039669) convention ("Numbers n > 2 such that ..."),
we require $n > 2$ to exclude the trivial cases $n \leq 2$, for which the primality condition
is vacuously satisfied.
-/
def Erdos1142Prop (n : ℕ) : Prop :=
  2 < n ∧ ∀ k, 0 < k → 2 ^ k < n → (n - 2 ^ k).Prime

/--
Are there infinitely many $n > 2$ such that $n - 2^k$ is prime for all $k \geq 1$ with $2^k < n$?

The only known such $n$ are $4, 7, 15, 21, 45, 75, 105$ (OEIS [A039669](https://oeis.org/A039669)).
-/
@[category research open, AMS 11]
theorem erdos_1142 :
    answer(sorry) ↔ Infinite { n | Erdos1142Prop n } := by
  sorry

/--
Mientka and Weitzenkamp [MiWe69] proved that the only $n \leq 2^{44}$ such that $n > 2$ and
$n - 2^k$ is prime for all $k \geq 1$ with $2^k < n$ are $4, 7, 15, 21, 45, 75, 105$.
-/
@[category research solved, AMS 11]
theorem erdos_1142.variants.mientka_weitzenkamp :
    { n : ℕ | n ≤ 2 ^ 44 ∧ Erdos1142Prop n } = {4, 7, 15, 21, 45, 75, 105} := by
  sorry
/-- Helper tactic for proving `Erdos1142Prop` for small concrete values. -/
local macro "prove_erdos_1142_prop" bound:num : tactic =>
  `(tactic| (
    refine ⟨by omega, fun k hk hlt => ?_⟩
    have : k ≤ $bound := by
      by_contra h; push_neg at h
      exact absurd (Nat.pow_le_pow_right (by omega : 1 ≤ 2) h) (by omega)
    interval_cases k <;> simp_all (config := { decide := true })))

/-- $4$ satisfies the Erdős 1142 property: $4 - 2 = 2$ is prime. -/
@[category test, AMS 11]
theorem erdos_1142.test_4 : Erdos1142Prop 4 := by prove_erdos_1142_prop 1

/-- $7$ satisfies the Erdős 1142 property: $7 - 2 = 5$ and $7 - 4 = 3$ are prime. -/
@[category test, AMS 11]
theorem erdos_1142.test_7 : Erdos1142Prop 7 := by prove_erdos_1142_prop 2

/-- $15$ satisfies the Erdős 1142 property: $15 - 2 = 13$, $15 - 4 = 11$, $15 - 8 = 7$. -/
@[category test, AMS 11]
theorem erdos_1142.test_15 : Erdos1142Prop 15 := by prove_erdos_1142_prop 3

/-- $21$ satisfies the Erdős 1142 property: $21 - 2 = 19$, $21 - 4 = 17$, $21 - 8 = 13$,
$21 - 16 = 5$. -/
@[category test, AMS 11]
theorem erdos_1142.test_21 : Erdos1142Prop 21 := by prove_erdos_1142_prop 4

/-- $45$ satisfies the Erdős 1142 property: $45 - 2 = 43$, $45 - 4 = 41$, $45 - 8 = 37$,
$45 - 16 = 29$, $45 - 32 = 13$. -/
@[category test, AMS 11]
theorem erdos_1142.test_45 : Erdos1142Prop 45 := by prove_erdos_1142_prop 5

/-- $75$ satisfies the Erdős 1142 property: $75 - 2 = 73$, $75 - 4 = 71$, $75 - 8 = 67$,
$75 - 16 = 59$, $75 - 32 = 43$, $75 - 64 = 11$. -/
@[category test, AMS 11]
theorem erdos_1142.test_75 : Erdos1142Prop 75 := by prove_erdos_1142_prop 6

/-- $105$ satisfies the Erdős 1142 property: the largest known example.
$105 - 2 = 103$, $105 - 4 = 101$, $105 - 8 = 97$, $105 - 16 = 89$, $105 - 32 = 73$,
$105 - 64 = 41$. -/
@[category test, AMS 11]
theorem erdos_1142.test_105 : Erdos1142Prop 105 := by prove_erdos_1142_prop 6

/-- $106$ does not satisfy the Erdős 1142 property ($106 - 2 = 104 = 8 \times 13$). -/
@[category test, AMS 11]
theorem erdos_1142.test_not_106 : ¬ Erdos1142Prop 106 := by
  intro ⟨_, h⟩
  have := h 1 (by omega) (by omega)
  revert this; decide

end Erdos1142
