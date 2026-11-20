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

public import FormalConjecturesUtil

/-!
# Kynea and Carol Primes

Near-square integers $k_n = (2^n + 1)^2 - 2 = 4^n + 2^{n+1} - 1$ (Kynea numbers, `A093069` for
$n \ge 1$) and $c_n = (2^n - 1)^2 - 2 = 4^n - 2^{n+1} - 1$ (Carol numbers, `A093112` for $n \ge 1$)
were named by Cletus Emmanuel and studied in prime searches (Crandall and Pomerance, 2005). Prime
values of $k_n$ (`A091514`, beginning $2, 7, 23, 79, 1087$ from $n = 0$) and of $c_n$ (`A091516`,
beginning $7, 47, 223, 3967$ from $n = 2$) are conjectured to be infinite; Wikipedia's unsolved
problems list poses the Kynea case directly, and the companion Carol question is likewise open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Prime_numbers)
- [OEIS A091514](https://oeis.org/A091514)
- [OEIS A091516](https://oeis.org/A091516)
- [OEIS A093069](https://oeis.org/A093069)
- [OEIS A093112](https://oeis.org/A093112)
- [MathWorld: Near-Square Prime](https://mathworld.wolfram.com/Near-SquarePrime.html)
- R. Crandall and C. Pomerance, *Prime Numbers: A Computational Perspective*, 2nd ed., Springer,
  New York, 2005, https://doi.org/10.1007/0-387-28979-8.
-/

@[expose] public section

namespace KyneaAndCarolPrime

/-- The $n$-th Carol integer $c_n = (2^n - 1)^2 - 2 \in \mathbb{Z}$ (equal to $-2$ at $n = 0$,
$-1$ at $n = 1$, and positive for $n \ge 2$). -/
def carolNumber (n : ℕ) : ℤ :=
  ((2 : ℤ) ^ n - 1) ^ 2 - 2

/-- The $n$-th Kynea number $k_n = (2^n + 1)^2 - 2 \in \mathbb{N}$. -/
def kyneaNumber (n : ℕ) : ℕ :=
  (2 ^ n + 1) ^ 2 - 2

/-- Index predicate asserting that $c_n = (2^n - 1)^2 - 2$ is a positive prime integer. -/
abbrev IsCarolPrimeIndex (n : ℕ) : Prop :=
  0 < carolNumber n ∧ (carolNumber n).toNat.Prime

/-- Index predicate asserting that $k_n = (2^n + 1)^2 - 2$ is prime. -/
abbrev IsKyneaPrimeIndex (n : ℕ) : Prop :=
  (kyneaNumber n).Prime

/-- Every Kynea number satisfies $k_n \ge 2$, avoiding $\mathbb{N}$-subtraction truncation. -/
@[category API, AMS 11]
theorem two_le_kyneaNumber (n : ℕ) : 2 ≤ kyneaNumber n := by
  unfold kyneaNumber
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hsq : 4 ≤ (2 ^ n + 1) ^ 2 := by nlinarith
  omega

/-- Boundary values at $n = 0, 1$: $c_0 = -2$ and $c_1 = -1$, whereas $k_0 = 2$ is prime. -/
@[category test, AMS 11]
theorem carol_and_kynea_boundary_values :
    carolNumber 0 = -2 ∧ carolNumber 1 = -1 ∧ ¬ IsCarolPrimeIndex 0 ∧ ¬ IsCarolPrimeIndex 1 ∧
      kyneaNumber 0 = 2 ∧ IsKyneaPrimeIndex 0 := by
  decide

/-- Small Carol checks: $c_2 = 7$, $c_3 = 47$, and $c_4 = 223$ are prime; $c_5 = 959$ is not. -/
@[category test, AMS 11]
theorem carol_small_witnesses :
    IsCarolPrimeIndex 2 ∧ IsCarolPrimeIndex 3 ∧ IsCarolPrimeIndex 4 ∧ ¬ IsCarolPrimeIndex 5 := by
  simp [IsCarolPrimeIndex, carolNumber]
  norm_num

/-- Small Kynea checks: $k_1 = 7$, $k_2 = 23$, and $k_3 = 79$ are prime; $k_4 = 287$ is not. -/
@[category test, AMS 11]
theorem kynea_small_witnesses :
    IsKyneaPrimeIndex 1 ∧ IsKyneaPrimeIndex 2 ∧ IsKyneaPrimeIndex 3 ∧ ¬ IsKyneaPrimeIndex 4 := by
  unfold IsKyneaPrimeIndex kyneaNumber
  norm_num

/--
Do infinitely many positive integers $n$ yield a prime Kynea number $(2^n + 1)^2 - 2$?
-/
@[category research open, question, AMS 11]
theorem infinitely_many_kynea_primes : {n : ℕ | 1 ≤ n ∧ IsKyneaPrimeIndex n}.Infinite := by
  sorry

/--
Do infinitely many natural numbers $n$ yield a prime Carol number $(2^n - 1)^2 - 2$?
-/
@[category research open, question, AMS 11]
theorem infinitely_many_carol_primes : {n : ℕ | IsCarolPrimeIndex n}.Infinite := by
  sorry

end KyneaAndCarolPrime
