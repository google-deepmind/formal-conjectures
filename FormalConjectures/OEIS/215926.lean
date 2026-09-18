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
# Smallest deficient multiplier for non-deficiency

For $n \ge 2$, $a(n)$ is the smallest deficient number $k$ such that the product $k \cdot n$ is
non-deficient (i.e., perfect or abundant).

*References:*
- [A215926](https://oeis.org/A215926)
-/

namespace OeisA215926

/-- `sigma1 m` is the sum of divisors of $m$. -/
def sigma1 (m : ℕ) : ℕ :=
  ∑ d ∈ m.divisors, d

/-- `a n` is the smallest deficient number $k$ such that $k \cdot n$ is non-deficient. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | sigma1 k < 2 * k ∧ 2 * (k * n) ≤ sigma1 (k * n)}

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  apply IsLeast.csInf_eq
  refine ⟨by decide, fun x hx => ?_⟩
  by_contra! h
  interval_cases x <;> revert hx <;> decide

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by
  apply IsLeast.csInf_eq
  refine ⟨by decide, fun x hx => ?_⟩
  by_contra! h
  interval_cases x <;> revert hx <;> decide

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by
  apply IsLeast.csInf_eq
  refine ⟨by decide, fun x hx => ?_⟩
  by_contra! h
  interval_cases x <;> revert hx <;> decide

@[category test, AMS 11]
theorem a_5 : a 5 = 4 := by
  apply IsLeast.csInf_eq
  refine ⟨by decide, fun x hx => ?_⟩
  by_contra! h
  interval_cases x <;> revert hx <;> decide

@[category test, AMS 11]
theorem a_6 : a 6 = 1 := by
  apply IsLeast.csInf_eq
  refine ⟨by decide, fun x hx => ?_⟩
  by_contra! h
  interval_cases x
  revert hx
  decide

/-- `A014210 m` is the smallest prime strictly greater than $2^m$. -/
noncomputable def A014210 (m : ℕ) : ℕ :=
  sInf {p : ℕ | 2 ^ m < p ∧ p.Prime}

/--
Conjecture: For every $n \ge 2$, $a(n)$ is $1$, $3$, or a power of $2$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 2 ≤ n) :
    a n = 1 ∨ a n = 3 ∨ (a n).isPowerOfTwo := by
  sorry

/--
Conjecture: The first occurrence of $2^m$ happens at [A014210](https://oeis.org/A014210)$(m)$.

We require $m \ge 1$ because for $m = 0$, the first occurrence of $2^0 = 1$ is at $n = 6$, whereas
$\mathrm{A014210}(0) = 2$ gives $a(2) = 3$.
-/
@[category research open, AMS 11]
theorem conjecture2 (m : ℕ) (hm : 1 ≤ m) :
    IsLeast {n : ℕ | 2 ≤ n ∧ a n = 2 ^ m} (A014210 m) := by
  sorry

end OeisA215926
