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

public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Repunits

For a radix `b` and digit count `n`, `Nat.repunit b n` is the geometric sum
$\sum_{i=0}^{n-1} b^i = 1 + b + \dots + b^{n-1}$, whose base-$b$ expansion (for $b \ge 2$) consists
of `n` ones.

## Main definitions

* `Nat.repunit`: the `n`-digit base-`b` repunit $\sum_{i=0}^{n-1} b^i$.
* `Nat.mul_repunit_eq_pow_sub_one`: the identity
  $(b - 1) \cdot \operatorname{repunit}(b, n) = b^n - 1$.
-/

namespace Nat

/-- The `n`-digit repunit in radix `b`, defined without division as $\sum_{i=0}^{n-1} b^i$. -/
def repunit (b n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, b ^ i

@[simp]
theorem repunit_zero (b : ℕ) : repunit b 0 = 0 := by
  simp [repunit]

@[simp]
theorem repunit_one (b : ℕ) : repunit b 1 = 1 := by
  simp [repunit]

@[simp]
theorem repunit_succ (b n : ℕ) : repunit b (n + 1) = repunit b n + b ^ n :=
  Finset.sum_range_succ (b ^ ·) n

/-- Division-free geometric-sum identity $(b - 1) \sum_{i=0}^{n-1} b^i = b^n - 1$ on `ℕ`. -/
theorem mul_repunit_eq_pow_sub_one (b n : ℕ) : (b - 1) * repunit b n = b ^ n - 1 := by
  by_cases hb : b < 2
  · have hb01 : b = 0 ∨ b = 1 := by omega
    rcases hb01 with rfl | rfl
    · cases n <;> simp [repunit]
    · simp [repunit]
  · obtain ⟨d, rfl⟩ : ∃ d, b = d + 2 := ⟨b - 2, by omega⟩
    have hsub : d + 2 - 1 = d + 1 := by omega
    rw [hsub]
    induction n with
    | zero => simp
    | succ m ih =>
      have hpow : 1 ≤ (d + 2) ^ m := Nat.one_le_pow m (d + 2) (by omega)
      have hmul : (d + 1) * (d + 2) ^ m + (d + 2) ^ m = (d + 2) ^ m * (d + 2) := by
        rw [← Nat.add_one_mul, Nat.mul_comm]
      rw [repunit_succ, Nat.mul_add, ih, pow_succ]
      omega

end Nat
