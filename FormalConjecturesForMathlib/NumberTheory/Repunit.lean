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
public import Mathlib.Data.Nat.Digits.Defs

/-!
# Decimal repunits

This file defines `repunit10 n`, the decimal repunit of length `n`, and computes its base-`10`
digit list.
-/

@[expose] public section

/-- The decimal repunit of length $n$, defined as $1 + 10 + \cdots + 10^{n-1}$. -/
def repunit10 (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, 10 ^ i

/-- The base-$10$ digits of the length-$n$ decimal repunit `repunit10 n` consist of $n$ ones. -/
@[simp]
theorem digits_repunit10 (n : ℕ) :
    Nat.digits 10 (repunit10 n) = List.replicate n 1 := by
  have hval : repunit10 n = Nat.ofDigits 10 (List.replicate n 1) := by
    induction n with
    | zero => simp [repunit10]
    | succ k ih =>
      have hsum : repunit10 (k + 1) = 1 + 10 * repunit10 k := by
        unfold repunit10
        rw [Finset.sum_range_succ']
        simp only [pow_zero, pow_succ', ← Finset.mul_sum]
        omega
      rw [hsum, ih, List.replicate_succ, Nat.ofDigits]
      rfl
  rw [hval]
  refine Nat.digits_ofDigits 10 (by omega) _ (fun d hd => ?_) (fun hne => ?_)
  · simp [List.mem_replicate.mp hd]
  · obtain ⟨_, h1⟩ := List.mem_replicate.mp (List.getLast_mem hne)
    omega
