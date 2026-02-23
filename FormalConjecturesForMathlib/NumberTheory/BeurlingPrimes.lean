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

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Defs

/-!
# Beurling primes

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Beurling_zeta_function)
 - [Beurling Zeta Functions, Generalised Primes, and Fractal Membranes](https://arxiv.org/abs/math/0410270)
-/

open Filter

/-- A sequence of real numbers `1 < a 0 < a 1 < ...` is called a set of Beurling prime numbers if
it tends to infinity. -/
noncomputable def IsBeurlingPrimes (a : ℕ → ℝ) : Prop :=
  1 < a 0 ∧ StrictMono a ∧ Tendsto a atTop atTop

/-- The set of Beurling integers are numbers of the form `∏ i, (a i) ^ (k i)`, where `k` has
finite support. -/
def BeurlingInteger (a : ℕ → ℝ) : Set ℝ :=
  letI g : (ℕ →₀ ℕ) → ℝ := fun k => k.prod (fun x y => (a x) ^ y)
  .range g

/-- Every element of the sequence `a` is a Beurling integer. -/
lemma generator_mem_beurling (a : ℕ → ℝ) (i : ℕ) : a i ∈ BeurlingInteger a :=
  ⟨Finsupp.single i 1, by aesop⟩

/-- The set of Beurling integers is closed under multiplication. -/
lemma mul_mem_beurling {a : ℕ → ℝ} {x y : ℝ} (hx : x ∈ BeurlingInteger a) (hy : y ∈ BeurlingInteger a) :
    x * y ∈ BeurlingInteger a := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨l, rfl⟩ := hy
  exact ⟨k + l, by simp [Finsupp.prod_add_index', pow_add]⟩

/-- The set of Beurling integers is closed under taking powers. -/
lemma pow_mem_beurling {a : ℕ → ℝ} {x : ℝ} (k : ℕ) (hx : x ∈ BeurlingInteger a) :
    x ^ k ∈ BeurlingInteger a := by
  induction k with
  | zero => exact ⟨0, by norm_num⟩
  | succ k ih => simpa [pow_succ'] using mul_mem_beurling hx ih
