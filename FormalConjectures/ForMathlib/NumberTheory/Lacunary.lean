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

import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic.Rify

/-- Say a sequence is lacunary if there exists some $\lambda > 1$ such that
$a_{n+1}/a_n\geq \lambda$ for all $n\geq 1$. -/
def IsLacunary (A : ℕ → ℕ) : Prop :=
  A 0 ≠ 0 ∧ ∃ μ > (1 : ℝ), (∀ n, μ ≤ A (n + 1) / A n)

/-- Every term of a lacunary sequence is positive. -/
theorem IsLacunary.pos {A : ℕ → ℕ} (hA : IsLacunary A) (n : ℕ) : 0 < A n := by
  induction n with
  | zero => exact Nat.pos_iff_ne_zero.mpr hA.left
  | succ n ih =>
    obtain ⟨μ, hμ, hμ'⟩ := hA.right
    specialize hμ' n
    rify at ih ⊢
    rw [le_div_iff₀ ih] at hμ'
    apply lt_trans ih (lt_of_lt_of_le (lt_mul_left ih hμ) hμ')

/-- Every lacunary sequence is strictly increasing. -/
theorem IsLacunary.StrictMono (A : ℕ → ℕ) (hA : IsLacunary A) : StrictMono A := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨μ, hμ, hμ'⟩ := hA.right
  specialize hμ' n
  have H := hA.pos n
  rify at H ⊢
  rw [le_div_iff₀ H] at hμ'
  apply lt_of_lt_of_le (lt_mul_left H hμ) hμ'
