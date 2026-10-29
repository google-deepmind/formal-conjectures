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
# A generating function with signed square terms

The sequence consists of the coefficients of
$A(x)=1+x(3A(x)^2-A(-x)^2)/2$.

*References:*
- [A368634](https://oeis.org/A368634)
- [Li26] Wentao Li, [Generating-function bridge and parity for A368634](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/9d4a205da2a4094800f9c600a7b0b5223eda51ce/proofs/new-proofs/A368634/PROOF.md), 2026.
-/

@[expose] public section

namespace OeisA368634

/-- Coefficients of the square of a power series with coefficient sequence $b$. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), b k * b (n - k)

/-- Coefficients of $A(x)=1+x(3A(x)^2-A(-x)^2)/2$. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      (if Even n then 2 else 1) * conv2 b (n - 1)

/-- The coefficient recurrence unfolded at an index. -/
@[category API, AMS 11]
theorem a_eq (n : ℕ) :
    a n = if n = 0 then 1 else
      (if Even n then 2 else 1) * conv2 (fun m => if m < n then a m else 0) (n - 1) := by
  rw [a, Nat.strongRec_eq]
  simp only [a, dite_eq_ite]

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  rw [a_eq]
  norm_num

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  rw [a_eq]
  norm_num [conv2, Finset.sum_range_succ, a_0]

@[category test, AMS 11]
theorem a_2 : a 2 = 4 := by
  rw [a_eq]
  norm_num [conv2, Finset.sum_range_succ, a_0, a_1]

@[category test, AMS 11]
theorem a_3 : a 3 = 9 := by
  rw [a_eq]
  norm_num [conv2, Finset.sum_range_succ, a_0, a_1, a_2]

@[category test, AMS 11]
theorem a_4 : a 4 = 52 := by
  rw [a_eq]
  norm_num [conv2, Finset.sum_range_succ, a_0, a_1, a_2, a_3]

@[category test, AMS 11]
theorem a_5 : a 5 = 138 := by
  rw [a_eq]
  norm_num [conv2, Finset.sum_range_succ, a_0, a_1, a_2, a_3, a_4]

set_option linter.style.formal_proof_palomar false in
/--
"Conjecture: $a(n)$ is odd when $n = 2^k - 1$ for $k \ge 0$ and even elsewhere."
- Paul D. Hanna, Jan 12 2024.

Lean proof by Wentao Li, with AI assistance; see [Li26].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/9d4a205da2a4094800f9c600a7b0b5223eda51ce/LeanOeisProofs/NewProofs/A368634.lean#L407"]
theorem conjecture (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  sorry

end OeisA368634
