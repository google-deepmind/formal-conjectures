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
# A generating function with powers two and four

The sequence consists of the coefficients of
$A(x)=1+x(A(x)^2-A(-x)^2)/2+x(A(x)^4+A(-x)^4)/2$.

*References:*
- [A368628](https://oeis.org/A368628)
- [Li26] Wentao Li, [Generating-function bridge and parity for A368628](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/b5eabe63ce276d12170d18f91b5b7327130c4cbe/proofs/new-formalization/A368628/PROOF.md), 2026.
-/

@[expose] public section

namespace OeisA368628

/-- Coefficients of the square of a power series with coefficient sequence $b$. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), b k * b (n - k)

/-- Coefficients of the fourth power of a power series with coefficient sequence $b$. -/
def conv4 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  conv2 (conv2 b) n

/-- Coefficients of $A(x)=1+x(A(x)^2-A(-x)^2)/2+x(A(x)^4+A(-x)^4)/2$. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      if Even n then conv2 b (n - 1) else conv4 b (n - 1)

/-- The coefficient recurrence unfolded at an index. -/
@[category API, AMS 11]
theorem a_eq (n : ℕ) :
    a n = if n = 0 then 1 else
      if Even n then conv2 (fun m => if m < n then a m else 0) (n - 1)
      else conv4 (fun m => if m < n then a m else 0) (n - 1) := by
  rw [a, Nat.strongRec_eq]
  simp only [a, dite_eq_ite]

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  rw [a_eq]
  norm_num

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  rw [a_eq]
  norm_num [conv4, conv2, Finset.sum_range_succ, a_0]

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  rw [a_eq]
  norm_num [conv4, conv2, Finset.sum_range_succ, a_0, a_1]

@[category test, AMS 11]
theorem a_3 : a 3 = 14 := by
  rw [a_eq]
  norm_num [conv4, conv2, Finset.sum_range_succ, a_0, a_1, a_2]

@[category test, AMS 11]
theorem a_4 : a 4 = 32 := by
  rw [a_eq]
  norm_num [conv4, conv2, Finset.sum_range_succ, a_0, a_1, a_2, a_3]

@[category test, AMS 11]
theorem a_5 : a 5 = 345 := by
  rw [a_eq]
  norm_num [conv4, conv2, Finset.sum_range_succ, a_0, a_1, a_2, a_3, a_4]

set_option linter.style.formal_proof_palomar false in
/--
"Conjecture: $a(n)$ is odd when $n = (4^k - 1)/3$ for $k \ge 0$, and even elsewhere."
- Paul D. Hanna, Jan 10 2024.

Lean formalization by Wentao Li, with AI assistance; see [Li26].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/b5eabe63ce276d12170d18f91b5b7327130c4cbe/LeanOeisProofs/NewFormalization/A368628.lean#L523"]
theorem conjecture (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n = (4 ^ k - 1) / 3 := by
  sorry

end OeisA368628
