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
# A quadratic generating function with sign substitution

The sequence consists of the coefficients of $A(x)=1+2xA(x)^2-xA(-x)^2$.

*References:*
- [A368633](https://oeis.org/A368633)
- [Li26] Wentao Li, [Catalan parity for A368633](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/proofs/new-formalization/A368633/PROOF.md), 2026.
-/

@[expose] public section

namespace OeisA368633

/-- Coefficients of the square of a power series with coefficient sequence $b$. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), b k * b (n - k)

/-- Coefficients of $A(x)=1+2xA(x)^2-xA(-x)^2$. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      (if Even n then 3 else 1) * conv2 b (n - 1)

/-- The coefficient recurrence unfolded at an index. -/
@[category API, AMS 11]
theorem a_eq (n : ℕ) :
    a n = if n = 0 then 1 else
      (if Even n then 3 else 1) * conv2 (fun m => if m < n then a m else 0) (n - 1) := by
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
theorem a_2 : a 2 = 6 := by
  rw [a_eq]
  norm_num [conv2, Finset.sum_range_succ, a_0, a_1]

@[category test, AMS 11]
theorem a_3 : a 3 = 13 := by
  rw [a_eq]
  norm_num [conv2, Finset.sum_range_succ, a_0, a_1, a_2]

@[category test, AMS 11]
theorem a_4 : a 4 = 114 := by
  rw [a_eq]
  norm_num [conv2, Finset.sum_range_succ, a_0, a_1, a_2, a_3]

/--
The parity conjecture (Conjecture 1):
"Conjecture: $a(n)$ is odd when $n = 2^k - 1$ for $k \ge 0$ and even elsewhere."
- Paul D. Hanna, Jan 11 2024.

Lean formalization by Wentao Li, with AI assistance; see [Li26].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/LeanOeisProofs/NewFormalization/A368633.lean#L166"]
theorem conjecture_1 (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  sorry

end OeisA368633
