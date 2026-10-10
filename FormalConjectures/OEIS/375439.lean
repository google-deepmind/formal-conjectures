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
# A cubic generating function with ternary substitution

The coefficients of the generating function
$A(x)=x+x^2+(2A(x)^3+A(x^3))/3$, with constant term $a(0)=0$.

*References:*
- [A375439](https://oeis.org/A375439)
- [A038754](https://oeis.org/A038754)
- [Li26] Wentao Li, [Parity of A375439](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/proofs/new-proofs/A375439/PROOF.md), 2026.
-/

@[expose] public section

namespace OeisA375439

/-- Coefficients of the square of a power series with coefficient sequence $b$. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), b k * b (n - k)

/-- Coefficients of the cube of a power series with coefficient sequence $b$. -/
def conv3 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), conv2 b k * b (n - k)

/-- Coefficients obtained by substituting $x^3$ for $x$. -/
def subst3 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  if 3 ∣ n then b (n / 3) else 0

/-- Coefficients of $2B(x)^3+B(x^3)$. -/
def rhs (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * conv3 b n + subst3 b n

/-- Coefficients of $A(x)=x+x^2+(2A(x)^3+A(x^3))/3$, with $a(0)=0$. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 0
    else if n = 1 then 1
    else if n = 2 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      rhs b n / 3

/-- The coefficient recurrence unfolded at an index. -/
@[category API, AMS 11]
theorem a_eq (n : ℕ) :
    a n = if n = 0 then 0 else if n = 1 then 1 else if n = 2 then 1
      else rhs (fun m => if m < n then a m else 0) n / 3 := by
  rw [a, Nat.strongRec_eq]
  simp only [a, dite_eq_ite]

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  rw [a_eq]
  norm_num

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  rw [a_eq]
  norm_num

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  rw [a_eq]
  norm_num

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  rw [a_eq]
  norm_num [rhs, conv3, conv2, subst3, Finset.sum_range_succ, a_0, a_1, a_2]

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by
  rw [a_eq]
  norm_num [rhs, conv3, conv2, subst3, Finset.sum_range_succ, a_0, a_1, a_2, a_3]

@[category test, AMS 11]
theorem a_5 : a 5 = 4 := by
  rw [a_eq]
  norm_num [rhs, conv3, conv2, subst3, Finset.sum_range_succ, a_0, a_1, a_2, a_3, a_4]

@[category test, AMS 11]
theorem a_6 : a 6 = 9 := by
  rw [a_eq]
  norm_num [rhs, conv3, conv2, subst3, Finset.sum_range_succ, a_0, a_1, a_2, a_3, a_4, a_5]

/--
"Conjecture: $a(n)$ is odd iff $n$ is in A038754, which consists of numbers of the form
$3^k$ and $2*3^k$."
- Paul D. Hanna, Aug 21 2024.

Lean proof by Wentao Li, with AI assistance; see [Li26].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/LeanOeisProofs/NewProofs/A375439.lean#L382"]
theorem conjecture (n : ℕ) (hn : 1 ≤ n) :
    Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k := by
  sorry

end OeisA375439
