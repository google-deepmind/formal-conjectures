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
# A differential generating function

The generating function satisfies $A(x)=x+(xA(x)^2)'$. Its constant term is zero.
Seiichi Manyama's recurrence is $a(1)=1$ and
$a(n)=(n+1)\sum_{k=1}^{n-1}a(k)a(n-k)$ for $n>1$.

*References:*
- [A397588](https://oeis.org/A397588)
- [Li26] Wentao Li, [Parity and divisibility for A397588](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/proofs/new-formalization/A397588/PROOF.md), 2026.
-/

@[expose] public section

namespace OeisA397588

/-- Manyama's coefficient recurrence, extended by $a(0)=0$. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    (n + 3) * ∑ k ∈ (Finset.Icc 1 (n + 1)).attach, a k.1 * a (n + 2 - k.1)
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_of_le (Finset.mem_Icc.mp k.2).2
  · exact Nat.sub_lt (Nat.succ_pos _) (Finset.mem_Icc.mp k.2).1

/-- The recurrence without attached membership proofs. -/
@[category API, AMS 11]
theorem a_succ_succ (n : ℕ) :
    a (n + 2) = (n + 3) * ∑ k ∈ Finset.Icc 1 (n + 1), a k * a (n + 2 - k) := by
  simp only [a]
  exact congrArg (fun t => (n + 3) * t)
    (Finset.sum_attach (Finset.Icc 1 (n + 1)) (fun k => a k * a (n + 2 - k)))

/-- Manyama's recurrence for every index greater than one. -/
@[category API, AMS 11]
theorem a_of_gt_one {n : ℕ} (hn : 1 < n) :
    a n = (n + 1) * ∑ k ∈ Finset.Icc 1 (n - 1), a k * a (n - k) := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n => simp [a_succ_succ]

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  simp only [a]

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  simp only [a]

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  have hI : Finset.Icc (1 : ℕ) (2 - 1) = {1} := by decide
  rw [a_of_gt_one (by decide : 1 < 2), hI]
  norm_num [a_1]

@[category test, AMS 11]
theorem a_3 : a 3 = 24 := by
  have hI : Finset.Icc (1 : ℕ) (3 - 1) = {1, 2} := by decide
  rw [a_of_gt_one (by decide : 1 < 3), hI]
  norm_num [a_1, a_2]

@[category test, AMS 11]
theorem a_4 : a 4 = 285 := by
  have hI : Finset.Icc (1 : ℕ) (4 - 1) = {1, 2, 3} := by decide
  rw [a_of_gt_one (by decide : 1 < 4), hI]
  norm_num [a_1, a_2, a_3]

@[category test, AMS 11]
theorem a_5 : a 5 = 4284 := by
  have hI : Finset.Icc (1 : ℕ) (5 - 1) = {1, 2, 3, 4} := by decide
  rw [a_of_gt_one (by decide : 1 < 5), hI]
  norm_num [a_1, a_2, a_3, a_4]

/--
"Conjecture: $a(n)$ is odd iff $n$ is a power of $2$ for $n \ge 1$."
- Paul D. Hanna, Jul 03 2026.

Lean formalization by Wentao Li, with AI assistance; see [Li26].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/LeanOeisProofs/NewFormalization/A397588.lean#L211"]
theorem conjecture_parity (n : ℕ) (hn : 1 ≤ n) :
    Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k := by
  sorry

/--
"$a(n)$ divisible by $3$ for $n > 1$."
- Paul D. Hanna, Jul 03 2026.

Lean formalization by Wentao Li, with AI assistance; see [Li26].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/LeanOeisProofs/NewFormalization/A397588.lean#L325"]
theorem three_dvd_a (n : ℕ) (hn : 1 < n) : 3 ∣ a n := by
  sorry

end OeisA397588
