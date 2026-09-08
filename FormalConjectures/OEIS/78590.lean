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
# $a(1)=1, a(2)=1, a(n)=(2^{a(n-1)} + 1)/a(n-2)$

The sequence is defined by $a(1) = 1, a(2) = 1$, and for $n \ge 3$,
$$a(n) = \frac{2^{a(n-1)} + 1}{a(n-2)}$$

*References:*
- [A078590](https://oeis.org/A078590)-/

namespace OeisA78590

/-- $a(1)=1, a(2)=1, a(n)=(2^{a(n-1)} + 1)/a(n-2)$. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => (2 ^ a (n + 2) + 1) / a (n + 1)

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by
  rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 9 := by
  rfl

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 171 := by
  rfl

/-- Are all terms integers? -/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 3 ≤ n) : a (n - 2) ∣ 2 ^ a (n - 1) + 1 := by
  sorry

/--
Counterexample at `n = 7`: `a 5 = 171` does not divide `2 ^ a 6 + 1`,
so `a 7 = (2 ^ a 6 + 1) / a 5` is not an integer. In particular the
divisibility claimed by `conjecture` fails at `n = 7`.
Proof: writing `c = a 6 = (2 ^ 171 + 1) / 9`, we have `c ≡ 3 [MOD 18]`,
hence `2 ^ c ≡ 2 ^ 3 = 8 [MOD 19]`, so `2 ^ c + 1 ≡ 9 [MOD 19]`;
since `19 ∣ 171`, `171` cannot divide `2 ^ c + 1`.
-/
@[category research solved, AMS 11]
theorem conjecture_counterexample : ¬ (a 5 ∣ 2 ^ a 6 + 1) := by
  have h5 : a 5 = 171 := a_5
  have h6 : a 6 = (2 ^ 171 + 1) / 9 := by
    have h : a 6 = (2 ^ a 5 + 1) / a 4 := rfl
    rw [h, a_5, a_4]
  rw [h5, h6]
  have hmod : ((2 ^ 171 + 1) / 9) % 18 = 3 := by decide
  have h19 : (2 : ℕ) ^ 18 % 19 = 1 := by decide
  have h171 : 19 ∣ 171 := by decide
  obtain ⟨q, hq⟩ : ∃ q, (2 ^ 171 + 1) / 9 = 18 * q + 3 :=
    ⟨(2 ^ 171 + 1) / 9 / 18, by omega⟩
  intro hdvd
  have h19dvd : 19 ∣ 2 ^ ((2 ^ 171 + 1) / 9) + 1 := dvd_trans h171 hdvd
  have hpow : (2 : ℕ) ^ ((2 ^ 171 + 1) / 9) % 19 = 8 := by
    conv_lhs => rw [hq, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod, h19]
    simp
  have h9 : (2 ^ ((2 ^ 171 + 1) / 9) + 1) % 19 = 9 := by
    rw [Nat.add_mod, hpow]
  have hz : (2 ^ ((2 ^ 171 + 1) / 9) + 1) ≡ 0 [MOD 19] :=
    Nat.modEq_zero_iff_dvd.mpr h19dvd
  have h9' : (2 ^ ((2 ^ 171 + 1) / 9) + 1) ≡ 9 [MOD 19] := h9
  exact absurd (hz.symm.trans h9') (by decide)

end OeisA78590
