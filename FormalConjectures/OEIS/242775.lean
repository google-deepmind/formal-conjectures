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
# Smallest $k \ge 1$ such that the concatenation of $k$ threes and $\text{prime}(n)$ is prime

Let $b_k = 3 \dots 3$ consist of $k \ge 1$ threes in base $10$. The sequence $a(n)$ is the smallest
$k \ge 1$ such that the decimal concatenation of $b_k$ and $\text{prime}(n)$ is prime, or
$a(n) = 0$ if no such prime exists.

*References:*
- [A242775](https://oeis.org/A242775)
-/

namespace OeisA242775

/-- The number formed by concatenating $k$ threes with $p$ in base $10$. -/
def concatThrees (k p : ℕ) : ℕ :=
  ((10 ^ k - 1) / 3) * (10 ^ (Nat.digits 10 p).length) + p

/-- Smallest $k \ge 1$ such that the concatenation of $k$ threes and $\text{prime}(n)$ is prime,
or $0$ if no such prime exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else sInf {k : ℕ | 0 < k ∧ Nat.Prime (concatThrees k (Nat.nth Nat.Prime (n - 1)))}

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by
  have h3 : Nat.nth Nat.Prime 3 = 7 := Nat.nth_prime_three_eq_seven
  simp only [a, OfNat.ofNat_ne_zero, ↓reduceIte, show 4 - 1 = 3 by rfl, h3]
  exact IsLeast.csInf_eq ⟨by native_decide, fun x hx => hx.1⟩

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by
  have h4 : Nat.nth Nat.Prime 4 = 11 := Nat.nth_prime_four_eq_eleven
  simp only [a, OfNat.ofNat_ne_zero, ↓reduceIte, show 5 - 1 = 4 by rfl, h4]
  exact IsLeast.csInf_eq ⟨by native_decide, fun x hx => hx.1⟩

/-- Value of the sequence `a` at 6. -/
@[category test, AMS 11]
theorem a_6 : a 6 = 1 := by
  have h5 : Nat.nth Nat.Prime 5 = 13 := Nat.nth_count (by decide : (13).Prime)
  simp only [a, OfNat.ofNat_ne_zero, ↓reduceIte, show 6 - 1 = 5 by rfl, h5]
  exact IsLeast.csInf_eq ⟨by native_decide, fun x hx => hx.1⟩

/-- Value of the sequence `a` at 7. -/
@[category test, AMS 11]
theorem a_7 : a 7 = 1 := by
  have h6 : Nat.nth Nat.Prime 6 = 17 := Nat.nth_count (by decide : (17).Prime)
  simp only [a, OfNat.ofNat_ne_zero, ↓reduceIte, show 7 - 1 = 6 by rfl, h6]
  exact IsLeast.csInf_eq ⟨by native_decide, fun x hx => hx.1⟩

/-- Value of the sequence `a` at 8. -/
@[category test, AMS 11]
theorem a_8 : a 8 = 2 := by
  have h7 : Nat.nth Nat.Prime 7 = 19 := Nat.nth_count (by decide : (19).Prime)
  simp only [a, OfNat.ofNat_ne_zero, ↓reduceIte, show 8 - 1 = 7 by rfl, h7]
  apply IsLeast.csInf_eq
  refine ⟨by native_decide, fun x hx => ?_⟩
  rcases hx with ⟨hx1, hx2⟩
  by_contra! hlt
  have hx_eq : x = 1 := by omega
  subst hx_eq
  exact absurd hx2 (by native_decide)

/--
Conjecture: For $n \ge 4$, $a(n) > 0$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 4 ≤ n) : 0 < a n := by
  sorry

end OeisA242775
