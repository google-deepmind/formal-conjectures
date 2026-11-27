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
# Golomb's self-describing sequence

Golomb's sequence is the nondecreasing positive-integer sequence in which $n$ occurs exactly
$a(n)$ times. It begins $1,2,2,3,3,4,4,4,5,\ldots$ and satisfies
$a(n+2)=1+a(n+2-a(a(n+1)))$. We use its official one-based indexing and extend it by $a(0)=0$.

*References:*
- [A001462](https://oeis.org/A001462)
-/

@[expose] public section

namespace OeisA1462

/-- A recurrence step carrying the index bound and positivity needed by later recursive calls. -/
def valueStep (n : ℕ)
    (prev : ∀ m, m < n → {x : ℕ // x ≤ m ∧ (0 < m → 0 < x)}) :
    {x : ℕ // x ≤ n ∧ (0 < n → 0 < x)} :=
  match n with
  | 0 => ⟨0, by omega⟩
  | 1 => ⟨1, by omega⟩
  | n + 2 => by
      let x := prev (n + 1) (by omega)
      have hx : x.val ≤ n + 1 := x.property.1
      let y := prev x.val (by omega)
      have hy_pos : 0 < y.val := y.property.2 (x.property.2 (by omega))
      have hy_le : y.val ≤ n + 1 := y.property.1.trans hx
      let z := prev (n + 2 - y.val) (by omega)
      have hz : z.val ≤ n + 2 - y.val := z.property.1
      exact ⟨1 + z.val, by constructor <;> omega⟩

/-- The nested recurrence together with certified upper and lower bounds for each index. -/
def boundedValue (n : ℕ) : {x : ℕ // x ≤ n ∧ (0 < n → 0 < x)} :=
  Nat.strongRec valueStep n

/-- Golomb's sequence, with $a(0)=0$ and $a(1)=1$, computed by its nested recurrence. -/
def a (n : ℕ) : ℕ := (boundedValue n).val

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide +kernel

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide +kernel

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by decide +kernel

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by decide +kernel

@[category test, AMS 11]
theorem a_5 : a 5 = 3 := by decide +kernel

@[category test, AMS 11]
theorem a_6 : a 6 = 4 := by decide +kernel

@[category test, AMS 11]
theorem a_7 : a 7 = 4 := by decide +kernel

@[category test, AMS 11]
theorem a_8 : a 8 = 4 := by decide +kernel

@[category test, AMS 11]
theorem a_9 : a 9 = 5 := by decide +kernel

/-- The value at zero is only a total extension of the official sequence. -/
@[category test, AMS 11]
theorem a_zero_extension : a 0 = 0 := by decide +kernel

/-- Each term is bounded by its index, which justifies the nested recursive calls. -/
@[category API, AMS 11]
theorem a_le (n : ℕ) : a n ≤ n := (boundedValue n).property.1

/-- Every official term is positive. -/
@[category API, AMS 11]
theorem a_pos {n : ℕ} (hn : 0 < n) : 0 < a n := (boundedValue n).property.2 hn

/-- The final recursive index is positive and strictly smaller than the new index. -/
@[category API, AMS 11]
theorem recurrence_index_bounds (n : ℕ) :
    1 ≤ n + 2 - a (a (n + 1)) ∧ n + 2 - a (a (n + 1)) ≤ n + 1 := by
  have hx := a_le (n + 1)
  have hx_pos := a_pos (by omega : 0 < n + 1)
  have hy := a_le (a (n + 1))
  have hy_pos := a_pos hx_pos
  omega

/-- The public sequence satisfies the recurrence recorded in the OEIS formula field. -/
@[category API, AMS 11]
theorem a_add_two (n : ℕ) : a (n + 2) = 1 + a (n + 2 - a (a (n + 1))) := by
  unfold a
  rw [boundedValue, Nat.strongRec_eq]
  rfl

/-- The bound is exact at the first official index. -/
@[category test, AMS 11]
theorem lower_bound_one : (1 : ℝ) ^ (Real.goldenRatio - 1) ≤ (a 1 : ℝ) := by
  simp [a_1]

/--
"Conjecture: a(n) >= n^(phi-1) for all n."
— Jianing Song, August 19, 2021, [A001462](https://oeis.org/A001462).

The proposed bound is $a(n) \ge n^{\varphi-1}$ for $n\ge1$,
where $\varphi=(1+\sqrt5)/2$.
-/
@[category research open, AMS 11]
theorem lower_bound :
    ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ (Real.goldenRatio - 1) ≤ (a n : ℝ) := by
  sorry

end OeisA1462
