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
# Infinitude and reciprocal convergence of Keith numbers

Defined by Mike Keith (1987) as *repfigit* numbers, an integer $N \ge b$ written in base $b \ge 2$
using $k \ge 2$ digits $d_0, \dots, d_{k-1}$ (most-significant digit first) is a base-$b$ Keith
integer when $N$ appears in the $k$-step Fibonacci-style recurrence initialized by $a_i = d_i$
($0 \le i < k$) and $a_m = \sum_{j=1}^k a_{m-j}$ ($m \ge k$). While base $2$ has infinitely many
examples (including $2^r$ for every $r \ge 1$), Martin Klazar and Florian Luca (2007) proved that
base-$10$ Keith integers have a convergent reciprocal sum, and whether infinitely many base-$10$
Keith integers exist (`OEIS A007629`) remains open.

*References:*
- [Wikipedia: Keith number](https://en.wikipedia.org/wiki/Keith_number)
- [OEIS A007629](https://oeis.org/A007629)
- M. Keith (1987), J. Recreational Math. **19**, no. 1, 41–42.
- M. Klazar and F. Luca (2007), J. Integer Seq. **10**, Article 07.2.2.
-/

@[expose] public section

namespace KeithNumber

/-- Advances the sliding $k$-term recurrence window by dropping its oldest entry and appending the
window sum. -/
def keithWindowStep (w : List ℕ) : List ℕ :=
  w.tail ++ [w.sum]

/-- Predicate asserting that $N \ge b$ in base $b \ge 2$ appears in the $k$-step recurrence seeded
by its base-$b$ digits (most-significant digit first). -/
def IsKeithNumberBase (b N : ℕ) : Prop :=
  2 ≤ b ∧ b ≤ N ∧
    ∃ m : ℕ, 1 ≤ m ∧ ((keithWindowStep^[m]) (Nat.digits b N).reverse).getLast? = some N

/-- Base-$10$ Keith integers (`OEIS A007629`), requiring $N \ge 10$ to exclude single-digit
integers. -/
abbrev IsKeithNumber : ℕ → Prop := IsKeithNumberBase 10

/-- `keithWindowStep` preserves the length of every nonempty window. -/
@[category API, AMS 11]
theorem keithWindowStep_length {w : List ℕ} (hw : w ≠ []) :
    (keithWindowStep w).length = w.length := by
  rcases w with _ | ⟨_, _⟩
  · exact False.elim (hw rfl)
  · simp [keithWindowStep]

/-- Once a two-element window `[a, b]` has `1 ≤ a` and `N < b`, no later iterate ends at `N`. -/
@[category API, AMS 11]
theorem two_elem_window_overshoot {a b N : ℕ} (ha : 1 ≤ a) (hb : N < b) :
    ∀ j : ℕ, ((keithWindowStep^[j]) [a, b]).getLast? ≠ some N := by
  have hiter : ∀ j : ℕ, ∃ x y : ℕ, 1 ≤ x ∧ N < y ∧ (keithWindowStep^[j]) [a, b] = [x, y] := by
    intro j
    induction j with
    | zero => exact ⟨a, b, ha, hb, rfl⟩
    | succ j ih =>
      obtain ⟨x, y, hx, hy, heq⟩ := ih
      refine ⟨y, x + y, by omega, by omega, ?_⟩
      rw [Function.iterate_succ_apply', heq]
      rfl
  intro j
  obtain ⟨_, y, _, hy, heq⟩ := hiter j
  rw [heq]
  simp [ne_of_gt hy]

/-- Verifies base-$10$ examples $14, 19, 28, 47, 197$, Wikipedia's base-$6$ example $88$,
single-digit exclusion ($n < 10$), and non-membership of $10$ and $15$. -/
@[category test, AMS 11]
theorem isKeithNumber_examples_and_nonmembers :
    IsKeithNumber 14 ∧ IsKeithNumber 19 ∧ IsKeithNumber 28 ∧ IsKeithNumber 47 ∧
      IsKeithNumber 197 ∧ IsKeithNumberBase 6 88 ∧
      (∀ n < 10, ¬ IsKeithNumber n) ∧ ¬ IsKeithNumber 10 ∧ ¬ IsKeithNumber 15 := by
  refine ⟨⟨by omega, by omega, 3, by omega, by decide⟩,
    ⟨by omega, by omega, 2, by omega, by decide⟩,
    ⟨by omega, by omega, 3, by omega, by decide⟩,
    ⟨by omega, by omega, 4, by omega, by decide⟩,
    ⟨by omega, by omega, 5, by omega, by decide⟩,
    ⟨by omega, by omega, 5, by omega, by decide⟩,
    fun n hn h ↦ absurd h.2.1 (by omega), ?_, ?_⟩
  · rintro ⟨_, _, m, hm1, hlast⟩
    rw [show (Nat.digits 10 10).reverse = [1, 0] by norm_num] at hlast
    by_cases hm7 : m < 7
    · interval_cases m <;> revert hlast <;> decide
    · rw [show m = (m - 7) + 0 + 7 by omega, Function.iterate_add_apply] at hlast
      exact two_elem_window_overshoot (a := 8) (b := 13) (by omega) (by omega) (m - 7) hlast
  · rintro ⟨_, _, m, hm1, hlast⟩
    rw [show (Nat.digits 10 15).reverse = [1, 5] by norm_num] at hlast
    by_cases hm3 : m < 3
    · interval_cases m <;> revert hlast <;> decide
    · rw [show m = (m - 3) + 0 + 3 by omega, Function.iterate_add_apply] at hlast
      exact two_elem_window_overshoot (a := 11) (b := 17) (by omega) (by omega) (m - 3) hlast

/-- Infinitely many base-$2$ Keith integers exist (for example $2^r$ for every $r \ge 1$). -/
@[category textbook, AMS 11]
theorem keith_numbers_base_two_infinite :
    {N : ℕ | IsKeithNumberBase 2 N}.Infinite := by
  sorry

/--
Klazar–Luca reciprocal convergence theorem (2007): reciprocals of base-$10$ Keith integers form a
summable real series.
-/
@[category research solved, AMS 11]
theorem klazar_luca_keith_reciprocals_summable :
    Summable (fun N : {n : ℕ | IsKeithNumber n} ↦ (1 : ℝ) / (N.1 : ℝ)) := by
  sorry

/--
Do infinitely many base-$10$ Keith integers exist ([OEIS A007629](https://oeis.org/A007629))?
-/
@[category research open, question, AMS 11]
theorem keith_numbers_infinite :
    {N : ℕ | IsKeithNumber N}.Infinite := by
  sorry

end KeithNumber
