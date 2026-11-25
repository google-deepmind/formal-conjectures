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
# Keith numbers

Defined by Mike Keith (1987) as *repfigit* numbers, an integer $N \ge b$ written in base $b \ge 2$
using $k \ge 2$ digits $d_0, \dots, d_{k-1}$ (most-significant digit first) is a base-$b$ Keith
integer when $N$ appears in the $k$-step Fibonacci-style recurrence initialized by $a_i = d_i$
($0 \le i < k$) and $a_m = \sum_{j=1}^k a_{m-j}$ ($m \ge k$). Base $2$ admits infinitely many Keith
integers (including $2^r$ for every $r \ge 1$). In base $10$ (`OEIS A007629`), Martin Klazar and
Florian Luca (2007, Theorem 1.2) proved the counting bound $\#\mathcal{K}(x) \ll x / \sqrt{\log x}$
for $x \ge 2$ (which extends to every fixed base $b \ge 4$ and shows natural density zero, though it
does not establish convergence of the reciprocal sum); whether infinitely many base-$10$ Keith
integers exist remains open.

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

/-- $14$ is the smallest base-$10$ Keith integer. -/
@[category test, AMS 11]
theorem isKeithNumber_14 : IsKeithNumber 14 :=
  ⟨by omega, by omega, 3, by omega, by decide⟩

/-- $19$ is a base-$10$ Keith integer. -/
@[category test, AMS 11]
theorem isKeithNumber_19 : IsKeithNumber 19 :=
  ⟨by omega, by omega, 2, by omega, by decide⟩

/-- $28$ is a base-$10$ Keith integer. -/
@[category test, AMS 11]
theorem isKeithNumber_28 : IsKeithNumber 28 :=
  ⟨by omega, by omega, 3, by omega, by decide⟩

/-- $47$ is a base-$10$ Keith integer. -/
@[category test, AMS 11]
theorem isKeithNumber_47 : IsKeithNumber 47 :=
  ⟨by omega, by omega, 4, by omega, by decide⟩

/-- $197$ is a three-digit base-$10$ Keith integer. -/
@[category test, AMS 11]
theorem isKeithNumber_197 : IsKeithNumber 197 :=
  ⟨by omega, by omega, 5, by omega, by decide⟩

/-- $88$ is a base-$6$ Keith integer ($88 = (224)_6$). -/
@[category test, AMS 11]
theorem isKeithNumberBase_6_88 : IsKeithNumberBase 6 88 :=
  ⟨by omega, by omega, 5, by omega, by decide⟩

/-- Single-digit integers $n < 10$ are excluded from `IsKeithNumber`. -/
@[category test, AMS 11]
theorem not_isKeithNumber_of_lt_ten {n : ℕ} (hn : n < 10) : ¬ IsKeithNumber n :=
  fun h ↦ absurd h.2.1 (by omega)

/-- $10$ is not a base-$10$ Keith integer. -/
@[category test, AMS 11]
theorem not_isKeithNumber_10 : ¬ IsKeithNumber 10 := by
  rintro ⟨_, _, m, hm1, hlast⟩
  rw [show (Nat.digits 10 10).reverse = [1, 0] by norm_num] at hlast
  by_cases hm7 : m < 7
  · interval_cases m <;> revert hlast <;> decide
  · rw [show m = (m - 7) + 0 + 7 by omega, Function.iterate_add_apply] at hlast
    exact two_elem_window_overshoot (a := 8) (b := 13) (by omega) (by omega) (m - 7) hlast

/-- $15$ is not a base-$10$ Keith integer. -/
@[category test, AMS 11]
theorem not_isKeithNumber_15 : ¬ IsKeithNumber 15 := by
  rintro ⟨_, _, m, hm1, hlast⟩
  rw [show (Nat.digits 10 15).reverse = [1, 5] by norm_num] at hlast
  by_cases hm3 : m < 3
  · interval_cases m <;> revert hlast <;> decide
  · rw [show m = (m - 3) + 0 + 3 by omega, Function.iterate_add_apply] at hlast
    exact two_elem_window_overshoot (a := 11) (b := 17) (by omega) (by omega) (m - 3) hlast

/-- Infinitely many base-$2$ Keith integers exist (for example $2^r$ for every $r \ge 1$). -/
@[category textbook, AMS 11]
theorem keith_numbers_base_two_infinite :
    {N : ℕ | IsKeithNumberBase 2 N}.Infinite := by
  have hsum : ∀ j : ℕ, 1 + (List.map (2 ^ ·) (List.range j)).sum = 2 ^ j := fun j ↦ by
    induction j with
    | zero => simp
    | succ j ih => rw [List.range_succ]; simp; omega
  have hdig : ∀ k : ℕ, (Nat.digits 2 (2 ^ k)).reverse = 1 :: List.replicate k 0 := fun k ↦ by
    induction k with
    | zero => decide
    | succ k ih =>
      rw [Nat.digits_def' (by omega) (by positivity), pow_succ', Nat.mul_mod_right,
        Nat.mul_div_cancel_left _ (by omega), List.reverse_cons, ih, List.cons_append,
        ← List.replicate_succ']
  refine Set.infinite_of_injective_forall_mem (f := fun r : ℕ ↦ 2 ^ (r + 1))
    (fun a b h ↦ by simpa using Nat.pow_right_injective (by omega) h) fun r ↦ ?_
  set k := r + 1
  have hiter : ∀ j ≤ k, (keithWindowStep^[j]) (List.replicate k 0 ++ [1]) =
      List.replicate (k - j) 0 ++ 1 :: List.map (2 ^ ·) (List.range j) := fun j hj ↦ by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih (by omega), show k - j = k - (j + 1) + 1 by omega,
        List.replicate_succ, List.range_succ]
      simp [keithWindowStep, ← hsum j]
  refine ⟨le_rfl, Nat.le_self_pow (by omega) 2, k + 2, by omega, ?_⟩
  rw [hdig, show k + 2 = (k + 1) + 1 by omega, Function.iterate_succ_apply',
    Function.iterate_succ_apply]
  have hstep1 : keithWindowStep (1 :: List.replicate k 0) = List.replicate k 0 ++ [1] := by
    simp [keithWindowStep]
  rw [hstep1, hiter k le_rfl]
  simp [keithWindowStep, hsum k]

/--
Klazar–Luca counting bound (2007, Theorem 1.2): there exists a constant $C > 0$ such that for every
integer $x \ge 2$, the number of base-$10$ Keith integers at most $x$ satisfies
$$\#\{N \le x : N \text{ is a Keith number}\} \le \frac{C x}{\sqrt{\log x}}.$$
-/
@[category research solved, AMS 11]
theorem klazar_luca_keith_counting_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 2 ≤ x →
      ({N : ℕ | N ≤ x ∧ IsKeithNumber N}.ncard : ℝ) ≤
        C * ((x : ℝ) / Real.sqrt (Real.log (x : ℝ))) := by
  sorry

/--
Do infinitely many base-$10$ Keith integers exist ([OEIS A007629](https://oeis.org/A007629))?
-/
@[category research open, question, AMS 11]
theorem keith_numbers_infinite :
    {N : ℕ | IsKeithNumber N}.Infinite := by
  sorry

end KeithNumber
