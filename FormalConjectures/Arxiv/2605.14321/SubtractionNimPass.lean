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
# A subtraction Nim with a pass

*References:*
- [arxiv/2605.14321](https://arxiv.org/abs/2605.14321)
  **A Subtraction Nim with a Pass** by *Urban Larsson, Hikaru Manabe, Ryohei Miyadera* (2026)

In the subtraction Nim with subtraction set `S`, a move removes `s ∈ S` stones from a single pile
of `x ≥ s` stones; the player who cannot move loses. Write `G(x, 0)` for the Grundy number of a
pile of `x` stones. With a *pass*, a player may instead, once in the whole game, pass the turn;
the pass is not allowed from the empty pile, and once used it is gone. Writing `G(x, 1)` for the
Grundy number of a pile of `x` stones while the pass is still available,
$$G(x, 1) = \operatorname{mex}\{G(x - s, 1) : s \in S,\ s \le x\} \cup \{G(x, 0) : x > 0\}.$$

The paper proves that for `S = {2, 4n, 4n + 2}` with `n ≥ 3`, the Grundy numbers have the
*reverse-mex property* `G(x) = mex {G(x + s) : s ∈ S}`, and that for large `x` the pass no longer
matters: `G(x, 1) = mex {G(x - s, 1) : s ∈ S}`. It then conjectures the same behaviour for three
families, for all `a, n ≥ 1`:
* (a) `S = {a, 2an, 2an + a}`, from `x ≥ 6an + 4a + 1` on;
* (b) `S = {a, (2n + 1)a, (2n + 3)a}`, from `x ≥ (2n + 3)a + 1` on, with `G(x, 1) < 4`;
* (c) `S = {a, (2n + 1)a, (2n + 5)a}`, from `x ≥ (2n + 5)a + 1` on, with `G(x, 1) < 4`.

All three statements fail for the smallest values of `n`:
* (a) with `a = 1`, `n = 2`, i.e. `S = {1, 4, 5}`: `G(18, 1) = 4`, but
  `mex {G(17, 1), G(14, 1), G(13, 1)} = mex {2, 3, 1} = 0`;
* (b) with `a = 1`, `n = 1`, i.e. `S = {1, 3, 5}`: `G(6, 1) = 1`, but
  `mex {G(5, 1), G(3, 1), G(1, 1)} = mex {2} = 0`;
* (c) with `a = 1`, `n = 2`, i.e. `S = {1, 5, 9}`: `G(10, 1) = 1`, but
  `mex {G(9, 1), G(5, 1), G(1, 1)} = mex {2} = 0`.

In each case the pass to `G(x, 0) = 0` is what raises the Grundy number. Computations for
`a ≤ 7` suggest that these are the only failures: (a) fails only for `n = 2`, (b) only for
`n = 1`, and (c) only for `n = 2`. The corrected statements are recorded as open variants.
-/

@[expose] public section

namespace Arxiv.«2605.14321»

open Finset

/-- The minimal excludant of a finite set of natural numbers. -/
def mex (s : Finset ℕ) : ℕ := Nat.find (Infinite.exists_notMem_finset s)

/-- The Grundy number `G(x, 0)` of a pile of `x` stones in the subtraction Nim with subtraction
set `S` (without a pass). -/
def grundy (S : Finset ℕ) (x : ℕ) : ℕ :=
  mex ((S.filter fun s => 0 < s ∧ s ≤ x).attach.image fun s => grundy S (x - s.1))
termination_by x
decreasing_by
  have := s.2
  simp only [Finset.mem_filter] at this
  omega

/-- The Grundy number `G(x, 1)` of a pile of `x` stones when the one-time pass is still available:
the options are the subtraction moves (keeping the pass) and, if `x > 0`, the pass, which leads to
`G(x, 0)`. -/
def grundyPass (S : Finset ℕ) (x : ℕ) : ℕ :=
  mex (((S.filter fun s => 0 < s ∧ s ≤ x).attach.image fun s => grundyPass S (x - s.1)) ∪
    if 0 < x then {grundy S x} else ∅)
termination_by x
decreasing_by
  have := s.2
  simp only [Finset.mem_filter] at this
  omega

/-- The value `mex {G(x - s, 1) : s ∈ S, s ≤ x}` obtained by ignoring the pass at `x`. -/
def grundyPassNoPass (S : Finset ℕ) (x : ℕ) : ℕ :=
  mex ((S.filter fun s => s ≤ x).image fun s => grundyPass S (x - s))

/-- The behaviour conjectured in the paper for the subtraction set `S`, starting from `x₀`:
the reverse-mex property for `G(x, 0)` for all `x`, and for `x ≥ x₀` both
`G(x, 1) = mex {G(x - s, 1) : s ∈ S}` and the reverse-mex property for `G(x, 1)`. -/
def Conjectured (S : Finset ℕ) (x₀ : ℕ) : Prop :=
  (∀ x, grundy S x = mex (S.image fun s => grundy S (x + s))) ∧
  ∀ x ≥ x₀, grundyPass S x = grundyPassNoPass S x ∧
    grundyPass S x = mex (S.image fun s => grundyPass S (x + s))

@[category test, AMS 5 91]
theorem mex_example : mex {0, 1, 3} = 2 := by native_decide

/-- The paper's table for `S = {2, 4n, 4n + 2}` with `n = 3`: `G(x, 1)` for `x = 0, …, 15`. -/
@[category test, AMS 5 91]
theorem grundyPass_two_twelve_fourteen :
    (List.range 16).map (grundyPass {2, 12, 14}) =
      [0, 1, 2, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 3, 4, 2] := by
  native_decide

/-- **Conjecture (a).** For `a, n ≥ 1` and `S = {a, 2an, 2an + a}`, the conjectured behaviour holds
from `x = 6an + 4a + 1` on. False for `a = 1`, `n = 2`. -/
@[category research solved, AMS 5 91]
theorem conjecture_a :
    ¬ ∀ a n : ℕ, 0 < a → 0 < n →
      Conjectured {a, 2 * a * n, 2 * a * n + a} (6 * a * n + 4 * a + 1) := by
  intro h
  have h18 := ((h 1 2 one_pos two_pos).2 18 (by norm_num)).1
  have : grundyPass {1, 4, 5} 18 = 4 ∧ grundyPassNoPass {1, 4, 5} 18 = 0 := by native_decide
  norm_num at h18
  omega

/-- **Conjecture (b).** For `a, n ≥ 1` and `S = {a, (2n + 1)a, (2n + 3)a}`, the conjectured
behaviour holds from `x = (2n + 3)a + 1` on, and `G(x, 1) < 4` for all `x`. False for `a = 1`,
`n = 1`. -/
@[category research solved, AMS 5 91]
theorem conjecture_b :
    ¬ ∀ a n : ℕ, 0 < a → 0 < n →
      Conjectured {a, (2 * n + 1) * a, (2 * n + 3) * a} ((2 * n + 3) * a + 1) ∧
        ∀ x, grundyPass {a, (2 * n + 1) * a, (2 * n + 3) * a} x < 4 := by
  intro h
  have h6 := (((h 1 1 one_pos one_pos).1).2 6 (by norm_num)).1
  have : grundyPass {1, 3, 5} 6 = 1 ∧ grundyPassNoPass {1, 3, 5} 6 = 0 := by native_decide
  norm_num at h6
  omega

/-- **Conjecture (c).** For `a, n ≥ 1` and `S = {a, (2n + 1)a, (2n + 5)a}`, the conjectured
behaviour holds from `x = (2n + 5)a + 1` on, and `G(x, 1) < 4` for all `x`. False for `a = 1`,
`n = 2`. -/
@[category research solved, AMS 5 91]
theorem conjecture_c :
    ¬ ∀ a n : ℕ, 0 < a → 0 < n →
      Conjectured {a, (2 * n + 1) * a, (2 * n + 5) * a} ((2 * n + 5) * a + 1) ∧
        ∀ x, grundyPass {a, (2 * n + 1) * a, (2 * n + 5) * a} x < 4 := by
  intro h
  have h10 := (((h 1 2 one_pos two_pos).1).2 10 (by norm_num)).1
  have : grundyPass {1, 5, 9} 10 = 1 ∧ grundyPassNoPass {1, 5, 9} 10 = 0 := by native_decide
  norm_num at h10
  omega

/-- Conjecture (a) with the failing case removed: `n ≠ 2`. -/
@[category research open, AMS 5 91]
theorem conjecture_a.variants.n_ne_two :
    ∀ a n : ℕ, 0 < a → 0 < n → n ≠ 2 →
      Conjectured {a, 2 * a * n, 2 * a * n + a} (6 * a * n + 4 * a + 1) := by
  sorry

/-- Conjecture (b) with the failing case removed: `n ≥ 2`. -/
@[category research open, AMS 5 91]
theorem conjecture_b.variants.two_le :
    ∀ a n : ℕ, 0 < a → 2 ≤ n →
      Conjectured {a, (2 * n + 1) * a, (2 * n + 3) * a} ((2 * n + 3) * a + 1) ∧
        ∀ x, grundyPass {a, (2 * n + 1) * a, (2 * n + 3) * a} x < 4 := by
  sorry

/-- Conjecture (c) with the failing case removed: `n ≠ 2`. -/
@[category research open, AMS 5 91]
theorem conjecture_c.variants.n_ne_two :
    ∀ a n : ℕ, 0 < a → 0 < n → n ≠ 2 →
      Conjectured {a, (2 * n + 1) * a, (2 * n + 5) * a} ((2 * n + 5) * a + 1) ∧
        ∀ x, grundyPass {a, (2 * n + 1) * a, (2 * n + 5) * a} x < 4 := by
  sorry

end Arxiv.«2605.14321»
