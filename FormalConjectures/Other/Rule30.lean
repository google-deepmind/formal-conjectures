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

import FormalConjectures.Util.ProblemImports

/-!
# The Rule 30 Prize Problems

**Rule 30** is the elementary cellular automaton with local update `c' = l ⊕ (c ∨ r)`, the
Boolean rule numbered `30` by Wolfram. Started from a single black cell on a bi-infinite row,
its **center column** `t ↦ (state t) 0` looks random — it was long *Mathematica*'s default
pseudorandom generator — yet nothing about that randomness is proven. In 2019 Wolfram offered
the **Rule 30 Prizes** for three questions about it; we formalize the first two.

* **Problem 1.** Is the center column non-periodic (never eventually periodic)?
* **Problem 2.** Does each color occur on average equally often, i.e. does the running average
  of the values converge to `1 / 2`?

Problem 3 — whether computing the `n`-th cell requires at least `~O(n)` work — is omitted. It is
model-relative and has no canonical model-independent phrasing. All three are open.

*References:*
- [Announcing the Rule 30 Prizes](https://writings.stephenwolfram.com/2019/10/announcing-the-rule-30-prizes/),
  Stephen Wolfram, 2019.
- [Rule 30 Prizes](https://rule30prize.org/).
- [Wikipedia: Rule 30](https://en.wikipedia.org/wiki/Rule_30).
-/

namespace Rule30

/-- The Rule 30 local update on a bi-infinite row `row : ℤ → Bool`.
The new value at `i` is `row (i-1) ⊕ (row i ∨ row (i+1))`, i.e. Wolfram's rule `30`. -/
def step (row : ℤ → Bool) : ℤ → Bool :=
  fun i => xor (row (i - 1)) (row i || row (i + 1))

/-- The Rule 30 evolution from the single-black-cell initial condition: `state 0` is black
exactly at position `0`, and each subsequent row is obtained by applying `step`. -/
def state : ℕ → ℤ → Bool
  | 0     => fun i => decide (i = 0)
  | t + 1 => step (state t)

@[simp, category API, AMS 37 68]
theorem state_zero (i : ℤ) : state 0 i = decide (i = 0) := rfl

@[simp, category API, AMS 37 68]
theorem state_succ (t : ℕ) : state (t + 1) = step (state t) := rfl

/-- The **center column** of Rule 30: the value of the single central cell (position `0`)
at time `t`. -/
def centerColumn (t : ℕ) : Bool := state t 0

/-- Sanity check: the first center-column values reproduce the known Rule 30 center column
([OEIS A051023](https://oeis.org/A051023)). Unlike `state_zero`/`state_succ`, this exercises the
composed evolution, guarding against a wrong seed, a swapped `xor`/`||`, or an off-by-one
neighbour index. -/
@[category test, AMS 37 68]
theorem centerColumn_prefix :
    (List.range 8).map centerColumn = [true, true, false, true, true, true, false, false] := by
  decide

/-- **Rule 30 Prize, Problem 1 (non-periodicity).** The center column of Rule 30 is not
eventually periodic: there is no positive period `p` and threshold `N` past which the column
repeats with period `p`. -/
@[category research open, AMS 37 68]
theorem centerColumn_not_eventually_periodic :
    answer(sorry) ↔
      ¬ ∃ p : ℕ, 0 < p ∧ ∃ N : ℕ, ∀ t : ℕ, N ≤ t → centerColumn (t + p) = centerColumn t := by
  sorry

/-- **Rule 30 Prize, Problem 2 (equal frequency).** Each color occurs on average equally often
in the center column: the set of times at which it is black has natural density `1 / 2`. This is
Wolfram's phrasing that the discrete limit of `Total[c[t]] / t` as `t → ∞` is `1 / 2`. -/
@[category research open, AMS 37 68]
theorem centerColumn_frequency_half :
    answer(sorry) ↔ {t : ℕ | centerColumn t}.HasDensity (1 / 2) := by
  sorry

end Rule30
