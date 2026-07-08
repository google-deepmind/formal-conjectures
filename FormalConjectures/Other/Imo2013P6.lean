/-
Copyright 2025 The Formal Conjectures Authors.

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
# IMO 2013 Problem 6 (beautiful labellings)

Consider `n + 1` points arranged on a circle, indexed by `0, 1, …, n` in cyclic
order.  A *beautiful labelling* is a bijection assigning the labels `0, 1, …, n`
to these points such that: for any four labels `a < b < c < d` with `a + d = b + c`,
the chord joining the points labelled `a` and `d` does not intersect the chord
joining the points labelled `b` and `c`.

Let `M n` be the number of beautiful labellings, counted up to rotation of the
circle (normalised so that the point in position `0` carries label `0`).  Let
`N n` be the number of ordered pairs `(x, y)` of positive integers with
`x + y ≤ n` and `gcd x y = 1`.

The problem asks to prove that for all `n ≥ 3`,
$$ M(n) = N(n) + 1. $$

This is a solved competition problem (IMO 2013, Problem 6) with a well-known
human solution, but to our knowledge it has no complete machine-checked proof in
any formal system; the statement is therefore recorded here with its proof left
open.

*Reference:* [IMO 2013 Problem 6](https://www.imo-official.org/problems.aspx);
discussion on [AoPS](https://artofproblemsolving.com/community/c6h550185).
-/

namespace Imo2013P6

open Finset

/-- Strict cyclic betweenness of `a, b, c` viewed as positions on the circle:
`b` lies strictly on the clockwise arc from `a` to `c`. -/
def sbtw (a b c : ℕ) : Prop :=
  (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b)

instance (a b c : ℕ) : Decidable (sbtw a b c) := by unfold sbtw; infer_instance

/-- The chord `p–q` and the chord `r–s` cross iff exactly one of `r`, `s` lies on
the clockwise arc strictly between `p` and `q`. -/
def Cross (p q r s : ℕ) : Prop := Xor' (sbtw p r q) (sbtw p s q)

instance (p q r s : ℕ) : Decidable (Cross p q r s) := by unfold Cross Xor'; infer_instance

/-- A permutation `f` of `Fin (n + 1)` is a *beautiful labelling* if no two chords
whose endpoint labels have equal sums cross.  We read the labels as natural
numbers via `Fin.val`. -/
def Beautiful (n : ℕ) (f : Equiv.Perm (Fin (n + 1))) : Prop :=
  ∀ a b c d : Fin (n + 1), a < b → b < c → c < d → a.val + d.val = b.val + c.val →
    ¬ Cross (f a).val (f d).val (f b).val (f c).val

instance (n : ℕ) : DecidablePred (Beautiful n) := fun _ => by
  unfold Beautiful; infer_instance

/-- `M n` : the number of beautiful labellings of the `n + 1` points, counted up
to rotation.  We normalise the rotation by requiring the label at position `0`
to be `0`, i.e. `f 0 = 0`. -/
def M (n : ℕ) : ℕ :=
  (univ.filter fun f : Equiv.Perm (Fin (n + 1)) =>
    Beautiful n f ∧ f 0 = 0).card

/-- `N n` : the number of ordered pairs `(x, y)` of positive integers with
`x + y ≤ n` and `gcd x y = 1`. -/
def N (n : ℕ) : ℕ :=
  ((Icc 1 n ×ˢ Icc 1 n).filter fun p => p.1 + p.2 ≤ n ∧ Nat.Coprime p.1 p.2).card

/-- **IMO 2013 Problem 6.** For every `n ≥ 3`, the number of beautiful labellings
of `n + 1` points on a circle (counted up to rotation) equals `N n + 1`, where
`N n` counts coprime ordered pairs of positive integers with sum at most `n`. -/
@[category research solved, AMS 5]
theorem imo2013_p6 (n : ℕ) (hn : 3 ≤ n) : M n = N n + 1 := by
  sorry

/- ### Basic API tests for the bespoke definitions.

`N` is a `Finset` count over `ℕ × ℕ` and reduces under `decide`, so we pin its
first values.  `M` counts over `Equiv.Perm (Fin (n + 1))`; its `Fintype`
enumeration does not kernel-reduce under `decide`, so we do not pin its values
here by computation.  For the record, the intended values are
`M 3 = 4`, `M 4 = 6`, `M 5 = 10` (matching `N 3 + 1 = 4`, `N 4 + 1 = 6`,
`N 5 + 1 = 10`), consistent with the identity below. -/

@[category test, AMS 5]
theorem N_three : N 3 = 3 := by decide

@[category test, AMS 5]
theorem N_four : N 4 = 5 := by decide

@[category test, AMS 5]
theorem N_five : N 5 = 9 := by decide

end Imo2013P6
