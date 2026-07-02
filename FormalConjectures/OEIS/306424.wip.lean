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
# Conjectures associated with A306424

A306424: Numbers $k$ such that the base $b$ expansion of $k$ for each
$b = 3..k-1$ never contains more than two distinct digits.

The sequence A306424: Numbers $k$ such that the base $b$ expansion of $k$ for each
$b = 3..k-1$ never contains more than two distinct digits.

*References:*
- [A306424](https://oeis.org/A306424)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA306424


open List Finset Nat

/--
A306424: Numbers $k$ such that the base $b$ expansion of $k$ for each
$b = 3..k-1$ never contains more than two distinct digits.
-/
def A306424_condition (k : ℕ) : Prop :=
  -- The bases $b$ range over $3 \le b \le k-1$, expressed as $3 \le b$ and $b < k$.
  ∀ b : ℕ, 3 ≤ b ∧ b < k → ((Nat.digits b k).toFinset.card) ≤ 2

/--
The sequence A306424: Numbers $k$ such that the base $b$ expansion of $k$ for each
$b = 3..k-1$ never contains more than two distinct digits.
-/
noncomputable def a (n : ℕ) : ℕ := n.nth A306424_condition


@[category test, AMS 11]
lemma a_one : a 1 = 1 := by sorry

@[category test, AMS 11]
lemma a_two : a 2 = 2 := by sorry

@[category test, AMS 11]
lemma a_three : a 3 = 3 := by sorry

@[category test, AMS 11]
lemma a_four : a 4 = 4 := by sorry

@[category test, AMS 11]
lemma a_five : a 5 = 5 := by sorry


/--
A306424: Numbers $k$ such that the base $b$ expansion of $k$ for each
$b = 3..k-1$ never contains more than two distinct digits.

The sequence A306424: Numbers $k$ such that the base $b$ expansion of $k$ for each
$b = 3..k-1$ never contains more than two distinct digits.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/306424.wip.lean#L276"]
theorem target_theorem_0
  : A306424_condition 43 ∧ ∀ k : ℕ, 43 < k → ¬A306424_condition k := by
    sorry

end OeisA306424
