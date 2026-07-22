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
# Conjectures associated with A108

A000108 Catalan numbers: C(n) = binomial(2n,n)/(n+1).

The sum $\sum_{i=j}^k \frac{1}{a(i)}$ of reciprocals of Catalan numbers.

*References:*
- [A108](https://oeis.org/A108)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA108


open Nat Real Finset

/--
A000108 Catalan numbers: C(n) = binomial(2n,n)/(n+1).
-/
def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) / (n + 1)

def a_rat (n : ℕ) : ℚ := (a n : ℚ)⁻¹

/-- The sum $\sum_{i=j}^k \frac{1}{a(i)}$ of reciprocals of Catalan numbers. -/
def catalan_reciprocal_sum (j k : ℕ) : ℚ :=
  (Finset.Icc j k).sum a_rat

/-- The index condition on $(j, k)$ from the conjecture: $0 < \min\{2,k\} \le j \le k$.
Since j and k are natural numbers, $0 < \min\{2,k\}$ is equivalent to $1 \le k$. -/
def oeis_108_index_cond (j k : ℕ) : Prop :=
  1 ≤ k ∧ min 2 k ≤ j ∧ j ≤ k

open Int (fract)

/-- The fractional part of a rational number, viewed as a real number. Must be noncomputable
due to dependence on the real floor function. -/
noncomputable def frac_part (q : ℚ) : ℝ := fract (q : ℝ)


@[category test, AMS 11]
lemma a_zero : a 0 = 1 := by rfl

@[category test, AMS 11]
lemma a_one : a 1 = 1 := by rfl

@[category test, AMS 11]
lemma a_three : a 3 = 5 := by rfl

@[category test, AMS 11]
lemma a_four : a 4 = 14 := by rfl


/--
A000108 Catalan numbers: C(n) = binomial(2n,n)/(n+1).

The sum $\sum_{i=j}^k \frac{1}{a(i)}$ of reciprocals of Catalan numbers.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/108.wip.lean#L255"]
theorem catalan_reciprocal_sum_frac_part_inj : ∀ ⦃j₁ k₁ j₂ k₂ : ℕ⦄,
    oeis_108_index_cond j₁ k₁ → oeis_108_index_cond j₂ k₂ →
    (j₁, k₁) ≠ (j₂, k₂) →
    frac_part (catalan_reciprocal_sum j₁ k₁) ≠ frac_part (catalan_reciprocal_sum j₂ k₂) := by
    sorry

end OeisA108
