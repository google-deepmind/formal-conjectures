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
# Half-Fibonacci sequence

$a(0) = 1, a(1) = 3$; for $n \ge 2$, $a(n) = f(a(n-1)) + f(a(n-2))$ where $f(x) = x/2$ if $x$
is even
and $f(x) = x$ if $x$ is odd.

*References:*
- [A120424](https://oeis.org/A120424)
- T. Adamczewski, "OEIS Open: How many conjectures can language models turn into theorems?",
  [arXiv:2608.11941](https://arxiv.org/abs/2608.11941) [cs.AI], 2026, Appendix A.-/

@[expose] public section

namespace OeisA120424

/-- Halve even numbers, leave odd numbers unchanged. -/
def f (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else x

/-- Half-Fibonacci sequence starting with $1, 3$. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | n + 2 => f (a (n + 1)) + f (a n)

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 4 := by rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 7 := by rfl

/--
Conjecture (1): The natural density of even terms in the sequence is $1/2$.-/
@[category research open, AMS 11]
theorem conjecture1 :
    Filter.Tendsto (fun n : ℕ => ((Finset.filter (fun k => a k % 2 = 0) (Finset.range n)).card
        : ℝ) / (n : ℝ))
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  sorry

/--
Conjecture (2): There are infinitely many consecutive pairs that differ by 1.-/
@[category research open, AMS 11]
theorem conjecture2 :
    Set.Infinite {n : ℕ | a (n + 1) = a n + 1 ∨ a n = a (n + 1) + 1} := by
  sorry

/-- The statement of `conjecture1` says that the set of indices of even terms has natural
density $1/2$. -/
@[category API, AMS 11]
theorem conjecture1_iff_hasDensity :
    Filter.Tendsto (fun n : ℕ => ((Finset.filter (fun k => a k % 2 = 0) (Finset.range n)).card
        : ℝ) / (n : ℝ)) Filter.atTop (nhds (1 / 2 : ℝ)) ↔
      {n : ℕ | a n % 2 = 0}.HasDensity (1 / 2) := by
  unfold Set.HasDensity Set.partialDensity
  refine Iff.of_eq (congrArg (fun g => Filter.Tendsto g _ _) (funext fun n => ?_))
  rw [Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat, ← Set.ncard_coe_finset]
  congr 3
  ext k
  simp [and_comm]

set_option linter.style.formal_proof_palomar false in
/--
Conjectures (1) and (2) are incompatible: if the even terms have natural density $1/2$, then only
finitely many consecutive terms differ by $1$.

Proved in the OEIS Open project, see T. Adamczewski, OEIS Open: How many conjectures can
language models turn into theorems?, [arXiv:2608.11941](https://arxiv.org/abs/2608.11941),
Appendix A.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/epoch-research/LeanOpenProblems-results/blob/cbb7cb657f24157d9ebb7640ec50bd35bad78ad8/runs/oeis-full-50usd-ant-j0j0g4uzligm1k41/oeis_a120424_conjecture_0/Submission/Spec.lean#L489"]
theorem not_conjecture1_and_conjecture2 :
    ¬ (Filter.Tendsto (fun n : ℕ => ((Finset.filter (fun k => a k % 2 = 0) (Finset.range n)).card
        : ℝ) / (n : ℝ)) Filter.atTop (nhds (1 / 2 : ℝ)) ∧
      Set.Infinite {n : ℕ | a (n + 1) = a n + 1 ∨ a n = a (n + 1) + 1}) := by
  sorry

end OeisA120424
