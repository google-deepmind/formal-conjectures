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
# Erdős Problem 1131

*Reference:* [erdosproblems.com/1131](https://www.erdosproblems.com/1131)
-/

open scoped BigOperators Interval
open Filter Set

namespace Erdos1131

def Admissible {n : ℕ} (x : Fin n ↪ ℝ) : Prop :=
  ∀ k, x k ∈ Set.Icc (-1 : ℝ) 1

noncomputable def functional {n : ℕ} (x : Fin n ↪ ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1,
    ∑ k : Fin n,
      ((Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval t) ^ 2

def values (n : ℕ) : Set ℝ :=
  {y | ∃ x : Fin n ↪ ℝ, Admissible x ∧ functional x = y}

noncomputable def M (n : ℕ) : ℝ :=
  sInf (values n)

noncomputable def scaledDefect (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * (2 - M (n + 1))

/--
Let `M n` be the infimum, over all pairwise-distinct `n`-tuples in
`[-1, 1]`, of the integral of the sum of the squared Lagrange basis
polynomials. Is

`M n = 2 - (1 + o(1)) / n`?

The answer is **no**. The roots of
`T n - (1 / 6) * T (n - 2)` give an explicit admissible comparison family.
The linked proof establishes that, for every `N ≥ 24780`,

`106 / 105 ≤ (N + 1) * (2 - M (N + 1))`,

so the scaled defect cannot tend to `1`.
-/
@[category research solved, AMS 28 41 65,
  formal_proof using lean4 at "https://github.com/seanm27lol/erdos-1131-lean/blob/31574acf09ae50430c08da92288800fe7d26c7fd/Erdos1131/Main.lean"]
theorem erdos_1131 :
    answer(False) ↔ Tendsto scaledDefect atTop (nhds 1) := by
  sorry

end Erdos1131
