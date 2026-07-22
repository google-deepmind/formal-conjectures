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
# Erdős Problem 226

*References:*
- [erdosproblems.com/226](https://www.erdosproblems.com/226)
- [BaSc70] Barth, K. F. and Schneider, W. J., *Entire functions mapping
  countable dense subsets of the reals onto each other monotonically*.
  J. London Math. Soc. (2) (1970), 620--626.
- [BaSc71] Barth, K. F. and Schneider, W. J., *Entire functions mapping
  arbitrary countable dense sets and their complements onto each other*.
  J. London Math. Soc. (2) (1971/72), 482--488.
- [Ha74] Hayman, W. K., *Research problems in function theory: new problems*.
  (1974), 155--180.
-/

namespace Erdos226

/-- A real function preserves rationality. -/
def PreservesRationality (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, x ∈ Set.range ((↑) : ℚ → ℝ) ↔ f x ∈ Set.range ((↑) : ℚ → ℝ)

/--
Is there an entire non-linear function $f$ such that, for all $x\in\mathbb{R}$, $x$ is rational if and only if $f(x)$ is?

Barth and Schneider [BaSc70] proved the stronger result for countable dense subsets of
$\mathbb{R}$.
-/
@[category research solved, AMS 30,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos226.lean"]
theorem erdos_226 : answer(True) ↔
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ x : ℝ, (F x).im = 0) ∧
      (∀ g : AffineMap ℝ ℝ ℝ, (fun x : ℝ => (F x).re) ≠ g) ∧
      PreservesRationality (fun x : ℝ => (F x).re) := by
  sorry

end Erdos226
