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
# Erdős Problem 1125

*Reference:* [erdosproblems.com/1125](https://www.erdosproblems.com/1125)
-/

namespace Erdos1125

/--
If $f : \mathbb{R} \to \mathbb{R}$ satisfies $2f(x) \le f(x+h) + f(x+2h)$ for all $x$ and all
$h > 0$, then $f$ is monotone. The answer is yes (Laczkovich).
-/
@[category research solved, AMS 26, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1125.lean"]
theorem erdos_1125 {f : ℝ → ℝ}
    (hf : ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) :
    Monotone f := by
  sorry

end Erdos1125
