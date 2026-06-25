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
Let $f:\mathbb{R}\to \mathbb{R}$ be such that
\[2f(x) \leq f(x+h)+f(x+2h)\]
for every $x\in \mathbb{R}$ and $h>0$. Must $f$ be monotonic?
-/
@[category research solved, AMS 26, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1125.lean"]
theorem erdos_1125 : answer(True) ↔ ∀ (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)),
    Monotone f := by
  sorry

end Erdos1125
