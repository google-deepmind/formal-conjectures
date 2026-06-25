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
# Erdős Problem 1126

*Reference:* [erdosproblems.com/1126](https://www.erdosproblems.com/1126)
-/

open MeasureTheory

namespace Erdos1126

/--
If
\[f(x+y)=f(x)+f(y)\]
for almost all $x,y\in \mathbb{R}$ then there exists a function $g$ such that
\[g(x+y)=g(x)+g(y)\]
for all $x,y\in\mathbb{R}$ such that $f(x)=g(x)$ for almost all $x$.
-/
@[category research solved, AMS 26 28, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1126.lean"]
theorem erdos_1126 : answer(True) ↔ ∀
    (f : ℝ → ℝ)
    (h :
      ∀ᵐ (p : ℝ × ℝ) ∂(volume.prod volume),
        f (p.1 + p.2) = f p.1 + f p.2),
    ∃ h : ℝ → ℝ,
      (∀ x y, h (x + y) = h x + h y) ∧ (∀ᵐ x ∂volume, f x = h x) := by
  sorry

end Erdos1126
