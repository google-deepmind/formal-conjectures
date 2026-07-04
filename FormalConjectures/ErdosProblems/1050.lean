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
# Erdős Problem 1050

*Reference:* [erdosproblems.com/1050](https://www.erdosproblems.com/1050)

Is $\sum_{n} \frac{1}{2^n - 3}$ irrational?

The answer is **yes**, proved by P. B. Borwein, *On the irrationality of $\sum 1/(q^n + r)$*,
J. Number Theory **37** (1991) 253-259 (cleaner self-contained proof in *On the irrationality of
certain series*, Math. Proc. Camb. Phil. Soc. **112** (1992) 141-146), specialized to $q = 2$,
$r = -3$.

A formal Lean proof is given in an external repository,
[`gotrevor/lean-gallery`](https://github.com/gotrevor/lean-gallery), formalized by Trevor Morris with
Claude Code and Harmonic's Aristotle.
-/

namespace Erdos1050

/-- **Erdős Problem 1050.** The series `∑ 1/(2ⁿ − 3)` is irrational. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/gotrevor/lean-gallery/blob/main/LeanGallery/NumberTheory/Erdos1050/Statement.lean"]
theorem erdos_1050 : Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ n - 3)) := by
  sorry

end Erdos1050
