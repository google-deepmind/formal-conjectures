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
# Erdős Problem 379

*Reference:* [erdosproblems.com/379](https://www.erdosproblems.com/379)
-/

namespace Erdos379

open Filter

private noncomputable def S (n : ℕ) : ℕ :=
  sSup {s | ∀ k ∈ Finset.Ico 1 n, ∃ p, p.Prime ∧ p^s ∣n.choose k}

/--
Let $S(n)$ denote the largest integer such that, for all $1 ≤ k < n$, the binomial coefficient
$\binom{n}{k}$ is divisible by $p^S(n)$ for some prime $p$ (depending on $k$).Then
$\limsup S(n) = \infty$.
See solution in the comments on erdosproblems.com, and
https://github.com/teorth/analysis/blob/3522239c96742eaa0b3e8db9e7d41fe4c4907b37/analysis/Analysis/Misc/erdos_379.lean#L111
-/
@[category research solved, AMS 11]
theorem erdos_379 : atTop.limsup (fun n => (S n : ℕ∞)) = ⊤ := by
  sorry

end Erdos379
