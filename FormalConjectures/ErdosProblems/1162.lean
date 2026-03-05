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
# Erdős Problem 1162

*Reference:* [erdosproblems.com/1162](https://www.erdosproblems.com/1162)

Give an asymptotic formula for the number of subgroups of $S_n$.
Is there a statistical theorem on their order?

A problem of Erdős and Turán.

Let $f(n)$ count the number of subgroups of $S_n$.
Pyber [Py93] proved that $\log f(n) \asymp n^2$.
Roney-Dougal and Tracey [RoTr25] proved that $\log f(n) = (\tfrac{1}{16} + o(1))n^2$.
-/

open Filter Real

namespace Erdos1162

/-- The number of subgroups of the symmetric group $S_n$. -/
noncomputable def numSubgroups (n : ℕ) : ℕ :=
  Nat.card (Subgroup (Equiv.Perm (Fin n)))

/--
Erdős Problem 1162 (partially resolved by Roney-Dougal and Tracey [RoTr25]):

$\log f(n) / n^2 \to \tfrac{1}{16}$ as $n \to \infty$, where $f(n)$ is the number of
subgroups of $S_n$.

The full problem, asking for an asymptotic formula for $f(n)$ and a statistical
theorem on the orders of subgroups, remains open.
-/
@[category research solved, AMS 20]
theorem erdos_1162 :
    Tendsto (fun n : ℕ => Real.log (numSubgroups n : ℝ) / ((n : ℝ) ^ 2))
      atTop (nhds (1 / 16)) := by
  sorry

end Erdos1162
