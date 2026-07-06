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
# Erdős Problem 419

*References:*
- [erdosproblems.com/419](https://www.erdosproblems.com/419)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [EGIP96] Erdős, Paul and Graham, S. W. and Ivić, Aleksandar and Pomerance, Carl,
  *On the number of divisors of $n!$*. (1996), 337--355.
-/

open Filter
open scoped ArithmeticFunction.sigma

namespace Erdos419

/-- The ratio $\sigma_0((n+1)!)/\sigma_0(n!)$, where $\sigma_0$ is the divisor-counting function. -/
noncomputable def factorialDivisorRatio (n : ℕ) : ℝ :=
  (σ 0 (n + 1).factorial : ℝ) / (σ 0 n.factorial : ℝ)

/-- The set $\{1\} \cup \{1+1/k : k \geq 1\}$. -/
def limitPointSet : Set ℝ :=
  {1} ∪ {x | ∃ k : ℕ, 1 ≤ k ∧ x = 1 + 1 / (k : ℝ)}

/--
If $\tau(n)$ counts the number of divisors of $n$, then what is the set of limit points of
\[
\frac{\tau((n+1)!)}{\tau(n!)}?
\]

The limit points are exactly $\{1\} \cup \{1+1/k : k \geq 1\}$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos419.lean"]
theorem erdos_419 :
    {x : ℝ | MapClusterPt x atTop factorialDivisorRatio} = limitPointSet := by
  sorry

end Erdos419
