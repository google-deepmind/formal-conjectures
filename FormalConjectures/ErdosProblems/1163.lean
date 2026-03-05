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
# Erdős Problem 1163

*Reference:* [erdosproblems.com/1163](https://www.erdosproblems.com/1163)

Describe (by statistical means) the arithmetic structure of the orders of
subgroups of $S_n$. A concrete interpretation: the proportion of divisors of
$n!$ that are orders of subgroups of $S_n$ tends to $0$ as $n \to \infty$.

[Va99] Vardi, I., *Computational Recreations in Mathematica* (1999).
-/

open Equiv Classical

namespace Erdos1163

/-- A natural number $m$ is a subgroup order of $S_n$ if there exists a subgroup
of the symmetric group `Perm (Fin n)` with exactly $m$ elements. -/
def IsSubgroupOrderOfSn (n m : ℕ) : Prop :=
  ∃ H : Subgroup (Perm (Fin n)), Nat.card H = m

/--
Erdős Problem 1163 (Erdős and Turán) [Va99, 5.74]:
Describe (by statistical means) the arithmetic structure of the orders of
subgroups of $S_n$.

The original problem is acknowledged as ambiguous. A concrete
interpretation: as $n \to \infty$, the proportion of divisors of $n!$ that are orders
of subgroups of $S_n$ tends to $0$. By Lagrange's theorem, every subgroup order
divides $n!$, but the set of subgroup orders becomes a vanishingly small
fraction of all divisors.
-/
@[category research open, AMS 5 20]
theorem erdos_1163 :
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n ≥ N,
        ((n.factorial.divisors.filter (fun m => IsSubgroupOrderOfSn n m)).card : ℝ) <
        ε * (n.factorial.divisors.card : ℝ) := by
  sorry

end Erdos1163
