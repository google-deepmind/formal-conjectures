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
# Erdős Problem 497

How many antichains are there in the power set of an n-element set?

*Reference:* [erdosproblems.com/497](https://www.erdosproblems.com/497)

[Kl69] Kleitman, D., *On Dedekind's Problem: The Number of Monotone Boolean Functions*.
Proc. Amer. Math. Soc. 21 (1969), 677-682.
-/

open Finset Filter

namespace Erdos497

open Classical in
/--
The number of antichains in the power set of $\operatorname{Fin} n$ (the Dedekind number $D(n)$).
An antichain is a family $F$ of subsets of $[n]$ such that for all $A, B \in F$,
$A \neq B$ implies $A \not\subset B$.
-/
noncomputable def dedekindNumber (n : ℕ) : ℕ :=
  Fintype.card {F : Finset (Finset (Fin n)) // IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n)))}

/--
Erdős Problem 497 (Dedekind's Problem, resolved by Kleitman [Kl69]):
How many antichains in $[n]$ are there? That is, how many families of subsets
of $[n]$ are there such that no member is a subset of another?

Sperner's theorem states that any single antichain has size at most
$\binom{n}{\lfloor n/2 \rfloor}$. Kleitman proved that the total number of antichains in the
power set of $[n]$ is $2^{(1+o(1)) \binom{n}{\lfloor n/2 \rfloor}}$.

Equivalently, $\log_2(D(n)) / \binom{n}{\lfloor n/2 \rfloor} \to 1$ as $n \to \infty$.
-/
@[category research solved, AMS 5 6]
theorem erdos_497 :
    Tendsto
      (fun n : ℕ => Real.log (dedekindNumber n : ℝ) / (Real.log 2 * (n.choose (n / 2) : ℝ)))
      atTop (nhds 1) := by
  sorry

end Erdos497
