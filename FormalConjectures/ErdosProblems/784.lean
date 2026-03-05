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
# Erdős Problem 784

For every $C > 0$, does every subset $A \subseteq \{2, \ldots, x\}$ with
$\sum_{a \in A} 1/a \le C$ leave at least $K \cdot x / (\log x)^c$ integers in $[1, x]$
undivided by any element of $A$? Resolved negatively for $C > 1$.

*Reference:* [erdosproblems.com/784](https://www.erdosproblems.com/784)

[Ru82] Ruzsa, I., *On the small sieve. I. Sieving by primes*, J. Number Theory, 1982.

[Sa98] Saias, E., *Entiers sans grand ni petit facteur premier. III*, Acta Arith., 1998.

[We25] Weingartner, A., *Integers free of divisors from a given set*, 2025.
-/

open Finset BigOperators Real

namespace Erdos784

/--
Erdős Problem 784:

For every $C > 0$, does there exist $c > 0$ and a constant $K > 0$ such that for all
sufficiently large $x$, every $A \subseteq \{2, \ldots, x\}$ with
$\sum_{a \in A} 1/a \le C$ satisfies
$$\#\{m \le x : a \nmid m \text{ for all } a \in A\} \ge K \cdot x / (\log x)^c ?$$

Resolved: true for $0 < C \le 1$ [Ru82] [Sa98], false for $C > 1$ [Ru82] [We25].
-/
@[category research solved, AMS 11]
theorem erdos_784 :
    answer(False) ↔
    ∀ C : ℝ, C > 0 →
    ∃ c : ℝ, c > 0 ∧
    ∃ K : ℝ, K > 0 ∧
    ∃ x₀ : ℕ, ∀ x : ℕ, x ≥ x₀ →
      ∀ A : Finset ℕ,
        (∀ a ∈ A, 2 ≤ a ∧ a ≤ x) →
        (∑ a ∈ A, (1 : ℝ) / (a : ℝ)) ≤ C →
        (((Finset.Icc 1 x).filter (fun m => ∀ a ∈ A, ¬(a ∣ m))).card : ℝ) ≥
          K * (x : ℝ) / (Real.log (x : ℝ)) ^ c := by
  sorry

end Erdos784
