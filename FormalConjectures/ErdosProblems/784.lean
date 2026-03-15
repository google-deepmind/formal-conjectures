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
undivided by any element of $A$? Resolved: true for $0 < C \le 1$ [Ru82] [Sa98],
false for $C > 1$ [Ru82] [We25].

*Reference:* [erdosproblems.com/784](https://www.erdosproblems.com/784)

See also Problem 542.

[Er72] Erdős, P., _Quelques problèmes de théorie des nombres_, p. 81, 1972.

[Er73] Erdős, P., _Problems and results on combinatorial number theory_. In: A Survey of
Combinatorial Theory (1973), 117–138.

[ScSz59] Schinzel, A., Szekeres, G., _Sur un problème de M. Paul Erdős_.
Acta Sci. Math. (Szeged) (1959), 221–229.

[Ru82] Ruzsa, I., _On the small sieve. II. Sifting by composite numbers_,
J. Number Theory (1982), 260–268.

[Sa98] Saias, E., _Applications des entiers à diviseurs denses_, Acta Arith. (1998), 225–240.

[We25] Weingartner, A., _The Schinzel–Szekeres function_, Res. Number Theory (2025),
Paper No. 63, 32 pp.
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

/--
Erdős Problem 784 (positive case):

For $0 < C \le 1$, there exist $c > 0$ and $K > 0$ such that for all sufficiently large $x$,
every $A \subseteq \{2, \ldots, x\}$ with $\sum_{a \in A} 1/a \le C$ satisfies
$$\#\{m \le x : a \nmid m \text{ for all } a \in A\} \ge K \cdot x / (\log x)^c.$$

Proved by Ruzsa [Ru82] (lower bound) and Saias [Sa98] (upper bound), giving
$H_1(x) \asymp x / \log x$.
-/
@[category research solved, AMS 11]
theorem erdos_784_small_C :
    ∀ C : ℝ, 0 < C → C ≤ 1 →
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
