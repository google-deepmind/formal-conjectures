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
# Erdős Problem 1161

*Reference:* [Va99, 5.72], [erdosproblems.com/1161](https://www.erdosproblems.com/1161)

Let $f_k(n)$ count the number of elements of $S_n$ (the symmetric group) of
order $k$. For which values of $k$ will $f_k(n)$ be maximal?

Beker [Be25d] proved that
$$\max_{k \geq 1} f_k(n) \sim (n-1)!,$$
and characterized the maximizing values of $k$: for all large $n$,
$f_k(n) = (n-1)!$ if and only if $k \geq 1$ is minimal such that
$\operatorname{lcm}(1,\ldots,n-k) \mid k$.

[Va99] Vardi, I., *Computational Recreations in Mathematica* (1999).
[Be25d] Beker, A., _The most probable order of a random permutation_. arXiv:2510.11698 (2025).
-/

open Finset Equiv

namespace Erdos1161

/-- $f_k(n)$: the number of permutations in $S_n$ whose order equals $k$. -/
noncomputable def countPermsOfOrder (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => orderOf σ = k)).card

/--
Erdős Problem 1161 — asymptotic magnitude (Solved by Beker [Be25d]):

Let $f_k(n)$ count the number of elements of $S_n$ of order $k$. Beker proved that
$\max_{k \geq 1} f_k(n) \sim (n-1)!$, i.e., the maximum over $k$ of the number of
permutations of order $k$ is asymptotic to $(n-1)!$.

This formalizes only the asymptotic magnitude result. The characterization of which
values of $k$ achieve the maximum is formalized separately in `erdos_1161_characterization`.

Formalized as: for every $\varepsilon > 0$, for all sufficiently large $n$,
(1) there exists $k \geq 1$ with $f_k(n) \geq (1 - \varepsilon) \cdot (n-1)!$, and
(2) for all $k$, $f_k(n) \leq (1 + \varepsilon) \cdot (n-1)!$.
-/
@[category research solved, AMS 5 20]
theorem erdos_1161 :
    ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        (∃ k : ℕ, k ≥ 1 ∧
          (countPermsOfOrder n k : ℝ) ≥ (1 - ε) * ((n - 1).factorial : ℝ)) ∧
        (∀ k : ℕ,
          (countPermsOfOrder n k : ℝ) ≤ (1 + ε) * ((n - 1).factorial : ℝ)) := by
  sorry

/--
Erdős Problem 1161 — characterization of maximizing $k$ (Solved by Beker [Be25d]):

Beker proved that for all sufficiently large $n$, $f_k(n) = (n-1)!$ if and only if
$k \geq 1$ is the minimal value such that $\operatorname{lcm}(1, \ldots, n-k) \mid k$.

This complements `erdos_1161` which establishes the asymptotic magnitude
$\max_{k \geq 1} f_k(n) \sim (n-1)!$.
-/
@[category research solved, AMS 5 20]
theorem erdos_1161_characterization :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → ∀ k : ℕ,
      (countPermsOfOrder n k = (n - 1).factorial) ↔
        (k ≥ 1 ∧
         (Finset.lcm (Finset.range (n - k)) (· + 1)) ∣ k ∧
         ∀ j : ℕ, j ≥ 1 → j < k →
           ¬((Finset.lcm (Finset.range (n - j)) (· + 1)) ∣ j)) := by
  sorry

end Erdos1161
