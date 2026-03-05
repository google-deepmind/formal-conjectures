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
# Erdős Problem 663

*Reference:* [erdosproblems.com/663](https://www.erdosproblems.com/663)

Let $k \geq 2$ and $q(n, k)$ denote the least prime which does not divide
$\prod_{1 \leq i \leq k} (n + i)$. Is it true that, if $k$ is fixed and $n$ is
sufficiently large, we have $q(n, k) < (1 + o(1)) \log n$?

A problem of Erdős and Pomerance [BEGL96][Er97e].

The bound $q(n, k) < (1 + o(1)) k \log n$ is easy. It may be true that this
improved bound holds even up to $k = o(\log n)$.

See also problem 457.

[BEGL96] Balog, A., Erdős, P., Graham, R. L., and Leep, D.

[Er97e] Erdős, P.
-/

open scoped BigOperators

namespace Erdos663

/-- $q(n, k)$ is the least prime which does not divide $\prod_{i=1}^{k} (n + i)$.
Returns $0$ if no such prime exists (which cannot happen since a finite
product has only finitely many prime factors). -/
noncomputable def leastNondividingPrime (n k : ℕ) : ℕ :=
  sInf {p : ℕ | Nat.Prime p ∧ ¬(p ∣ ∏ i ∈ Finset.range k, (n + i + 1))}

/--
Erdős Problem 663 [BEGL96][Er97e]:

Is it true that for any fixed $k \geq 2$, $q(n, k) < (1 + o(1)) \log n$ as $n \to \infty$,
where $q(n, k)$ is the least prime not dividing $\prod_{i=1}^{k} (n + i)$?

Formulated as: for every $\varepsilon > 0$ and every $k \geq 2$, there exists $N_0$ such that
for all $n \geq N_0$, $q(n, k) < (1 + \varepsilon) \cdot \log n$.
-/
@[category research open, AMS 11]
theorem erdos_663 : answer(sorry) ↔
    ∀ (k : ℕ), k ≥ 2 →
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (leastNondividingPrime n k : ℝ) < (1 + ε) * Real.log (n : ℝ) := by
  sorry

end Erdos663
