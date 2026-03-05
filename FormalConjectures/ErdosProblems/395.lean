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
# Erdős Problem 395

For unit complex vectors, the probability that a random signed sum has norm
at most √2 is at least proportional to 1/n.

*Reference:* [erdosproblems.com/395](https://www.erdosproblems.com/395)

[HJNS24] He, X., Juškevičius, T., Narayanan, B., and Spiro, S.,
_A reverse Littlewood-Offord problem_.
-/

open Finset

open scoped BigOperators

namespace Erdos395

/-- The signed sum of complex numbers $z$ with signs $\varepsilon \in \{-1, 1\}^n$
(encoded as `Bool`). -/
noncomputable def signedSum {n : ℕ} (z : Fin n → ℂ) (ε : Fin n → Bool) : ℂ :=
  ∑ i : Fin n, (if ε i then (1 : ℂ) else (-1 : ℂ)) * z i

/--
Erdős Problem 395 (Proved by He, Juškevičius, Narayanan, and Spiro [HJNS24]):

If $z_1, \ldots, z_n \in \mathbb{C}$ with $|z_i| = 1$, then the probability that
$|\varepsilon_1 z_1 + \cdots + \varepsilon_n z_n| \leq \sqrt{2}$, where
$\varepsilon_i \in \{-1, 1\}$ uniformly at random, is $\gg 1/n$.

Formally: there exists $c > 0$ such that for all $n \geq 1$ and all unit complex vectors
$z$, the number of sign patterns $\varepsilon$ for which
$\|\sum \varepsilon_i z_i\| \leq \sqrt{2}$ is at least $c \cdot 2^n / n$.

This is a reverse Littlewood-Offord problem. The bound $1/n$ is best possible,
as shown by taking $z_k = 1$ for $1 \leq k \leq n/2$ and $z_k = i$ otherwise.
-/
@[category research solved, AMS 5 60]
theorem erdos_395 :
    ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ), 0 < n →
    ∀ (z : Fin n → ℂ),
    (∀ i, ‖z i‖ = 1) →
    c * (2 : ℝ) ^ n / (n : ℝ) ≤
      ((Finset.univ.filter (fun ε : Fin n → Bool =>
        ‖signedSum z ε‖ ≤ Real.sqrt 2)).card : ℝ) := by
  sorry

end Erdos395
