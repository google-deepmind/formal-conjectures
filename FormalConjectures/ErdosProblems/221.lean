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
# Erdős Problem 221

Is there a set $A \subseteq \mathbb{N}$ with $|A \cap \{1, \ldots, N\}| \ll N / \log N$
such that every sufficiently large integer can be written as $2^k + a$ for some
$k \geq 0$ and $a \in A$?

The answer is yes. Lorentz [Lo54] first proved a weaker result with
$|A \cap \{1, \ldots, N\}| \ll N \cdot \log\log N / \log N$. Ruzsa [Ru72] proved the full
result with an elegant construction. Ruzsa [Ru01] later constructed an exact additive
complement achieving $|A \cap \{1, \ldots, N\}| \sim N / \log_2 N$, which is asymptotically
best possible.

## References

[Lo54] Lorentz, G. G., _On a problem of additive number theory_.
Proc. Amer. Math. Soc. **5** (1954), 838–841.

[Ru72] Ruzsa, I., _On a problem of P. Erdős_.
Canad. Math. Bull. **15** (1972), 309–310.

[Ru01] Ruzsa, I. Z., _Additive completion of lacunary sequences_.
Combinatorica **21** (2001), 279–291.

*Reference:* [erdosproblems.com/221](https://www.erdosproblems.com/221)
-/

open scoped Classical
open Finset Real

namespace Erdos221

/--
Is there a set $A \subseteq \mathbb{N}$ such that
$|A \cap \{1, \ldots, N\}| \ll N / \log N$ and every sufficiently large integer can be
written as $2^k + a$ for some $k \geq 0$ and $a \in A$?

The answer is yes, proved by Ruzsa [Ru72]. Lorentz [Lo54] had previously proved a weaker
result with $|A \cap \{1, \ldots, N\}| \ll N \cdot \log\log N / \log N$.
-/
@[category research solved, AMS 11]
theorem erdos_221 :
    answer(True) ↔
      ∃ (A : Set ℕ),
        (∃ (C : ℝ), C > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) ≤ C * ↑N / Real.log ↑N) ∧
        (∃ M : ℕ, ∀ n : ℕ, M ≤ n → ∃ k : ℕ, ∃ a ∈ A, n = 2 ^ k + a) := by
  sorry

/--
Ruzsa [Ru01] constructed an exact additive complement of the powers of 2 achieving
the asymptotically optimal counting bound: there exists a set $A \subseteq \mathbb{N}$ such that
$|A \cap \{1, \ldots, N\}| \sim N / \log_2 N$ as $N \to \infty$, and every sufficiently large
integer can be written as $2^k + a$ for some $k \geq 0$ and $a \in A$. This is best possible
since the number of powers of 2 up to $N$ is $\sim \log_2 N$.
-/
@[category research solved, AMS 11]
theorem erdos_221_optimal :
    ∃ (A : Set ℕ),
      (Filter.Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / (↑N / Real.logb 2 ↑N))
        Filter.atTop (nhds 1)) ∧
      (∃ M : ℕ, ∀ n : ℕ, M ≤ n → ∃ k : ℕ, ∃ a ∈ A, n = 2 ^ k + a) := by
  sorry

end Erdos221
