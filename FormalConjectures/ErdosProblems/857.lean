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
# Erdős Problem 857

*Reference:* [erdosproblems.com/857](https://www.erdosproblems.com/857)

This is sometimes known as the weak sunflower problem (see problem \#20
for the strong sunflower problem).

[NaSa17] Naslund, E. and Sawin, W., _Upper bounds for sunflower-free sets_, 2017.
-/

open Finset

namespace Erdos857

/-- A family of sets forms a sunflower if every pair of distinct members
has the same intersection (the "kernel"). -/
def IsSunflower {n : ℕ} (S : Finset (Finset (Fin n))) : Prop :=
  ∃ K : Finset (Fin n), ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = K

/--
**Erdős Problem 857** — Weak Sunflower Problem:

For every $k \geq 2$, there exists a constant $c$ depending only on $k$ (with $c < 2$)
such that any family of distinct subsets of $\{1, \ldots, n\}$ of size greater than
$c^n$ must contain a sunflower of size $k$.

The trivial upper bound on $m(n,k)$ is $2^n$ (the total number of subsets),
so the content of this conjecture is that the base of the exponential
is strictly less than $2$.
-/
@[category research open, AMS 5]
theorem erdos_857 (k : ℕ) (hk : k ≥ 2) :
    ∃ c : ℝ, 0 < c ∧ c < 2 ∧
    ∀ n : ℕ,
    ∀ F : Finset (Finset (Fin n)),
      (F.card : ℝ) > c ^ n →
      ∃ S ⊆ F, S.card = k ∧ IsSunflower S := by
  sorry

/--
**Erdős Problem 857** — Naslund–Sawin bound [NaSa17]:

$m(n, 3) \leq (3 / 2^{2/3})^{(1 + o(1)) n}$.

For every $\varepsilon > 0$, for all sufficiently large $n$, any family of more than
$((3 / 2^{2/3}) + \varepsilon)^n$ distinct subsets of $\{1, \ldots, n\}$ contains a
$3$-sunflower.
-/
@[category research solved, AMS 5]
theorem erdos_857.variants.naslund_sawin :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ F : Finset (Finset (Fin n)),
      (F.card : ℝ) > (3 / (2 : ℝ) ^ ((2 : ℝ) / 3) + ε) ^ n →
      ∃ S ⊆ F, S.card = 3 ∧ IsSunflower S := by
  sorry

end Erdos857
