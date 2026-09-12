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

import FormalConjecturesUtil

/-!
# Erdős Problem 866

*References:*
- [erdosproblems.com/866](https://www.erdosproblems.com/866)
-/

open Asymptotics Filter Finset

namespace Erdos866

/--
There exist `k` distinct integers whose $\binom{k}{2}$ pairwise sums all lie in `A`
(the integers themselves need not lie in `A`).
-/
def HasPairwiseSums (k : ℕ) (A : Finset ℕ) : Prop :=
  ∃ b : Fin k → ℕ, Function.Injective b ∧ ∀ i j : Fin k, i < j → b i + b j ∈ A

/--
`g_k(N)` is minimal such that every $A\subseteq\{1,\ldots,2N\}$ of size at least $N+g_k(N)$
has `k` integers with all pairwise sums in `A`.
-/
noncomputable def g (k N : ℕ) : ℕ :=
  sInf {m | ∀ A ⊆ Icc 1 (2 * N), N + m ≤ A.card → HasPairwiseSums k A}

/--
Let $k\geq 3$ and $g_k(N)$ be minimal such that if $A\subseteq \{1,\ldots,2N\}$ has
$\lvert A\rvert \geq N+g_k(N)$ then there exist integers $b_1,\ldots,b_k$ such that all
$\binom{k}{2}$ pairwise sums are in $A$ (but the $b_i$ themselves need not be in $A$).

Estimate $g_k(N)$.
-/
@[category research open, AMS 5 11]
theorem erdos_866 :
    let f : ℕ → ℕ → ℝ := answer(sorry)
    ∀ k : ℕ, 3 ≤ k → (fun N => (g k N : ℝ)) ~[atTop] (f k) := by
  sorry

/--
Choi, Erdős, and Szemerédi proved that $g_3(N)=2$.
-/
@[category research solved, AMS 5 11]
theorem erdos_866.variants.g3 : ∀ᶠ N : ℕ in atTop, g 3 N = 2 := by
  sorry

/--
Choi, Erdős, and Szemerédi proved that $g_4(N) \ll 1$.
-/
@[category research solved, AMS 5 11]
theorem erdos_866.variants.g4 : ∃ C, ∀ᶠ N : ℕ in atTop, g 4 N ≤ C := by
  sorry

/--
van Doorn has shown that $g_4(N)\leq 2032$.
-/
@[category research solved, AMS 5 11]
theorem erdos_866.variants.g4_explicit : ∀ᶠ N : ℕ in atTop, g 4 N ≤ 2032 := by
  sorry

/--
Choi, Erdős, and Szemerédi also proved that $g_5(N)\asymp \log N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_866.variants.g5 :
    (fun N => (g 5 N : ℝ)) =Θ[atTop] fun N => Real.log N := by
  sorry

/--
Choi, Erdős, and Szemerédi also proved that $g_6(N)\asymp N^{1/2}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_866.variants.g6 :
    (fun N => (g 6 N : ℝ)) =Θ[atTop] fun N => (N : ℝ) ^ (1 / 2 : ℝ) := by
  sorry

/--
In general they proved that $g_k(N) \ll_k N^{1-2^{-k}}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_866.variants.upper (k : ℕ) (_hk : 3 ≤ k) :
    (fun N => (g k N : ℝ)) ≪
      fun N => (N : ℝ) ^ (1 - (2 : ℝ) ^ (-(k : ℝ))) := by
  sorry

/--
For every $\epsilon>0$ if $k$ is sufficiently large then $g_k(N) > N^{1-\epsilon}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_866.variants.lower :
    ∀ ε > (0 : ℝ), ∃ k₀, ∀ k ≥ k₀, ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - ε) < (g k N : ℝ) := by
  sorry

end Erdos866
