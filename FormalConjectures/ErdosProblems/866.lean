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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 866

*References:*
- [erdosproblems.com/866](https://www.erdosproblems.com/866)
- [CES75] S. L. G. Choi, P. Erdős and E. Szemerédi, *Some additive and multiplicative problems
  in number theory*, Acta Arith. 27 (1975), 37–50.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos866

/--
`A` contains all sums $b_i + b_j$ ($1 \le i < j \le k$) for some distinct positive integers
$b_1, \ldots, b_k$.

[CES75] takes all summands to be distinct ("a sum ... will mean, unless otherwise indicated, one
formed with distinct integers"). Without distinctness a single even element $2b$ of `A` would
suffice. The $b_i$ are positive: the sharpness example for $k = 3$ in [CES75] is the set of odd
numbers together with $2$, which contains the sums of $0, 1, 2$.
-/
def HasPairwiseSums (k : ℕ) (A : Finset ℕ) : Prop :=
  ∃ b : Fin k → ℕ, Function.Injective b ∧ (∀ i, 0 < b i) ∧ ∀ i j, i < j → b i + b j ∈ A

/--
$g_k(N)$ is the least $g$ such that every $A \subseteq \{1, \ldots, 2N\}$ with
$\lvert A\rvert \ge N + g$ satisfies `HasPairwiseSums k A`.
-/
noncomputable def g (k N : ℕ) : ℕ :=
  sInf {g : ℕ | ∀ A ⊆ Finset.Icc 1 (2 * N), N + g ≤ A.card → HasPairwiseSums k A}

/-- The odd numbers in $\{1, \ldots, 2N\}$ contain no three pairwise sums of integers, since
$b_1 + b_2$, $b_1 + b_3$ and $b_2 + b_3$ cannot all be odd. -/
@[category test, AMS 11]
theorem not_hasPairwiseSums_odd (N : ℕ) :
    ¬ HasPairwiseSums 3 ((Finset.Icc 1 (2 * N)).filter Odd) := by
  rintro ⟨b, -, -, h⟩
  have h01 := (Finset.mem_filter.1 (h 0 1 (by decide))).2
  have h02 := (Finset.mem_filter.1 (h 0 2 (by decide))).2
  have h12 := (Finset.mem_filter.1 (h 1 2 (by decide))).2
  rw [Nat.odd_iff] at h01 h02 h12
  omega

def erdos_866.answer : ℕ → ℕ → ℝ := by sorry

/-- Fix $k \ge 3$. Let $g_k(N)$ be minimal such that if $A \subseteq \{1, \ldots, 2N\}$ has
$\lvert A\rvert \ge N + g_k(N)$ then there exist integers $b_1, \ldots, b_k$ such that all
$\binom{k}{2}$ pairwise sums $b_i + b_j$ ($i < j$) are in $A$. Estimate $g_k(N)$. -/
@[category research open, question value, AMS 11]
theorem erdos_866 (k : ℕ) (hk : 3 ≤ k) :
    (fun N : ℕ => (g k N : ℝ)) =Θ[atTop] erdos_866.answer k := by
  sorry

/-- [CES75, Theorem 1] and the example after it: $g_3(N) = 2$ for $N > 4$. -/
@[category research solved, AMS 11]
theorem erdos_866.variants.three (N : ℕ) (hN : 4 < N) : g 3 N = 2 := by
  sorry

/-- [CES75, Theorem 2]: $g_4(N) \ll 1$. -/
@[category research solved, AMS 11]
theorem erdos_866.variants.four : ∃ C : ℕ, ∀ᶠ N in atTop, g 4 N ≤ C := by
  sorry

/-- [CES75, Theorem 3]: $g_5(N) \asymp \log N$. The lower bound comes from the odd numbers
together with the powers of $2$. -/
@[category research solved, AMS 11]
theorem erdos_866.variants.five :
    (fun N : ℕ => (g 5 N : ℝ)) =Θ[atTop] fun N : ℕ => Real.log N := by
  sorry

/-- [CES75, Theorem 4]: $g_6(N) \asymp N^{1/2}$. -/
@[category research solved, AMS 11]
theorem erdos_866.variants.six :
    (fun N : ℕ => (g 6 N : ℝ)) =Θ[atTop] fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ) := by
  sorry

/-- [CES75, Theorem 5]: $g_k(N) \ll_k N^{1 - 2^{-k}}$. -/
@[category research solved, AMS 11]
theorem erdos_866.variants.upper (k : ℕ) (hk : 3 ≤ k) :
    (fun N : ℕ => (g k N : ℝ)) ≪ fun N : ℕ => (N : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ k) := by
  sorry

/-- [CES75, Theorem 6]: for every $\varepsilon > 0$, if $k$ is sufficiently large then
$g_k(N) > N^{1 - \varepsilon}$ for all large $N$. -/
@[category research solved, AMS 11]
theorem erdos_866.variants.lower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 - ε) < g k N := by
  sorry

end Erdos866
