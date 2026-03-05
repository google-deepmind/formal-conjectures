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
# Erdős Problem 441

*Reference:* [erdosproblems.com/441](https://www.erdosproblems.com/441)

Let $N \geq 1$. What is the size of the largest $A \subseteq \{1, \ldots, N\}$
such that $\text{lcm}(a, b) \leq N$ for all $a, b \in A$?

Is it attained by choosing all integers in $[1, (N/2)^{1/2}]$ together with
all even integers in $[(N/2)^{1/2}, (2N)^{1/2}]$?

This construction gives $g(N) \geq (9N/8)^{1/2} + O(1)$. Erdős [Er51b] proved
$g(N) \leq (4N)^{1/2} + O(1)$. Chen [Ch98] established the asymptotic
$g(N) \sim (9N/8)^{1/2}$. Chen and Dai [ChDa07] proved that, infinitely often,
Erdős' construction is not optimal, disproving the conjecture.

[Er51b] Erdős, P., _On a problem in elementary number theory and a
combinatorial problem_. Proc. Amer. Math. Soc. (1951), 2, 308-311.

[Ch98] Chen, S., _On the size of sets whose elements have perfect power
pairwise l.c.m._. Acta Arith. (1998).

[ChDa07] Chen, S. and Dai, L.-X., _On the lcm-sum problem_. J. Number Theory
(2007).
-/

namespace Erdos441

/-- A finite set $A \subseteq \{1, \ldots, N\}$ has all pairwise lcm bounded by $N$. -/
def LcmBounded (A : Finset ℕ) (N : ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧ ∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N

/-- Erdős' construction: all integers in $[1, \sqrt{N/2}]$ together with all
even integers in $(\sqrt{N/2}, \sqrt{2N}]$. -/
noncomputable def erdosConstruction (N : ℕ) : Finset ℕ :=
  let lo := Nat.sqrt (N / 2)
  let hi := Nat.sqrt (2 * N)
  (Finset.Icc 1 lo) ∪ ((Finset.Ioc lo hi).filter (fun m => Even m))

/-- Erdős Problem 441, asymptotic upper bound (proved by Chen [Ch98]):
$g(N) \sim (9N/8)^{1/2}$. For any $\varepsilon > 0$ and sufficiently large $N$, any
$A \subseteq \{1, \ldots, N\}$ with all pairwise $\operatorname{lcm} \leq N$ satisfies
$|A| \leq (1+\varepsilon) \sqrt{9N/8}$. -/
@[category research solved, AMS 5 11]
theorem erdos_441 (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ, LcmBounded A N →
    (A.card : ℝ) ≤ (1 + ε) * Real.sqrt (9 * N / 8) := by
  sorry

/-- Erdős Problem 441, asymptotic lower bound (proved by construction):
For any $\varepsilon > 0$ and sufficiently large $N$, there exists
$A \subseteq \{1, \ldots, N\}$ with all pairwise $\operatorname{lcm} \leq N$ and
$|A| \geq (1-\varepsilon) \sqrt{9N/8}$. -/
@[category research solved, AMS 5 11]
theorem erdos_441.variants.lower (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∃ A : Finset ℕ, LcmBounded A N ∧
    (1 - ε) * Real.sqrt (9 * N / 8) ≤ (A.card : ℝ) := by
  sorry

/-- Erdős Problem 441, original conjecture (disproved by Chen–Dai [ChDa07]):
It is not true that Erdős' construction is optimal for all $N$. For infinitely
many $N$, there exists $A$ with $|A| > |\operatorname{erdosConstruction}(N)|$ and all
pairwise $\operatorname{lcm} \leq N$. -/
@[category research solved, AMS 5 11]
theorem erdos_441.variants.disproved :
    ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
    ∃ A : Finset ℕ, LcmBounded A N ∧
    (erdosConstruction N).card < A.card := by
  sorry

end Erdos441
