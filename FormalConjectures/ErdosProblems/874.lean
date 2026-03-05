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
# Erdős Problem 874

*Reference:* [erdosproblems.com/874](https://www.erdosproblems.com/874)

Let $k(N)$ denote the size of the largest set $A \subseteq \{1,\ldots,N\}$ such that the sets
$$S_r = \{ a_1 + \cdots + a_r : a_1 < \cdots < a_r \in A \}$$
are disjoint for distinct $r \geq 1$. Estimate $k(N)$ — in particular, is it true
that $k(N) \sim 2N^{1/2}$?

Straus [St66] calls such sets admissible and showed
$\liminf k(N)/N^{1/2} \geq 2$ and $\limsup k(N)/N^{1/2} \leq 4/\sqrt{3}$.
Erdős–Nicolas–Sárközy [ENS91] improved the upper bound to $(143/27)^{1/2}$.
The conjecture was proved for all large $N$ by Deshouillers and Freiman [DeFr99].
-/

open Filter

namespace Erdos874

/-- The set of $r$-fold subset sums of $A$: all possible values of $a_1 + \cdots + a_r$
where $a_1, \ldots, a_r$ are $r$ distinct elements of $A$. -/
def rSubsetSums (A : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (A.powersetCard r).image (fun S => S.sum id)

/-- A set $A \subseteq \mathbb{N}$ is *admissible* (in the sense of Straus) if the $r$-fold subset
sums $S_r$ are pairwise disjoint for all distinct $r_1 \neq r_2$ with $r_1, r_2 \geq 1$. -/
def IsAdmissible874 (A : Finset ℕ) : Prop :=
  ∀ r₁ r₂ : ℕ, 1 ≤ r₁ → 1 ≤ r₂ → r₁ ≠ r₂ →
    Disjoint (rSubsetSums A r₁) (rSubsetSums A r₂)

/-- $k(N)$ is the maximum size of an admissible subset of $\{1,\ldots,N\}$. -/
noncomputable def kAdmissible (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsAdmissible874 A ∧ A.card = k}

/--
Erdős Problem 874 (proved by Deshouillers–Freiman [DeFr99]):
$k(N) \sim 2N^{1/2}$, i.e., for every $\varepsilon > 0$ and all sufficiently large $N$,
$(2 - \varepsilon) \cdot N^{1/2} \leq k(N) \leq (2 + \varepsilon) \cdot N^{1/2}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_874 :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        (2 - ε) * (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (kAdmissible N : ℝ) ∧
        (kAdmissible N : ℝ) ≤ (2 + ε) * (N : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

end Erdos874
