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
# Erdős Problem 787

*Reference:* [erdosproblems.com/787](https://www.erdosproblems.com/787)

Let $g(n)$ be maximal such that given any set $A \subset \mathbb{R}$ with $|A| = n$ there exists
some $B \subseteq A$ of size $|B| \geq g(n)$ such that $b_1 + b_2 \notin A$ for all
$b_1 \neq b_2 \in B$.

Estimate $g(n)$.

The current best bounds are
$$(\log n)^{1+c} \ll g(n) \ll \exp(\sqrt{\log n})$$
for some constant $c > 0$, the lower bound due to Sanders [Sa21] and the upper bound due to
Ruzsa [Ru05]. Beker [Be25] proved the lower bound with $c = 1/68$.

[Sa21] Sanders, T., _On the Erdős sum-avoiding set problem_ (2021).

[Be25] Beker, A., _Sum-avoiding sets in groups_ (2025).

[Ru05] Ruzsa, I. Z., _Sum-avoiding subsets_ (2005).
-/

open Finset Real

namespace Erdos787

/-- A subset $B$ of a finite set $A \subseteq \mathbb{R}$ is *sum-avoiding in $A$* if
$B \subseteq A$ and for all distinct $b_1, b_2 \in B$, their sum $b_1 + b_2 \notin A$. -/
def IsSumAvoidingIn (A B : Finset ℝ) : Prop :=
  B ⊆ A ∧ ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → b₁ + b₂ ∉ A

/-- $g(n)$: the largest $m$ such that every $n$-element subset of $\mathbb{R}$ contains a
sum-avoiding subset of size at least $m$. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ A : Finset ℝ, A.card = n →
    ∃ B : Finset ℝ, IsSumAvoidingIn A B ∧ B.card ≥ m}

/--
**Erdős Problem 787** — Lower bound (Sanders [Sa21], Beker [Be25]):

There exists a constant $c > 0$ such that $g(n) \gg (\log n)^{1+c}$ for all
sufficiently large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_787 :
    ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (g n : ℝ) ≥ C * (Real.log (n : ℝ)) ^ (1 + c) := by
  sorry

/--
**Erdős Problem 787** — Upper bound (Ruzsa [Ru05]):

$g(n) \ll \exp(\sqrt{\log n})$ for all sufficiently large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_787.variants.upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (g n : ℝ) ≤ C * Real.exp (Real.sqrt (Real.log (n : ℝ))) := by
  sorry

end Erdos787
