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
# Erdős Problem 531

*References:*
- [erdosproblems.com/531](https://www.erdosproblems.com/531)
- [Er73] Erdős, P., _Problems and results on combinatorial number theory_. In: A Survey of
  Combinatorial Theory (1973), 117–138.
- [ErSp89] Erdős, P. and Spencer, J., _Monochromatic sumsets_. Journal of Combinatorial
  Theory, Series A **50** (1989), 162–163.
- [BENTW17] Balogh, J., Eberhard, S., Narayanan, B., Treglown, A. and Wagner, A. Z.,
_An improved lower bound for Folkman's theorem_. Bulletin of the London Mathematical
Society **49** (2017), 745–747.
-/

open Filter Finset

open scoped BigOperators

namespace Erdos531

/-- A 2-coloring $\chi : \mathbb{N} \to \mathrm{Bool}$ admits a **monochromatic subset-sum
$k$-set** within $\{1, \ldots, N\}$ if there is a $k$-element set
$A \subseteq \{1, \ldots, N\}$ whose non-empty subset sums all lie in
$\{1, \ldots, N\}$ and receive the same color. -/
def HasMonoSubsetSumSet (χ : ℕ → Bool) (k N : ℕ) : Prop :=
  ∃ A : Finset ℕ,
    A.card = k ∧
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
    (∀ S ∈ A.powerset, S.Nonempty → ∑ i ∈ S, i ≤ N) ∧
    ∃ c : Bool, ∀ S ∈ A.powerset, S.Nonempty → χ (∑ i ∈ S, i) = c

/-- The **Folkman number** $F(k)$: the minimum $N$ such that every 2-coloring
of $\{1, \ldots, N\}$ admits a $k$-element subset whose non-empty subset sums
are monochromatic. -/
noncomputable def folkmanNumber (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ χ : ℕ → Bool, HasMonoSubsetSumSet χ k N}

/-- Folkman's theorem: for every $k$, the Folkman number $F(k)$ is finite.
That is, there exists $N$ such that every 2-coloring of $\{1, \ldots, N\}$ has a
monochromatic subset-sum $k$-set. -/
@[category research solved, AMS 5]
theorem folkman_theorem (k : ℕ) :
    ∃ N : ℕ, ∀ χ : ℕ → Bool, HasMonoSubsetSumSet χ k N := by
  sorry

/--
**Erdős Problem 531** (lower bound, [BENTW17]):

$F(k) \geq 2^{2^{k-1}/k}$ for all sufficiently large $k$.

This is the best known lower bound on the Folkman number, due to
Balogh, Eberhard, Narayanan, Treglown, and Wagner.
-/
@[category research solved, AMS 5]
theorem erdos_531 :
    ∀ᶠ k : ℕ in atTop,
      (folkmanNumber k : ℝ) ≥ (2 : ℝ) ^ ((2 : ℝ) ^ ((k : ℝ) - 1) / (k : ℝ)) := by
  sorry

end Erdos531
