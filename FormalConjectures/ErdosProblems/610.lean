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
# Erdős Problem 610

*Reference:* [erdosproblems.com/610](https://www.erdosproblems.com/610)

For a graph $G$, let $\tau(G)$ denote the minimal number of vertices that include at
least one from each maximal clique of $G$ (the clique transversal number).

Estimate $\tau(G)$. In particular, is it true that if $G$ has $n$ vertices then
$\tau(G) \leq n - \omega(n)\sqrt{n}$ for some $\omega(n) \to \infty$, or even
$\tau(G) \leq n - c\sqrt{n \log n}$ for some absolute constant $c > 0$?

A problem of Erdős, Gallai, and Tuza [EGT92], who proved that
$\tau(G) \leq n - \sqrt{2n} + O(1)$.

[EGT92] Erdős, P., Gallai, T., and Tuza, Zs., *Covering the cliques of a graph with
vertices*, Discrete Mathematics, 1992.

[Er94] Erdős, P., *Some old and new problems in various branches of combinatorics*,
Discrete Mathematics, 1994.

[Er99] Erdős, P., *Some of my favourite problems in various branches of combinatorics*,
Le Matematiche, 1999.
-/

open SimpleGraph Filter

namespace Erdos610

/-- $S$ is a maximal clique of $G$ (as a `Finset`): it is a clique and no vertex
outside $S$ can be added while preserving the clique property. -/
def IsMaximalCliqueFS {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  G.IsClique (S : Set (Fin n)) ∧
  ∀ v : Fin n, v ∉ S → ¬G.IsClique (↑(insert v S) : Set (Fin n))

/-- $T$ is a clique transversal of $G$ if $T$ meets every maximal clique of $G$
that has at least $2$ vertices. -/
def IsCliqueTransversal {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), IsMaximalCliqueFS G S → 2 ≤ S.card → (T ∩ S).Nonempty

/-- The clique transversal number $\tau(G)$: the minimum cardinality of a clique
transversal of $G$. -/
noncomputable def cliqueTransversalNum {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf { k : ℕ | ∃ T : Finset (Fin n), IsCliqueTransversal G T ∧ T.card = k }

/--
**Erdős Problem 610** (Weak form) [EGT92]:

There exists a function $\omega : \mathbb{N} \to \mathbb{R}$ with $\omega(n) \to \infty$
such that for every graph $G$ on $n$ vertices,
$\tau(G) \leq n - \omega(n) \cdot \sqrt{n}$.
-/
@[category research open, AMS 5]
theorem erdos_610 : answer(sorry) ↔
    ∃ ω : ℕ → ℝ, Tendsto ω atTop atTop ∧
      ∀ n : ℕ, n ≥ 1 →
        ∀ G : SimpleGraph (Fin n),
          (cliqueTransversalNum G : ℝ) ≤ (n : ℝ) - ω n * Real.sqrt (n : ℝ) := by
  sorry

/--
**Erdős Problem 610** (Strong form) [EGT92] [Er94] [Er99]:

There exists $c > 0$ such that for every graph $G$ on $n$ vertices,
$\tau(G) \leq n - c \cdot \sqrt{n \cdot \log n}$.
-/
@[category research open, AMS 5]
theorem erdos_610.variants.strong : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        ∀ G : SimpleGraph (Fin n),
          (cliqueTransversalNum G : ℝ) ≤
            (n : ℝ) - c * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
  sorry

/--
**Erdős Problem 610** (Known bound, Erdős–Gallai–Tuza) [EGT92]:

There exists $C > 0$ such that for every graph $G$ on $n$ vertices,
$\tau(G) \leq n - \sqrt{2n} + C$.
-/
@[category research solved, AMS 5]
theorem erdos_610.variants.known_bound :
    ∃ C : ℝ, ∀ n : ℕ, n ≥ 1 →
      ∀ G : SimpleGraph (Fin n),
        (cliqueTransversalNum G : ℝ) ≤ (n : ℝ) - Real.sqrt (2 * (n : ℝ)) + C := by
  sorry

end Erdos610
