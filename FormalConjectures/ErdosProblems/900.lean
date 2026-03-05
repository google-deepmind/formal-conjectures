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
# Erdős Problem 900

*Reference:* [erdosproblems.com/900](https://www.erdosproblems.com/900)

There exists a function $f$ with $f(c) \to 0$ as $c \to (1/2)^+$ and $f(c) \to 1$ as
$c \to \infty$, such that for every $c > 1/2$, a random graph $G(n, \lfloor cn \rfloor)$
with high probability contains a path of length at least $f(c) \cdot n$.

[AKS81] Ajtai, M., Komlós, J. and Szemerédi, E., _The longest path in a random graph_,
Combinatorica 1 (1981), 1-12.
-/

namespace Erdos900

/-- A simple graph $G$ contains a path with at least $k$ edges, i.e., a sequence
of $k+1$ distinct vertices where consecutive vertices are adjacent. -/
def GraphHasLongPath {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ m : ℕ, m ≥ k ∧
    ∃ (path : Fin (m + 1) → V),
      Function.Injective path ∧
      ∀ i : ℕ, ∀ h : i < m,
        G.Adj (path ⟨i, by omega⟩) (path ⟨i + 1, by omega⟩)

open Classical in
/-- The probability that a uniformly random simple graph on $\operatorname{Fin}(n)$ with exactly
$m$ edges satisfies a given property, in the Erdős–Rényi $G(n,m)$ model.
This is the fraction $|\{G \in G(n,m) \mid P(G)\}| / |G(n,m)|$. -/
noncomputable def erdosRenyiProbability (n m : ℕ)
    (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  let total := Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.edgeFinset.card = m)
  ((total.filter (fun G => P G)).card : ℝ) / (total.card : ℝ)

/--
Erdős Problem 900 (proved by Ajtai, Komlós, and Szemerédi [AKS81]):

There exists $f : \mathbb{R} \to \mathbb{R}$ with $f(c) \to 0$ as $c \to (1/2)^+$ and
$f(c) \to 1$ as $c \to \infty$, such that for every $c > 1/2$, a random graph
$G(n, \lfloor cn \rfloor)$ with high probability contains a path of length at least
$f(c) \cdot n$.
-/
@[category research solved, AMS 5 60]
theorem erdos_900 :
    ∃ f : ℝ → ℝ,
    (Filter.Tendsto (fun h => f (1/2 + h))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
    (Filter.Tendsto f Filter.atTop (nhds 1)) ∧
    (∀ c : ℝ, c > 1/2 → ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        erdosRenyiProbability n (⌊c * (n : ℝ)⌋₊)
          (fun G => GraphHasLongPath G (⌊f c * (n : ℝ)⌋₊)) ≥ 1 - ε) := by
  sorry

end Erdos900
