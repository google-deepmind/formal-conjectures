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

[Er78] Erdős, P., _Problems and results in combinatorial analysis and combinatorial
  number theory_, Proceedings of the Ninth Southeastern Conference on Combinatorics,
  Graph Theory, and Computing (1978), 29–40.

[AKS81] Ajtai, M., Komlós, J. and Szemerédi, E., _The longest path in a random graph_,
Combinatorica 1 (1981), 1–12.

[Er82e] Erdős, P., _Problems and results on finite and infinite combinatorial analysis II_,
  L'Enseignement Math. 27 (1982), 163–176.
-/

namespace Erdos900

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
    (Filter.Tendsto f (nhdsWithin (1/2) (Set.Ioi (1/2))) (nhds 0)) ∧
    (Filter.Tendsto f Filter.atTop (nhds 1)) ∧
    (∀ c : ℝ, c > 1/2 → ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        erdosRenyiProbability n (⌊c * (n : ℝ)⌋₊)
          (fun G => ∃ (v w : Fin n) (p : G.Walk v w), p.IsPath ∧
            ⌊f c * (n : ℝ)⌋₊ ≤ p.length) ≥ 1 - ε) := by
  sorry

end Erdos900
