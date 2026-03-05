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
# Erdős Problem 182

*Reference:* [erdosproblems.com/182](https://www.erdosproblems.com/182)

Let $k \geq 3$. What is the maximum number of edges that a graph on $n$ vertices can
contain if it does not have a $k$-regular subgraph? Is it $\ll n^{1+o(1)}$?

Asked by Erdős and Sauer [Er75] [Er81]. Resolved by Janzer and Sudakov [JaSu23], who proved
that there exists some $C = C(k) > 0$ such that any graph on $n$ vertices with at
least $C \cdot n \cdot \log(\log(n))$ edges contains a $k$-regular subgraph.

A construction due to Pyber, Rödl, and Szemerédi [PRS95] shows that this
bound is best possible up to the value of the constant $C(k)$.

[Er75] Erdős, P., _Problems and results on combinatorial number theory III_,
  Number Theory Day (1975).

[Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_,
  Combinatorica 1 (1981), 25–42.

[JaSu23] Janzer, O. and Sudakov, B., _Resolution of the Erdős–Sauer conjecture on
  regular subgraphs_, 2023.

[PRS95] Pyber, L., Rödl, V., and Szemerédi, E., _Dense graphs without 3-regular
  subgraphs_, J. Combin. Theory Ser. B 63 (1995), 41–54.
-/

open SimpleGraph

namespace Erdos182

/-- $G$ contains a $k$-regular subgraph: there exists a nonempty finite graph $H$ that
is $k$-regular (every vertex has degree exactly $k$) and admits an injective
graph homomorphism into $G$. -/
def ContainsKRegularSubgraph {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (U : Type) (fU : Fintype U) (_ : Nonempty U) (H : SimpleGraph U) (dH : DecidableRel H.Adj),
    haveI := fU; haveI := dH;
    (∀ v : U, H.degree v = k) ∧
    ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/--
Erdős Problem 182 (Erdős–Sauer conjecture) [Er75] [Er81]:

For every $k \geq 3$, there exists a constant $C > 0$ such that for all sufficiently
large $n$, every simple graph on $n$ vertices with at least $C \cdot n \cdot \log(\log(n))$
edges contains a $k$-regular subgraph.

Proved by Janzer and Sudakov [JaSu23].
-/
@[category research solved, AMS 5]
theorem erdos_182 :
    ∀ k : ℕ, 3 ≤ k →
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
    ∀ (n : ℕ), n₀ ≤ n →
    ∀ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
      haveI := dG;
      (G.edgeFinset.card : ℝ) ≥ C * (n : ℝ) * Real.log (Real.log (n : ℝ)) →
      ContainsKRegularSubgraph G k := by
  sorry

end Erdos182
