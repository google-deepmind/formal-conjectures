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

Asked by Erdős and Sauer [Er75] [Er78] [Er81]. Resolved by Janzer and Sudakov [JaSu23], who
proved that there exists some $C = C(k) > 0$ such that any graph on $n$ vertices with at
least $C \cdot n \cdot \log(\log(n))$ edges contains a $k$-regular subgraph.

A construction due to Pyber, Rödl, and Szemerédi [PRS95] shows that this
bound is best possible up to the value of the constant $C(k)$. Chakraborti, Janzer,
Methuku, and Montgomery [CJMM24b] proved that $C(k) \ll k^2$, which is best possible
up to absolute constants.

Erdős offered a $100 prize in [Er78] for the case $k = 3$.

[Er75] Erdős, P., _Some recent progress on extremal problems in graph theory_,
  Congressus Numerantium (1975), 3–14.

[Er78] Erdős, P., _Problems and results in combinatorial analysis and combinatorial
  number theory_, Proceedings of the Ninth Southeastern Conference on Combinatorics,
  Graph Theory, and Computing (1978), 29–40.

[Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_,
  Combinatorica 1 (1981), 25–42.

[JaSu23] Janzer, O. and Sudakov, B., _Resolution of the Erdős–Sauer problem on
  regular subgraphs_, Forum Math. Pi (2023), Paper No. e19, 13.

[PRS95] Pyber, L., Rödl, V., and Szemerédi, E., _Dense graphs without 3-regular
  subgraphs_, J. Combin. Theory Ser. B 63 (1995), 41–54.

[CJMM24b] Chakraborti, D., Janzer, O., Methuku, A., and Montgomery, R.,
  _Regular subgraphs at every density_, arXiv:2411.11785 (2024).
-/

open SimpleGraph

namespace Erdos182

/-- $G$ contains a $k$-regular subgraph: there exists a nonempty finite graph $H$ that
is $k$-regular (every vertex has degree exactly $k$) and admits an injective
graph homomorphism into $G$. -/
def ContainsKRegularSubgraph {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (U : Type) (fU : Fintype U) (_ : Nonempty U) (H : SimpleGraph U) (dH : DecidableRel H.Adj),
    haveI := fU; haveI := dH;
    H.IsRegularOfDegree k ∧
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

/--
Erdős Problem 182 — quantitative bound on $C(k)$ [CJMM24b]:

Chakraborti, Janzer, Methuku, and Montgomery proved that the constant $C(k)$ in the
Janzer–Sudakov theorem can be taken to satisfy $C(k) \ll k^2$, which is best possible
up to absolute constants.
-/
@[category research solved, AMS 5]
theorem erdos_182_quantitative :
    ∃ A : ℝ, 0 < A ∧ ∃ n₀ : ℕ,
    ∀ k : ℕ, 3 ≤ k →
    ∀ n : ℕ, n₀ ≤ n →
    ∀ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
      haveI := dG;
      (G.edgeFinset.card : ℝ) ≥ A * (k : ℝ) ^ 2 * n * Real.log (Real.log n) →
      ContainsKRegularSubgraph G k := by
  sorry

/--
Erdős Problem 182 — lower bound (Pyber–Rödl–Szemerédi) [PRS95]:

For every $k \geq 3$, there exist graphs on $n$ vertices with $\Omega(n \cdot \log \log n)$
edges containing no $k$-regular subgraph. This shows the Janzer–Sudakov upper bound
is tight up to the constant.
-/
@[category research solved, AMS 5]
theorem erdos_182_lower :
    ∀ k : ℕ, 3 ≤ k →
    ∃ C : ℝ, 0 < C ∧
    ∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧
    ∃ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
      haveI := dG;
      (G.edgeFinset.card : ℝ) ≥ C * n * Real.log (Real.log n) ∧
      ¬ContainsKRegularSubgraph G k := by
  sorry

/--
Erdős Problem 182 — connected variant (Szemerédi) [Er75]:

Let $F(n,k)$ be the minimum number of edges that guarantees a *connected* $k$-regular
subgraph. Erdős proved $F(n,3) \ll n^{5/3}$. This variant requires the $k$-regular
subgraph to be connected, which is a strictly stronger condition.
-/
@[category research open, AMS 5]
theorem erdos_182_connected :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
    ∀ n : ℕ, n₀ ≤ n →
    ∀ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
      haveI := dG;
      (G.edgeFinset.card : ℝ) ≥ C * (n : ℝ) ^ ((5 : ℝ) / 3) →
      ∃ (U : Type) (fU : Fintype U) (_ : Nonempty U) (H : SimpleGraph U)
        (dH : DecidableRel H.Adj),
        haveI := fU; haveI := dH;
        H.IsRegularOfDegree 3 ∧ H.Connected ∧
        ∃ f : U → Fin n, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v) := by
  sorry

end Erdos182
