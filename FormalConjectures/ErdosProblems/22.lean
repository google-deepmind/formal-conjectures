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
# Erdős Problem 22

The central problem of Ramsey–Turán theory: writing $\mathrm{rt}(n; k, \ell)$ for the maximum
number of edges of a $K_k$-free graph on $n$ vertices whose largest independent set has size
less than $\ell$, is it true that for every $\epsilon > 0$ and all sufficiently large $n$
$$\mathrm{rt}(n; 4, \epsilon n) \geq n^2/8?$$

Conjectured by Bollobás and Erdős [BoEr76], who constructed such a graph with
$(1/8 + o(1))n^2$ edges. Together with the matching upper bound
$\mathrm{rt}(n; 4, \epsilon n) \leq (1/8 + o(1))n^2$ of Szemerédi [Sz72], this determines the
Ramsey–Turán density of $K_4$ to be $1/8$. The conjecture as stated was proved by Fox, Loh,
and Zhao [FLZ15].

*References:*
* [erdosproblems.com/22](https://www.erdosproblems.com/22)
* [BoEr76] Bollobás, B. and Erdős, P., *On a Ramsey-Turán type problem*. J. Combin. Theory
  Ser. B 21 (1976), 166--168.
* [Sz72] Szemerédi, E., *On graphs containing no complete subgraph with 4 vertices*
  (Hungarian). Mat. Lapok 23 (1972), 113--116.
* [FLZ15] Fox, J., Loh, P.-S., and Zhao, Y., *The critical window for the classical
  Ramsey-Turán problem*. Combinatorica 35 (2015), 435--476.
-/

open Classical Filter SimpleGraph

namespace Erdos22

/--
Let $\epsilon > 0$ and let $n$ be sufficiently large depending on $\epsilon$. Is there a graph
on $n$ vertices with at least $n^2/8$ many edges which contains no $K_4$, such that the largest
independent set has size at most $\epsilon n$?

This is true, as proved by Fox, Loh, and Zhao [FLZ15].
-/
@[category research solved, AMS 5]
theorem erdos_22 : answer(True) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop,
      ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
        (G.indepNum : ℝ) ≤ ε * n ∧ (n : ℝ) ^ 2 / 8 ≤ G.edgeFinset.card := by
  sorry

/--
The matching upper bound, due to Szemerédi [Sz72]: a $K_4$-free graph on $n$ vertices whose
independence number is sublinear in $n$ has at most $(1/8 + o(1))n^2$ edges. That is, for every
$\epsilon > 0$ there is a $\delta > 0$ such that for all sufficiently large $n$, every
$K_4$-free graph $G$ on $n$ vertices with $\alpha(G) \leq \delta n$ has at most
$(1/8 + \epsilon)n^2$ edges.
-/
@[category research solved, AMS 5]
theorem erdos_22.variants.szemeredi_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ (n : ℕ) in atTop,
      ∀ G : SimpleGraph (Fin n), G.CliqueFree 4 →
        (G.indepNum : ℝ) ≤ δ * n →
        (G.edgeFinset.card : ℝ) ≤ (1 / 8 + ε) * n ^ 2 := by
  sorry

/--
The construction of Bollobás and Erdős [BoEr76]: for every $\epsilon > 0$ and $\delta > 0$,
for all sufficiently large $n$ there is a $K_4$-free graph on $n$ vertices with independence
number at most $\delta n$ and at least $(1/8 - \epsilon)n^2$ edges. Together with
`erdos_22.variants.szemeredi_upper` this shows that the Ramsey–Turán density of $K_4$ is $1/8$.
-/
@[category research solved, AMS 5]
theorem erdos_22.variants.bollobas_erdos_lower (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ (n : ℕ) in atTop,
      ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
        (G.indepNum : ℝ) ≤ δ * n ∧ (1 / 8 - ε) * n ^ 2 ≤ G.edgeFinset.card := by
  sorry

/--
The quantitative strengthening proved by Fox, Loh, and Zhao [FLZ15]: there is a constant
$C > 0$ such that for all sufficiently large $n$ there exists a $K_4$-free graph on $n$
vertices with at least $n^2/8$ edges whose largest independent set has size at most
$$C \cdot \frac{(\log\log n)^{3/2}}{(\log n)^{1/2}} \cdot n.$$
-/
@[category research solved, AMS 5]
theorem erdos_22.variants.fox_loh_zhao :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ (n : ℕ) in atTop,
      ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
        (G.indepNum : ℝ) ≤
          C * (Real.log (Real.log n)) ^ (3 / 2 : ℝ) / (Real.log n) ^ (1 / 2 : ℝ) * n ∧
        (n : ℝ) ^ 2 / 8 ≤ G.edgeFinset.card := by
  sorry

/--
A sanity check for `erdos_22.variants.szemeredi_upper`: the empty graph is $K_4$-free and
trivially satisfies the upper bound $(1/8 + \epsilon)n^2$ on the number of edges.
-/
@[category test, AMS 5]
theorem erdos_22.variants.test_bot (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2 := by
  refine ⟨cliqueFree_bot (by norm_num), ?_⟩
  rw [edgeFinset_bot]
  simp only [Finset.card_empty, Nat.cast_zero]
  positivity

end Erdos22
