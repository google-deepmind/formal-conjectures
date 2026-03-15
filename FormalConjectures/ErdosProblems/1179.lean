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
# Erdős Problem 1179

*Reference:* [erdosproblems.com/1179](https://www.erdosproblems.com/1179)

Let $0 < \varepsilon < 1$ and let $g_\varepsilon(N)$ be the minimal $k$ such that if $G$ is an
abelian group of size $N$ and $A \subseteq G$ is a uniformly random subset of size $k$, and
$$F_A(g) = \#\{S \subseteq A : g = \sum_{x \in S} x\},$$
then, with probability $\to 1$ as $N \to \infty$,
$$|F_A(g) - 2^k/N| \leq \varepsilon \cdot 2^k/N$$
for all $g \in G$. Estimate $g_\varepsilon(N)$; in particular, is it true that for all
$\varepsilon > 0$,
$$g_\varepsilon(N) = (1 + o_\varepsilon(1)) \log_2 N?$$

It is trivial that $g_\varepsilon(N) \geq \log_2 N$. Erdős and Rényi proved
$g_\varepsilon(N) \leq (2 + o(1)) \log_2 N + O_\varepsilon(1)$, and Erdős and Hall improved
this to
$$g_\varepsilon(N) \leq (1 + O_\varepsilon(\log \log \log N / \log \log N)) \log_2 N.$$

Related: [Erdős Problem 543](https://www.erdosproblems.com/543).

A problem of Erdős.

[Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
(1973), 117-138.

[ErRe65] Erdős, P. and Rényi, A., *Probabilistic methods in group theory*. J. Analyse Math.
(1965), 127-138.

[ErHa76] Erdős, P. and Hall, R. R., *Probabilistic methods in group theory. II*. Houston J. Math.
(1976), 173-180.
-/

open Filter

open scoped Topology Real

namespace Erdos1179

/-- For a finite abelian group $G$, a subset $A \subseteq G$, and element $g \in G$,
$F_A(g) = \#\{S \subseteq A : \sum_{x \in S} x = g\}$ counts the subsets of $A$ (including
$\emptyset$) whose element-sum equals $g$. -/
def subsetSumCount {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (g : G) : ℕ :=
  (A.powerset.filter (fun S => S.sum id = g)).card

/-- A $k$-subset $A$ of a finite abelian group $G$ of size $N$ is
$\varepsilon$-approximation-uniform if the subset-sum counts are uniformly close to their
"expected" value $2^k/N$:
$$|F_A(g) - 2^k/N| \leq \varepsilon \cdot 2^k/N \quad \text{for all } g \in G.$$ -/
def IsApproxUniform {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (ε : ℝ) (A : Finset G) : Prop :=
  let N : ℕ := Fintype.card G
  let k : ℕ := A.card
  ∀ g : G, |((subsetSumCount A g : ℝ) - (2 : ℝ) ^ k / N)| ≤ ε * (2 : ℝ) ^ k / N

/-- The fraction of $k$-subsets $A$ of a finite abelian group $G$ that are
$\varepsilon$-approximation-uniform. This models the probability that a uniformly random
$k$-subset satisfies the approximation. -/
noncomputable def goodFraction {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (ε : ℝ) (k : ℕ) : ℝ :=
  let all := (Finset.univ : Finset G).powersetCard k
  let good := @Finset.filter (Finset G) (fun A => IsApproxUniform ε A) (Classical.decPred _) all
  good.card / all.card

/-- $g_\varepsilon(N)$ is the minimal $k$ such that for every finite abelian group $G$ of order
$N$, the fraction of $k$-subsets that are $\varepsilon$-approximation-uniform is at least
$1 - 1/N$. This captures the condition "with probability $\to 1$ as $N \to \infty$" for
each $N$. -/
noncomputable def gEps (ε : ℝ) (N : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (G : Type) [hG : AddCommGroup G] [hF : Fintype G] [hD : DecidableEq G],
    Fintype.card G = N →
    @goodFraction G hG hF hD ε k ≥ 1 - 1 / (N : ℝ)}

/--
Erdős Problem 1179:

For all $0 < \varepsilon < 1$, $g_\varepsilon(N) = (1 + o_\varepsilon(1)) \log_2 N$ as
$N \to \infty$, i.e., $g_\varepsilon(N) / \log_2 N \to 1$ as $N \to \infty$.

Here $g_\varepsilon(N)$ is the minimal $k$ such that for every abelian group $G$ of order $N$,
at least a $(1 - 1/N)$ fraction of all $k$-subsets $A$ of $G$ satisfy
$$|F_A(g) - 2^k/N| \leq \varepsilon \cdot 2^k/N \quad \text{for all } g \in G,$$
where $F_A(g) = \#\{S \subseteq A : \sum_{x \in S} x = g\}$.

The lower bound $g_\varepsilon(N) \geq \log_2 N$ is trivial.
Erdős and Rényi [ErRe65] proved $g_\varepsilon(N) \leq (2 + o(1)) \log_2 N + O_\varepsilon(1)$.
Erdős and Hall [ErHa76] proved
$g_\varepsilon(N) \leq (1 + O_\varepsilon(\log \log \log N / \log \log N)) \log_2 N$.
-/
@[category research solved, AMS 5 60]
theorem erdos_1179 : answer(True) ↔
    ∀ ε : ℝ, 0 < ε → ε < 1 →
    Tendsto (fun N : ℕ => (gEps ε N : ℝ) / Real.logb 2 N)
      atTop (nhds 1) := by
  sorry

end Erdos1179
