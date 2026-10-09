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
module

public import FormalConjecturesUtil
public import FormalConjectures.ErdosProblems.«183»

/-!
# Erdős Problem 554

*References:*
- [erdosproblems.com/554](https://www.erdosproblems.com/554)
- [Er81c] Erdős, P., *Some new problems and results in graph theory and other branches of
  combinatorial mathematics*. Combinatorics and graph theory (Calcutta, 1980), Lecture Notes in
  Math. 885 (1981), 9-17.
- [BoEr73] Bondy, J. A. and Erdős, P., *Ramsey numbers for cycles in graphs*. J. Combin. Theory
  Ser. B 14 (1973), 46-54.
- [ErGr75] Erdős, P. and Graham, R. L., *On partition theorems for finite graphs*. Infinite and
  finite sets (Colloq., Keszthely, 1973), Colloq. Math. Soc. János Bolyai 10 (1975), 515-527.
- [DaJo17] Day, A. N. and Johnson, J. R., *Multicolour Ramsey numbers of odd cycles*.
  J. Combin. Theory Ser. B 124 (2017), 56-63. [arXiv:1602.07607](https://arxiv.org/abs/1602.07607)
- [JeSk21] Jenssen, M. and Skokan, J., *Exact Ramsey numbers of odd cycles via nonlinear
  optimisation*. Adv. Math. 376 (2021), Paper No. 107444.
  [arXiv:1608.05705](https://arxiv.org/abs/1608.05705)
- [ACJMR26] Axenovich, M., Cames van Batenburg, W., Janzer, O., Michel, L. and Rundström, M.,
  *An improved upper bound for the multicolour Ramsey number of odd cycles*. J. Combin. Theory
  Ser. B 179 (2026), 293-298. [arXiv:2510.17981](https://arxiv.org/abs/2510.17981)
  [doi:10.1016/j.jctb.2026.04.005](https://doi.org/10.1016/j.jctb.2026.04.005)
-/

@[expose] public section

open Filter SimpleGraph

open scoped Topology

namespace Erdos554

/-- $R_k(K_3)$ agrees with `Erdos183.multicolourTriangleRamsey`: a colouring has a monochromatic
triangle exactly when it is not $3$-clique-free. -/
@[category test, AMS 5]
theorem multicolourRamsey_completeGraph_three (k : ℕ) :
    multicolourRamsey k (completeGraph (Fin 3)) = Erdos183.multicolourTriangleRamsey k := by
  simp only [multicolourRamsey, Erdos183.multicolourTriangleRamsey,
    Erdos183.ForcesMonochromaticTriangle, TopEdgeLabeling.CliqueFree, not_forall,
    not_cliqueFree_iff_top_isContained]

/-- The cycle $C_3$ is the triangle $K_3$, so $R_k(C_3) = R_k(K_3)$. -/
@[category test, AMS 5]
theorem multicolourRamsey_cycleGraph_three (k : ℕ) :
    multicolourRamsey k (cycleGraph 3) = multicolourRamsey k (completeGraph (Fin 3)) :=
  congrArg (multicolourRamsey k) cycleGraph_three_eq_top

/-- With one colour the only colouring of $K_m$ is $K_m$ itself, and $K_m$ contains $C_5$
exactly when $m \geq 5$. -/
@[category test, AMS 5]
theorem multicolourRamsey_one_cycleGraph_five : multicolourRamsey 1 (cycleGraph 5) = 5 := by
  sorry

/--
Let $R_k(G)$ denote the minimal $m$ such that if the edges of $K_m$ are $k$-coloured then there
is a monochromatic copy of $G$. Show that
$$\lim_{k\to \infty}\frac{R_k(C_{2n+1})}{R_k(K_3)}=0$$
for any $n\geq 2$.

A problem of Erdős and Graham. The case $n = 1$ is excluded since $C_3 = K_3$. This problem is
#23 in Ramsey Theory in the graphs problem collection.
-/
@[category research open, AMS 5]
theorem erdos_554 (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun k : ℕ ↦ (multicolourRamsey k (cycleGraph (2 * n + 1)) : ℝ) /
      (multicolourRamsey k (completeGraph (Fin 3)) : ℝ)) atTop (𝓝 0) := by
  sorry

/--
The problem is open even for $n = 2$:
$$\lim_{k\to \infty}\frac{R_k(C_5)}{R_k(K_3)}=0.$$
-/
@[category research open, AMS 5]
theorem erdos_554.variants.n_eq_two :
    Tendsto (fun k : ℕ ↦ (multicolourRamsey k (cycleGraph 5) : ℝ) /
      (multicolourRamsey k (completeGraph (Fin 3)) : ℝ)) atTop (𝓝 0) := by
  sorry

/--
Bondy and Erdős [BoEr73] and Erdős and Graham [ErGr75] proved the lower bound
$$n2^k+1\leq R_k(C_{2n+1})$$
for all $n, k \geq 1$. The condition $k \geq 1$ excludes the junk value $R_0(G) = 2$.
-/
@[category research solved, AMS 5]
theorem erdos_554.variants.lower_bound :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k →
      n * 2 ^ k + 1 ≤ multicolourRamsey k (cycleGraph (2 * n + 1)) := by
  sorry

/--
Erdős and Graham [ErGr75] (see also [BoEr73]) proved the upper bound
$$R_k(C_{2n+1})\leq 2n(k+2)!$$
for all $n, k \geq 1$.
-/
@[category research solved, AMS 5]
theorem erdos_554.variants.upper_bound :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k →
      multicolourRamsey k (cycleGraph (2 * n + 1)) ≤ 2 * n * (k + 2).factorial := by
  sorry

/--
Axenovich, Cames van Batenburg, Janzer, Michel and Rundström [ACJMR26] proved that
$$R_k(C_{2n+1}) \leq (4n)^k k^{k/n}$$
for all $n, k \geq 1$, which improves the exponent of the upper bound in
`Erdos554.erdos_554.variants.upper_bound`.
-/
@[category research solved, AMS 5]
theorem erdos_554.variants.acjmr :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k →
      (multicolourRamsey k (cycleGraph (2 * n + 1)) : ℝ) ≤
        (4 * n : ℝ) ^ k * (k : ℝ) ^ ((k : ℝ) / n) := by
  sorry

/--
Day and Johnson [DaJo17] proved that for every $n \geq 1$ there is a constant $c_n > 0$ such that
$$R_k(C_{2n+1}) > 2n(2+c_n)^{k-1}$$
for all sufficiently large $k$. So the lower bound in `Erdos554.erdos_554.variants.lower_bound`
is not sharp for fixed $n$ and large $k$.
-/
@[category research solved, AMS 5]
theorem erdos_554.variants.day_johnson :
    ∀ n : ℕ, 1 ≤ n → ∃ c > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      (2 * n : ℝ) * (2 + c) ^ (k - 1) < (multicolourRamsey k (cycleGraph (2 * n + 1)) : ℝ) := by
  sorry

/--
Jenssen and Skokan [JeSk21] proved that the lower bound in
`Erdos554.erdos_554.variants.lower_bound` is sharp for fixed $k$ and large $n$: for every
$k \geq 2$,
$$R_k(C_{2n+1}) = n2^k+1$$
for all sufficiently large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_554.variants.jenssen_skokan :
    ∀ k : ℕ, 2 ≤ k → ∀ᶠ n : ℕ in atTop,
      multicolourRamsey k (cycleGraph (2 * n + 1)) = n * 2 ^ k + 1 := by
  sorry

end Erdos554
