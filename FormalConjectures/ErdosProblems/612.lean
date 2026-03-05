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
# Erdős Problem 612

*Reference:* [erdosproblems.com/612](https://www.erdosproblems.com/612)

Let $G$ be a connected graph with $n$ vertices, minimum degree $d$, and diameter $D$.

The original conjecture of Erdős, Pach, Pollack, and Tuza [EPPT89] stated:
- If $G$ contains no $K_{2r}$ and $(r-1)(3r+2) \mid d$ then
  $D \leq \frac{2(r-1)(3r+2)}{2r^2-1} \cdot \frac{n}{d} + O(1)$
- If $G$ contains no $K_{2r+1}$ and $(3r-1) \mid d$ then
  $D \leq \frac{3r-1}{r} \cdot \frac{n}{d} + O(1)$

The first case was disproven for $r \geq 2$ by Czabarka, Singgih, and Székely [CSS21].

The amended conjecture (due to [CSS21]) states that if $G$ contains no $K_{k+1}$ then
$D \leq (3 - 2/k) \cdot n/d + O(1)$.

This is known:
- For $k = 2$ ($K_3$-free), proved in [EPPT89]
- For $3$-colourable graphs (weaker than $K_4$-free), by Czabarka, Dankelmann,
  Székely [CDS09]
- For $4$-colourable graphs (weaker than $K_5$-free), by Czabarka, Smith,
  Székely [CSS23]

It is also known that any connected graph on $n$ vertices with minimum degree $d$ has
$D \leq 3n/(d+1) + O(1)$.

[EPPT89] Erdős, P., Pach, J., Pollack, R., and Tuza, Zs., _Radius, diameter, and
minimum degree_. J. Combin. Theory Ser. B 47 (1989), 73-79.

[CSS21] Czabarka, É., Singgih, O., and Székely, L.A., _Counterexample to a conjecture
of Erdős, Pach, Pollack, and Tuza on diameter and minimum degree_. 2021.

[CDS09] Czabarka, É., Dankelmann, P., and Székely, L.A., _Diameter and degree
conditions for $K_{t,t}$-free graphs_. 2009.

[CSS23] Czabarka, É., Smith, S.J., and Székely, L.A., _Diameter bounds for
4-colourable graphs_. 2023.
-/

open SimpleGraph

namespace Erdos612

/--
**Erdős Problem 612** (Amended conjecture, [CSS21]):

If $G$ is a connected $K_{k+1}$-free graph on $n$ vertices with minimum degree $d \geq 1$,
then
$$\operatorname{diam}(G) \leq \left(3 - \frac{2}{k}\right) \cdot \frac{n}{d} + C$$
for some constant $C$ depending only on $k$.
-/
@[category research open, AMS 5]
theorem erdos_612 (k : ℕ) (hk : k ≥ 2) :
    ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.Connected →
      G.CliqueFree (k + 1) →
      G.minDegree ≥ 1 →
      (G.diam : ℝ) ≤ (3 - 2 / (k : ℝ)) * ((n : ℝ) / (G.minDegree : ℝ)) + C := by
  sorry

/--
**Erdős Problem 612** (Known case $k = 2$, [EPPT89]):

If $G$ is a connected triangle-free graph on $n$ vertices with minimum degree $d \geq 1$,
then
$$\operatorname{diam}(G) \leq 2 \cdot \frac{n}{d} + C$$
for some absolute constant $C$.
-/
@[category research solved, AMS 5]
theorem erdos_612.variants.triangle_free :
    ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.Connected →
      G.CliqueFree 3 →
      G.minDegree ≥ 1 →
      (G.diam : ℝ) ≤ 2 * ((n : ℝ) / (G.minDegree : ℝ)) + C := by
  sorry

/--
Known general bound ([EPPT89]):

Any connected graph on $n$ vertices with minimum degree $d \geq 1$ has
$$\operatorname{diam}(G) \leq \frac{3n}{d+1} + O(1).$$
-/
@[category research solved, AMS 5]
theorem erdos_612.variants.general_bound :
    ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.Connected →
      G.minDegree ≥ 1 →
      (G.diam : ℝ) ≤ 3 * ((n : ℝ) / ((G.minDegree : ℝ) + 1)) + C := by
  sorry

end Erdos612
