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
# Erdős Problem 604

*Reference:* [erdosproblems.com/604](https://www.erdosproblems.com/604)

Given $n$ distinct points $A \subset \mathbb{R}^2$, must there be a point $x \in A$ such that
$$\#\{ d(x,y) : y \in A\} \gg n/\sqrt{\log n}?$$

This is the pinned distance problem, a stronger form of Problem \#89 (the distinct
distances problem). The example of an integer grid shows that $n/\sqrt{\log n}$ would
be best possible.

The best known bound is $\gg n^{c - o(1)}$ where $c = (48 - 14e)/(55 - 16e) = 0.8641\ldots$,
due to Katz and Tardos [KaTa04].

[Er57] Erdős, P., _Some unsolved problems_, 1957.

[Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. 6 (1961),
221–254.

[Er75f] Erdős, P., _Problems and results in combinatorial geometry_, 1975, p. 99.

[Er83c] Erdős, P., _Old and new problems in combinatorial analysis and graph theory_, 1983.

[Er85] Erdős, P., _Problems and results in combinatorial geometry_. Discrete geometry and
convexity (New York, 1982), Ann. New York Acad. Sci. 440 (1985), 1–11.

[Er87b] Erdős, P., _Some combinatorial and metric problems in geometry_. Intuitive geometry
(Siófok, 1985) (1987), 167–177, p. 169.

[Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
467–478.

[Er95] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Combinatorics '94 (Catania), Congressus Numerantium 107 (1995).

[Er97b] Erdős, P., _Some of my favourite problems which recently have been solved_,
Proceedings of the International Conference on Discrete Mathematics (ICDM) (1997).

[Er97c] Erdős, P., _Some recent problems and results in graph theory_. Discrete Math.
**164** (1997), 81–85.

[Er97e] Erdős, P., _Some problems and results on combinatorial number theory_ (1997).

[Er97f] Erdős, P., _Some of my new and almost new problems and results in combinatorial
geometry_. (1997)

[KaTa04] Katz, N.H. and Tardos, G., _A new entropy inequality for the Erdős distance problem_.
Towards a theory of geometric graphs (2004), 119–126.
-/

namespace Erdos604

/--
The set of distinct distances from a point $x$ to all points in a finite set $A$ in
$\mathbb{R}^2$.
-/
noncomputable def pinnedDistances (x : EuclideanSpace ℝ (Fin 2))
    (A : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
  A.image (fun y => dist x y)

/--
Erdős Problem 604 [Er57][Er61]:

Given $n$ distinct points $A \subset \mathbb{R}^2$, there must exist a point $x \in A$ such that
the number of distinct distances from $x$ to other points in $A$ is
$\gg n/\sqrt{\log n}$.

Formally: there exists a constant $C > 0$ and a threshold $N_0$ such that for all $n \geq N_0$
and every set $A$ of $n$ points in $\mathbb{R}^2$, some point $x \in A$ has at least
$C \cdot n / \sqrt{\log n}$ distinct pinned distances.

The integer grid shows this would be best possible.
-/
@[category research open, AMS 52]
theorem erdos_604 : answer(sorry) ↔
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
        A.card = n →
        ∃ x ∈ A, ((pinnedDistances x A).card : ℝ) ≥
          C * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by
  sorry

/--
Katz and Tardos [KaTa04] proved that for any $n$ distinct points in $\mathbb{R}^2$, some point
has $\gg n^{c - o(1)}$ pinned distances, where $c = (48 - 14e)/(55 - 16e) \approx 0.8641$.

This is a partial result towards `erdos_604`, which conjectures the stronger bound
$\gg n / \sqrt{\log n}$.

[KaTa04] Katz, N.H. and Tardos, G., _A new entropy inequality for the Erdős distance problem_.
Towards a theory of geometric graphs (2004), 119–126.
-/
@[category research solved, AMS 52]
theorem erdos_604.variants.katz_tardos :
    let c : ℝ := (48 - 14 * Real.exp 1) / (55 - 16 * Real.exp 1)
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
        A.card = n →
        ∃ x ∈ A, ((pinnedDistances x A).card : ℝ) ≥
          (n : ℝ) ^ (c - ε) := by
  sorry

end Erdos604
