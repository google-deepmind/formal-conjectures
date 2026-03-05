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
due to Katz and Tardos.

[Er57] Erdős, P. (1957)

[Er61] Erdős, P. (1961)
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

end Erdos604
