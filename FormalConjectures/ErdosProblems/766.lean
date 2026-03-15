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
# Erdős Problem 766

*Reference:* [erdosproblems.com/766](https://www.erdosproblems.com/766)

[Er64c] Erdős, P., _On extremal problems of graphs and generalized graphs_.
Israel J. Math. **2** (1964), 183–190.

Let $f(n;k,l) = \min \operatorname{ex}(n;G)$, where $G$ ranges over all graphs with $k$ vertices
and $l$ edges.

Give good estimates for $f(n;k,l)$ in the range $k < l \leq k^2/4$. For fixed $k$ and
large $n$, is $f(n;k,l)$ a strictly monotone function of $l$?

Dirac and Erdős proved independently that when $l = \lfloor k^2/4 \rfloor + 1$,
$f(n;k,l) \leq \lfloor n^2/4 \rfloor + 1$.
-/

open SimpleGraph

namespace Erdos766

/-- The minimum extremal number $f(n;k,l)$: the minimum of $\operatorname{ex}(n;G)$ over all
graphs $G$ on $k$ vertices with exactly $l$ edges. -/
noncomputable def minExtremalNumber (n k l : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ G : SimpleGraph (Fin k),
    G.edgeSet.ncard = l ∧ SimpleGraph.extremalNumber n G = m}

/--
Erdős Problem 766, monotonicity conjecture:

For fixed $k$ and large $n$, $f(n;k,l)$ is a strictly monotone function of $l$
in the range $k < l \leq k^2/4$.

Formally: for all $k \geq 2$ and $l < l'$ in the range $(k, k^2/4]$, there exists $N_0$
such that for all $n \geq N_0$, $f(n;k,l) < f(n;k,l')$.
-/
@[category research open, AMS 5]
theorem erdos_766 : answer(sorry) ↔
    ∀ (k l l' : ℕ), k ≥ 2 → k < l → l < l' → 4 * l' ≤ k ^ 2 →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        minExtremalNumber n k l < minExtremalNumber n k l' := by
  sorry

/--
Dirac--Erdős theorem (known result):

When $l = \lfloor k^2/4 \rfloor + 1$, $f(n;k,l) \leq \lfloor n^2/4 \rfloor + 1$.
-/
@[category research solved, AMS 5]
theorem erdos_766.variants.dirac_erdos (k n : ℕ) (hk : k ≥ 2) :
    minExtremalNumber n k (k ^ 2 / 4 + 1) ≤ n ^ 2 / 4 + 1 := by
  sorry

end Erdos766
