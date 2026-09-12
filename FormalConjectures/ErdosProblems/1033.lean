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

import FormalConjecturesUtil

/-!
# Erdős Problem 1033

*References:*
- [erdosproblems.com/1033](https://www.erdosproblems.com/1033)
- [BoNi05] Bollobás, Béla and Nikiforov, Vladimir, *The sum of degrees in cliques*. Electron. J.
  Combin. (2005), Note 21, 10.
- [Er82e] Erdős, Paul, *Some of my favourite problems which recently have been solved*.
  (1982), 59--79.
- [ErLa85] Erdős, Paul and Laskar, Renu, *A note on the size of a chordal subgraph*. Congr. Numer.
  (1985), 81--86.
- [Fa88] Fan, Genghua, *Degree sum for a triangle in a graph*. J. Graph Theory (1988), 249--263.
- [Fa92] Faudree, Ralph J., *Complete subgraphs with large degree sums*. J. Graph Theory (1992),
  327--334.
-/

open Filter

namespace Erdos1033

open scoped Classical in
/--
The largest real $h(n)$ such that every graph on $n$ vertices with more than $n^2/4$ edges contains
a triangle whose vertices have degrees summing to at least $h(n)$. If no such graph exists, this
is $0$.
-/
noncomputable def h (n : ℕ) : ℝ :=
  sSup {x : ℝ | ∀ G : SimpleGraph (Fin n),
    (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
      ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ x ≤ (∑ v ∈ T, G.degree v : ℝ)}

/--
Let $h(n)$ be such that every graph on $n$ vertices with $>n^2/4$ many edges contains a triangle
whose vertices have degrees summing to at least $h(n)$. Estimate $h(n)$. In particular, is it true
that
$$h(n)\geq (2(\sqrt{3}-1)-o(1))n?$$

A conjecture of Bollobás and Erdős.
-/
@[category research open, AMS 5]
theorem erdos_1033 : answer(sorry) ↔
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n : ℕ in atTop, (2 * (Real.sqrt 3 - 1) - o n) * n ≤ h n := by
  sorry

/--
It is now known that
$$2(\sqrt{3}-1)n +O(1)\geq h(n) \geq \frac{21}{16}n.$$
The lower bound is due to Fan [Fa88].
-/
@[category research solved, AMS 5]
theorem erdos_1033.variants.fan :
    ∀ᶠ n : ℕ in atTop, (21 : ℝ) / 16 * n ≤ h n := by
  sorry

/--
It is now known that
$$2(\sqrt{3}-1)n +O(1)\geq h(n) \geq \frac{21}{16}n.$$
The upper bound is due to Erdős and Laskar [ErLa85].
-/
@[category research solved, AMS 5]
theorem erdos_1033.variants.erdos_laskar :
    ∃ C : ℝ, ∀ n : ℕ, h n ≤ 2 * (Real.sqrt 3 - 1) * n + C := by
  sorry

end Erdos1033
