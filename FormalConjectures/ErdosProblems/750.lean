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
# Erdős Problem 750

*Reference:* [erdosproblems.com/750](https://www.erdosproblems.com/750)

Does there exist, for every function $f$ with $f(m) \to \infty$, a graph with infinite chromatic
number such that every finite set of $m$ vertices contains an independent set of size at least
$m/2 - f(m)$?

See also [Problem #75](https://www.erdosproblems.com/75).

[Er69b] Erdős, P., _Problems and results in chromatic graph theory_. Proof Techniques in Graph
Theory (1969), 27-35.

[ErHa67b] Erdős, P. and Hajnal, A., _On chromatic graphs_. Mat. Lapok (1967), 1-4.

[EHS82] Erdős, P., Hajnal, A., and Szemerédi, E., _On almost bipartite large chromatic
graphs_. Theory and practice of combinatorics (1982), 117-123.

[Er94b] Erdős, P., _Some old and new problems in various branches of combinatorics_ (1994).

[Er95d] Erdős, P., _Problems and results in discrete mathematics_ (1995).
-/

open SimpleGraph

namespace Erdos750

/--
Erdős Problem 750 [Er94b][Er95d]:

Does there exist, for every function $f : \mathbb{N} \to \mathbb{N}$ with $f(m) \to \infty$
as $m \to \infty$, a graph $G$ with infinite chromatic number such that every finite set of
$m$ vertices in $G$ contains an independent set of size at least $m/2 - f(m)$?

In [Er69b] Erdős conjectures this for $f(m) = \varepsilon m$ for any fixed $\varepsilon > 0$.
This follows from a result of Erdős, Hajnal, and Szemerédi [EHS82].

In [ErHa67b] Erdős and Hajnal prove this for $f(m) \geq cm$ for all $c > 1/4$.
-/
@[category research open, AMS 5]
theorem erdos_750 : answer(sorry) ↔
    ∀ f : ℕ → ℕ, (∀ C : ℕ, ∃ M₀ : ℕ, ∀ m : ℕ, m ≥ M₀ → f m ≥ C) →
    ∃ (V : Type) (G : SimpleGraph V),
      (∀ k : ℕ, ¬G.Colorable k) ∧
      ∀ (S : Finset V), ∃ I : Finset V,
        I ⊆ S ∧ G.IsIndepSet ↑I ∧
        (S.card : ℝ) / 2 - (f S.card : ℝ) ≤ (I.card : ℝ) := by
  sorry

/--
Erdős Problem 750 — εm variant [EHS82]:

For every $\varepsilon > 0$, there exists a graph $G$ with infinite chromatic number such that
every finite set of $m$ vertices in $G$ contains an independent set of size at least
$(1/2 - \varepsilon) m$.

This was conjectured by Erdős [Er69b] and follows from a result of Erdős, Hajnal, and
Szemerédi [EHS82].
-/
@[category research solved, AMS 5]
theorem erdos_750_eps :
    ∀ ε : ℝ, ε > 0 →
    ∃ (V : Type) (G : SimpleGraph V),
      (∀ k : ℕ, ¬G.Colorable k) ∧
      ∀ (S : Finset V), ∃ I : Finset V,
        I ⊆ S ∧ G.IsIndepSet ↑I ∧
        (1 / 2 - ε) * (S.card : ℝ) ≤ (I.card : ℝ) := by
  sorry

/--
Erdős Problem 750 — c > 1/4 variant [ErHa67b]:

For every $c > 1/4$, there exists a graph $G$ with infinite chromatic number such that
every finite set of $m$ vertices in $G$ contains an independent set of size at least
$(1/2 - c) m$.

Proved by Erdős and Hajnal [ErHa67b].
-/
@[category research solved, AMS 5]
theorem erdos_750_quarter :
    ∀ c : ℝ, c > 1 / 4 →
    ∃ (V : Type) (G : SimpleGraph V),
      (∀ k : ℕ, ¬G.Colorable k) ∧
      ∀ (S : Finset V), ∃ I : Finset V,
        I ⊆ S ∧ G.IsIndepSet ↑I ∧
        (1 / 2 - c) * (S.card : ℝ) ≤ (I.card : ℝ) := by
  sorry

end Erdos750
