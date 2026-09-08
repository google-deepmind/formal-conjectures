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
# Erdős Problem 1035

*References:*
- [erdosproblems.com/1035](https://www.erdosproblems.com/1035)
- [Er93] Erdős, Paul, *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. (1993), 333-350.
-/

namespace Erdos1035

/--
Is there a constant $c > 0$ such that every graph on $2^n$ vertices with minimum degree
$> (1-c) \cdot 2^n$ contains the $n$-dimensional hypercube $Q_n$?

This is Erdős's question [Er93, p. 345].

See also [576] for the extremal number of edges that guarantee a $Q_n$.
-/
@[category research open, AMS 5]
theorem erdos_1035 : answer(sorry) ↔
    ∃ c > 0, ∀ n : ℕ, ∀ (G : SimpleGraph (Fin (2 ^ n))) [DecidableRel G.Adj],
      (∀ v, (G.degree v : ℝ) > (1 - c) * 2 ^ n) →
        (SimpleGraph.hypercube n).IsContained G := by
  sorry

end Erdos1035
