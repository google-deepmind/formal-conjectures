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
import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 31

*Reference:* [erdosproblems.com/31](https://www.erdosproblems.com/31)

Given any infinite set $A \subset \mathbb{N}$, there exists a set $B$ of natural density zero
such that $A + B$ contains all except finitely many natural numbers. Proved by Lorentz [Lo54].

[Er56] Erdős, P., _Problems and results in additive number theory_. Colloque sur la Théorie
des Nombres, Bruxelles, 1955 (1956), 127-137.

[Er59] Erdős, P., 1959.

[Er65b] Erdős, P., _Extremal problems in number theory_ (1965).

[Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo.,
1971) (1973), 117-138.

[Lo54] Lorentz, G. G., _On a problem of additive number theory_. Proc. Amer. Math. Soc. 5
(1954), 838–840.
-/

open scoped Classical Pointwise

namespace Erdos31

/--
**Erdős Problem 31** (Erdős–Straus, proved by Lorentz [Lo54]):

Given any infinite set $A \subset \mathbb{N}$, there exists a set $B \subseteq \mathbb{N}$
of natural density $0$ such that $A + B$ contains all except finitely many natural numbers.
-/
@[category research solved, AMS 11]
theorem erdos_31 (A : Set ℕ) (hA : A.Infinite) :
    ∃ B : Set ℕ, B.HasDensity 0 ∧
      Set.Finite {n : ℕ | n ∉ A + B} := by
  sorry

end Erdos31
