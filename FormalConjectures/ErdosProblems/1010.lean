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
# Erdős Problem 1010

*Reference:* [erdosproblems.com/1010](https://www.erdosproblems.com/1010)

Rademacher proved that every graph on $n$ vertices with $\lfloor n^2/4 \rfloor + 1$
edges contains at least $\lfloor n/2 \rfloor$ triangles. Erdős [Er62d] proved this
for $t < cn$ for some constant $c > 0$.

This was proved independently by Lovász and Simonovits [LoSi76] and Nikiforov and
Khadzhiivanov [NiKh81].
-/

open SimpleGraph

namespace Erdos1010

/-- The number of triangles (3-cliques) in a simple graph on `Fin n`. -/
noncomputable def triangleCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Nat.card {s : Finset (Fin n) // G.IsNClique 3 s}

/--
Erdős Problem 1010 [Er62d]:

Let $t < \lfloor n/2 \rfloor$. Every graph on $n$ vertices with
$\lfloor n^2/4 \rfloor + t$ edges contains at least $t \cdot \lfloor n/2 \rfloor$
triangles.

Proved independently by Lovász–Simonovits [LoSi76] and
Nikiforov–Khadzhiivanov [NiKh81].
-/
@[category research solved, AMS 5]
theorem erdos_1010 (n : ℕ) (t : ℕ) (ht : t < n / 2)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hedge : G.edgeFinset.card ≥ n ^ 2 / 4 + t) :
    triangleCount G ≥ t * (n / 2) := by
  sorry

end Erdos1010
