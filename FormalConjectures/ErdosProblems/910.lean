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
# Erdős Problem 910

*Reference:* [erdosproblems.com/910](https://www.erdosproblems.com/910)

Does every connected set in $\mathbb{R}^n$ contain a connected subset which is not a point
and not homeomorphic to the original set? If $n \geq 2$, does every connected set in
$\mathbb{R}^n$ contain more than $2^{\aleph_0}$ many connected subsets?

Asked by Erdős in the 1940s, who thought the answer to both questions is yes.
The answer to both is in fact no, as shown by Rudin [Ru58] (conditional on the
continuum hypothesis).

[Ru58] Rudin, M. E., _A connected subset of the plane_, Fund. Math. 46 (1958), 15-24.
-/

open Set Cardinal Topology

namespace Erdos910

/--
Erdős Problem 910, Part 1 (disproved by Rudin [Ru58]):

Does every connected set in $\mathbb{R}^n$ contain a connected subset which is not a single
point and not homeomorphic to the original set?
-/
@[category research solved, AMS 54]
theorem erdos_910 : answer(False) ↔
    ∀ (n : ℕ), n ≥ 1 →
    ∀ (S : Set (EuclideanSpace ℝ (Fin n))),
    IsConnected S →
    ∃ (T : Set (EuclideanSpace ℝ (Fin n))),
      T ⊆ S ∧ IsConnected T ∧ T.Nontrivial ∧
      IsEmpty (Homeomorph T S) := by
  sorry

/--
Erdős Problem 910, Part 2 (disproved by Rudin [Ru58]):

If $n \geq 2$, does every connected set in $\mathbb{R}^n$ have more than $2^{\aleph_0}$ many
connected subsets?
-/
@[category research solved, AMS 54]
theorem erdos_910.variants.part2 : answer(False) ↔
    ∀ (n : ℕ), n ≥ 2 →
    ∀ (S : Set (EuclideanSpace ℝ (Fin n))),
    IsConnected S →
    Cardinal.continuum < #{T : Set (EuclideanSpace ℝ (Fin n)) // T ⊆ S ∧ IsConnected T} := by
  sorry

end Erdos910
