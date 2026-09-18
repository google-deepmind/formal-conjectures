/-
Copyright 2025 The Formal Conjectures Authors.

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
# Mathoverflow 1973

Does the 6-sphere $S^6$ admit the structure of a complex manifold?

*References:*
- [mathoverflow/1973](https://mathoverflow.net/questions/1973/),
  asked by user [*Fetchinson0234*](https://mathoverflow.net/users/41312/victor-ramos).
- [Al26] L. Alpöge, [*A compact complex threefold fibred by tori over the projective line, and the six-sphere*](https://alpo.ge/s6.pdf) (2026),
  originally [shared on X](https://x.com/__alpoge__/status/2091639597193368014).
-/
open scoped Manifold
namespace Mathoverflow1973

/-- The unit `n`-sphere, defined as `Metric.sphere 0 1` in `EuclideanSpace ℝ (Fin (n + 1))`. -/
abbrev unitSphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) := Metric.sphere 0 1

/--
Does the 6-sphere admit a complex structure, i.e. an atlas of holomorphically compatible charts
relating it to `EuclideanSpace ℂ (Fin 3)`? This is known as the Hopf Problem.

The answer is yes, see [Al26].
Formalisation of the proof by Boris Alexeev.
-/
@[category research solved, AMS 32,
  formal_proof using lean4 at "https://github.com/plby/HopfProblem/blob/9ac8a456b526527837d7082ff775213ca8bc9809/Solution.lean"]
theorem mathoverflow_1973 :
    answer(True) ↔ ∃ atlas : ChartedSpace (EuclideanSpace ℂ (Fin 3)) (unitSphere 6),
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) 1 (unitSphere 6) := by
  sorry

end Mathoverflow1973
