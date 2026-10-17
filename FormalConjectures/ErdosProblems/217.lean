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
# Erdős Problem 217

*Reference:* [Erdős Problem 217](https://www.erdosproblems.com/217)
-/

namespace Erdos217

open EuclideanGeometry

/-- For which $n$ do there exist $n$ points in $\mathbb{R}^2$, no three on a line and no four on
a circle, that determine $n-1$ distinct distances whose multiplicities are
$1,2,\ldots,n-1$? -/
@[category research open, AMS 5 52]
theorem erdos_217 : answer(sorry) = {n : ℕ | 0 < n ∧ ∃ P : Finset ℝ²,
    P.card = n ∧ InGeneralPosition (P : Set ℝ²) ∧
      (distanceSet P).card = n - 1 ∧
      (distanceSet P).image (distanceMultiplicity P) = Finset.Icc 1 (n - 1)} := by
  sorry

end Erdos217
