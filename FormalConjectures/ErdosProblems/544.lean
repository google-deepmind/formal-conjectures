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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 544

*References:*
- [erdosproblems.com/544](https://www.erdosproblems.com/544)
-/

@[expose] public section

open Filter

namespace Erdos544

/--
Show that
$$R(3,k+1)-R(3,k)\to\infty$$
as $k\to \infty$.

A problem of Erdős and Sós.
This problem is #8 in Ramsey Theory in the graphs problem collection.
-/
@[category research open, AMS 5]
theorem erdos_544.parts.i :
    Tendsto (fun k : ℕ ↦ (SimpleGraph.classicalRamsey 3 (k + 1) : ℝ) -
      (SimpleGraph.classicalRamsey 3 k : ℝ)) atTop atTop := by
  sorry

/--
Similarly, prove or disprove that
$$R(3,k+1)-R(3,k)=o(k).$$
-/
@[category research open, AMS 5]
theorem erdos_544.parts.ii : answer(sorry) ↔
    (fun k : ℕ ↦ (SimpleGraph.classicalRamsey 3 (k + 1) : ℝ) -
      (SimpleGraph.classicalRamsey 3 k : ℝ)) =o[atTop] (fun k : ℕ ↦ (k : ℝ)) := by
  sorry

-- TODO: Add variants of the problem.

end Erdos544
