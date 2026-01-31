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
import FormalConjecturesForMathlib.Combinatorics.AP.Basic

/-!
# Green's Open Problem 9

References:
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.9)
- [BlSi20] Bloom, Thomas F., and Olof Sisask. "Breaking the logarithmic barrier in Roth's theorem on
  arithmetic progressions." arXiv preprint arXiv:2007.03528 (2020).
-/

open Filter

namespace Green9

/--
The quantity $r_k(N)$, defined as the size of the largest subset of $\{1, \dots, N\}$ without
non-trivial $k$-term arithmetic progressions.
-/
noncomputable def r (k N : ℕ) : ℕ := (Finset.Icc 1 N).maxAPFreeCard k

/--
Problem 9 (i): is $r_3(N) \ll N(\log N)^{-10}$?

Solved in [BlSi20].
-/
@[category research solved, AMS 5]
theorem green_9_i :
    (fun (N : ℕ) ↦ (r 3 N : ℝ))
      =O[atTop] fun (N : ℕ) ↦ (N : ℝ) * (Real.log N) ^ (-10 : ℝ) := by
  sorry

/--
Problem 9 (ii): is $r_5(N) \ll N(\log N)^{-c}$?
-/
@[category research open, AMS 5]
theorem green_9_ii : answer(sorry) ↔
    ∃ c > (0 : ℝ), (fun (N : ℕ) ↦ (r 5 N : ℝ))
      =O[atTop] fun (N : ℕ) ↦ (N : ℝ) * (Real.log N) ^ (-c) := by
  sorry

/--
Problem 9 (iii): is $r_4(\mathbf{F}_5^n) \ll N^{1-c}$, where $N=5^n$?
-/
@[category research open, AMS 5]
theorem green_9_iii : answer(sorry) ↔
    ∃ c > (0 : ℝ), (fun (n : ℕ) ↦ ((Finset.univ : Finset (Fin n → ZMod 5)).maxAPFreeCard 4 : ℝ))
      =O[atTop] fun (n : ℕ) ↦ ((5 : ℝ) ^ n) ^ (1 - c) := by
  sorry

-- TODO(jeangud): Add some additional bounds from the literature.

end Green9
