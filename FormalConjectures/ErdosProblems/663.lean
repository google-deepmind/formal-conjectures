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
# Erdős Problem 663
*Reference:* [erdosproblems.com/663](https://www.erdosproblems.com/663)
-/


namespace Erdos663

/--
Let $q(n,k)$ denote the least number coprime to all numbers in $[n+1, n+k]$.
-/

noncomputable def q (n k : ℕ) : ℕ :=
    if k > 0 ∧ n > 0
    then sInf {q > 1 | ∀ i ∈ Finset.Icc (n+1) (n+k), q.Coprime i}
    else 0

/--
Is it true that, if $k>1$ is fixed and $n$ is sufficiently large, we have
$q(n,k) < (1 + o(1)) \log n$?
-/
@[category research open, AMS 11]
theorem erdos_663 :
    answer(sorry) ↔ ∀ k > 1, ∃ C > 0, ∀ᶠ n in .atTop, q k n < C * (Real.log ·) := by
    sorry

/--
The bound $q(n,k) < (1 + o(1)) k \log n$ is easy.
-/
@[category research solved, AMS 11]
theorem erdos_663.easy :
    answer(sorry) ↔ ∀ k > 1, ∃ C > 0, ∀ᶠ n in .atTop, q k n < C * k * (Real.log ·) := by
    sorry

end Erdos663
