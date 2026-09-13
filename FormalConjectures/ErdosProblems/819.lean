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
# Erdős Problem 819

*Reference:* [erdosproblems.com/819](https://www.erdosproblems.com/819)
-/

open scoped Pointwise
open Set

namespace Erdos819

/-- $f(N)$ is maximal such that some $A\subseteq\{1,\ldots,N\}$ with $|A|=\lfloor N^{1/2}\rfloor$
has $|(A+A)\cap[1,N]|=f(N)$. -/
noncomputable def f (N : ℕ) : ℕ :=
  sSup { m | ∃ A : Set ℕ, A ⊆ Icc 1 N ∧ A.ncard = N.sqrt ∧
    ((A + A) ∩ Icc 1 N).ncard = m }

/--
Let $f(N)$ be maximal such that there exists $A\subseteq \{1,\ldots,N\}$ with
$\lvert A\rvert=\lfloor N^{1/2}\rfloor$ such that $\lvert (A+A)\cap [1,N]\rvert=f(N)$.
Estimate $f(N)$.
-/
@[category research open, AMS 11]
theorem erdos_819.lower_bound : answer(sorry) ≤ f := by
  sorry

/-- An upper estimate for $f(N)$. -/
@[category research open, AMS 11]
theorem erdos_819.upper_bound : f ≤ answer(sorry) := by
  sorry

end Erdos819
