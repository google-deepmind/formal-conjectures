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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 681

*Reference:* [erdosproblems.com/681](https://www.erdosproblems.com/681)
-/

namespace Erdos681

/-- `IsLPF p m` says that `p` is the least prime factor of `m`. -/
def IsLPF (p m : ℕ) : Prop := p.Prime ∧ p ∣ m ∧ ∀ q, q.Prime ∧ q ∣ m → p ≤ q

/--
**Erdős problem 681.**
Is it true that for all large $n$ there exists $k$
such that $n + k$ is composite and $p(n+k) > k^2$,
where $p(m)$ is the least prime factor of $m$ ?
-/
@[category research open, AMS 11]
theorem erdos_681 :
    (∃ N, ∀ n > N, ∃ k > 0, (n + k).Composite ∧ ∀ p, IsLPF p (n + k) → p > k ^ 2) ↔
    answer(sorry) := by
  sorry

end Erdos681
