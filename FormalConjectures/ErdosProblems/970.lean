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
# Erdős Problem 970

*Reference:* [erdosproblems.com/970](https://www.erdosproblems.com/970)
-/

namespace Erdos970

/--
`IsJacobsthalBound k m` says that every interval of `m` consecutive integers contains an
integer coprime to every positive natural number having at most `k` distinct prime factors.
-/
def IsJacobsthalBound (k m : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
    ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n

/--
Jacobsthal's function, uniformly parametrized by the maximum number of distinct prime factors.
-/
noncomputable def jacobsthalFunction (k : ℕ) : ℕ :=
  sInf {m : ℕ | IsJacobsthalBound k m}

/--
Let $h(k)$ be Jacobsthal's function, defined to as the minimal $m$ such that, if $n$ has at most $k$ prime factors, then in any set of $m$ consecutive integers there exists an integer coprime to $n$. Determine the order of magnitude of $h(k)$. In particular, is it true that $$h(k) \ll k^2?$$
-/
@[category research open, AMS 11]
theorem erdos_970 :
    (∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ C * k ^ 2) ↔
      answer(sorry) := by
  sorry

end Erdos970
