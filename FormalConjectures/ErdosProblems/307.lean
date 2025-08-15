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
# Erdős Problem 307

*Reference:* [erdosproblems.com/307](https://www.erdosproblems.com/307)
-/

/--
Are there two finite set of primes $P$ and $Q$ such that

$$
1 = \left( \sum_{p \in P} \frac{1}{p} \right) \left( \sum_{q \in Q} \frac{1}{q} \right)
$$
?

Asked by Barbeau [Ba76].

[Ba76] Barbeau, E. J., _Computer challenge corner: Problem 477: A brute force program._
-/
@[category research open, AMS 11]
theorem erdos_307 : (∃ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧
    (1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹))) ↔ answer(sorry) := by
  sorry

/--
Instead of asking for sets of primes, ask only that all primes in the sets be relatively coprime.
-/
@[category research open, AMS 5 11]
theorem erdos_307_coprime : (∃ P Q : Finset ℕ, P.toSet.Pairwise Nat.Coprime ∧
    Q.toSet.Pairwise Nat.Coprime ∧
    (1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹))) ↔ answer(sorry) := by
  sorry
