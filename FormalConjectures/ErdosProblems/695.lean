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
# Erdős Problem 695
*Reference:* [erdosproblems.com/695](https://www.erdosproblems.com/695)
-/

open Filter Finset Real

/--
Let $q_1 < q_2 < \cdots$ be a sequence of primes such that $q_{i + 1} \equiv 1 \pmod{q_i}$. Is it
true that
$$
\lim_{k \to \infty} q_k^{1/k} = \infty?
$$
-/
@[category research open, AMS 11]
theorem erdos_695 :
    (∀ {q : ℕ → ℕ},
      StrictMono q →
      (∀ i, (q i).Prime) →
      (∀ i, q (i + 1) % q i = 1) →
      Tendsto (fun k => (q k : ℝ) ^ (1 / k : ℝ)) atTop atTop) ↔ answer(sorry) := by
  sorry

/--
Is there a sequence of primes $q_1 < q_2 < \cdots$ such that $q_{i + 1} \equiv 1 \pmod{q_i}$ and
$$
q(k) \leq \exp(k (\log k)^{1 + o(1)})?
$$
-/
@[category research open, AMS 11]
theorem erdos_695.variant.upperBound :
    (∃ q : ℕ → ℕ,
      StrictMono q ∧
      (∀ i, (q i).Prime) ∧
      (∀ i, q (i + 1) % q i = 1) ∧
      ∃ o : ℕ → ℝ,
        (o =o[atTop] (1 : ℕ → ℝ)) ∧
        ∀ k, q k ≤ exp (k * (log k) ^ (1 + o k))) ↔
    answer(sorry) := by
  sorry
