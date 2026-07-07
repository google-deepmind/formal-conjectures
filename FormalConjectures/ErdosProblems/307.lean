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

namespace Erdos307

open scoped Finset

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
theorem erdos_307 : answer(sorry) ↔ ∃ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) := by
  sorry

/--
Instead of asking for sets of primes, ask only that all elements in the sets be relatively coprime.

Cambie has found several examples when this weakened version is true. For example,
$$
1=\left(1+\frac{1}{5}\right)\left(\frac{1}{2}+\frac{1}{3}\right)
$$
and
$$
1=\left(1+\frac{1}{41}\right)\left(\frac{1}{2}+\frac{1}{3}+\frac{1}{7}\right).
$$
-/
@[category textbook, AMS 5 11]
theorem erdos_307.variants.coprime : answer(True) ↔ ∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 < #P ∧ 1 < #Q ∧
    Set.Pairwise P Nat.Coprime ∧ Set.Pairwise Q Nat.Coprime ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) := by
  show True ↔ _
  simp only [Finset.mem_inter, not_and, true_iff]
  use {1, 5}, {2, 3}
  norm_num +decide

/--
There are no examples known of the weakened coprime version if we insist that $1\not\in P\cup Q$.
-/
@[category research open, AMS 5 11]
theorem erdos_307.variants.coprime_one_notMem : answer(sorry) ↔ ∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 ∉ P ∪ Q ∧
    1 < #P ∧ 1 < #Q ∧ Set.Pairwise P Nat.Coprime ∧ Set.Pairwise Q Nat.Coprime ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) := by
  sorry

/--
A machine-checked **barrier** for Erdős 307 (Bonfioli, 2026): any solution with `Q` nonempty uses at
least 59 primes in total, and `(∏_{p ∈ P} p)² ≥ 4·10¹¹²` — i.e. `∏_{p ∈ P} p ≥ 2·10⁵⁶` (and, by
symmetry, the same for `∏ Q`); so no solution lies below a prime-product of `2.09·10⁵⁶`. The full
`sorry`-free proof is in the linked repository (`Closed.lean` at tag `v1.0.0`): the left conjunct is
`card_ge_59`, the right is `erdos307_barrier_closed`. The only non-logical input is a `native_decide`
evaluation of the first 59 primes; the axioms are `propext, Classical.choice, Quot.sound` together
with that `native_decide`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/ElVec1o/erdos307/blob/v1.0.0/lean/Erdos307/Closed.lean"]
theorem erdos_307.barrier {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hQne : Q.Nonempty)
    (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    59 ≤ #(P ∪ Q) ∧ (4 * 10 ^ 112 : ℚ) ≤ (∏ p ∈ P, (p : ℚ)) ^ 2 := by
  sorry

end Erdos307
