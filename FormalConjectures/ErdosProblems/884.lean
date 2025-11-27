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
# Erdős Problem 884

*References:*
- [erdosproblems.com/884](https://www.erdosproblems.com/884)
- [Tao25](https://terrytao.wordpress.com/wp-content/uploads/2025/09/erdos-884.pdf)
-/



namespace Erdos884

/--
`divisors_increasing n` is the increasingly ordered list of divisors of `n`.
By convention, we set `divisors_increasing 0 = ∅`.
As a `Finset`, this is the same as `Nat.divisors`
-/
abbrev divisors_increasing (n : ℕ) : List ℕ := (List.range (n + 1)).filter (· ∣ n)

noncomputable abbrev sum_inv_of_divisor_pair_differences (n : ℕ) : ℚ :=
    ∑ j : Fin n.divisors.card, ∑ i : Fin  j,
    (1 : ℚ) / (Nat.nth (· ∣ n) j - Nat.nth (· ∣ n) i )

noncomputable abbrev sum_inv_of_consecutive_divisors (n : ℕ) : ℚ :=
    ∑ i : Fin (n.divisors.card - 1),
    (1 : ℚ) / (Nat.nth (· ∣ n) (i + 1) - Nat.nth (· ∣ n) i)

/--
For a natural number n, let `1 = d₁ < ⋯ < d_{τ(n)} = n` denote the divisors of n
in increasing order.
Does it hold that
`∑ 1 ≤ i < j ≤ τ(n), 1 / (d_j - d_i) ⟪ 1 + ∑ 1 ≤ i < τ(n), 1 / (d_{i + 1} - d_i)`
for `n → ∞`, i.e.
`∑ 1 ≤ i < j ≤ τ(n), 1 / (d_j - d_i) ∈ O (1 + ∑ 1 ≤ i < τ(n), 1 / (d_{i + 1} - d_i))`?

In September 2025, Terence Tao gave a conditional _negative_ answer to this conjecture,
disproving it under the assumption of the *Qualitative Hardy-Littlewood Conjecture*,
See [here](https://terrytao.wordpress.com/wp-content/uploads/2025/09/erdos-884.pdf).
However, the conjecture itself remains open.
-/
@[category research open, AMS 11]
theorem erdos_884 :
    sum_inv_of_divisor_pair_differences =O[Filter.atTop] (1 + sum_inv_of_divisor_pair_differences) := by
  sorry


end Erdos884
