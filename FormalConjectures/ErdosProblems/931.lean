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
# Erdős Problem 931

*Reference:* [erdosproblems.com/931](https://www.erdosproblems.com/931)
-/
/--
Let $k_1 \geq k_2 \geq 3$. Are there only finitely many $n_2\geq n_1 + k_1$
such that
$$
  \prod_{1\leq i\leq k_1}(n_1 + i)\ \text{and}\ \prod_{1\leq j\leq k_2} (n_2 + j)
$$
have the same prime factors?
-/
@[category research open, AMS 11]
theorem erdos_931 (k₁ k₂ : ℕ) (h₁ : k₂ ≤ k₁) (h₂ : 3 ≤ k₂) :
    { (n₁, n₂) | n₁ + k₁ ≤ n₂ ∧
      (∏ i ∈ Finset.Icc 1 k₁, (n₁ + i)).primeFactors =
      (∏ j ∈ Finset.Icc 1 k₂, (n₂ + j)).primeFactors }.Finite :=
  sorry

/--
Erdős thought perhaps if the two products have the same factors then
$n_2 > 2(n_1 + k_1)$.
It is an open question whether this is true when allowing a finite number of counterexamples.
-/
@[category research open, AMS 11]
theorem erdos_931.variants.additional_condition (k₁ k₂ : ℕ) (h₁ : k₂ ≤ k₁) (h₂ : 3 ≤ k₂):
    {(n₁, n₂) | n₁ + k₁ ≤ n₂ ∧ n₂ ≤ 2 * (n₁ + k₁) ∧
      (∏ i ∈ Finset.Icc 1 k₁, (n₁ + i)).primeFactors =
      (∏ j ∈ Finset.Icc 1 k₂, (n₂ + j)).primeFactors}.Finite :=
  sorry

/--
In fact there exist counterexamples, like this one found by AlphaProof.
-/
@[category research solved, AMS 11]
theorem erdos_931.variants.additional_condition_nonempty : ∃ (k₁ k₂ : ℕ), ∃ (_h₁ : k₂ ≤ k₁), ∃ (_h₂ : 3 ≤ k₂),
  {(n₁, n₂) | n₁ + k₁ ≤ n₂ ∧ n₂ ≤ 2 * (n₁ + k₁) ∧
      (∏ i ∈ Finset.Icc 1 k₁, (n₁ + i)).primeFactors =
      (∏ j ∈ Finset.Icc 1 k₂, (n₂ + j)).primeFactors}.Nonempty := by
  use 10, 3, (by norm_num), (by norm_num)
  use (0, 13)
  norm_num [Finset.prod_Icc_succ_top]
  norm_num +decide [Nat.primeFactors, Nat.primeFactorsList]

/--
Erdős was unable to prove that if the two products have the same factors
then there must exist a prime between $n_1$ and $n_2$.
-/
@[category research open, AMS 11]
theorem erdos_931.variants.exists_prime (k₁ k₂ n₁ n₂ : ℕ) (h₁ : k₂ ≤ k₁) (h₂ : 3 ≤ k₂)
    (h₃ : n₁ + k₁ ≤ n₂) (h₄ : (∏ i ∈ Finset.Icc 1 k₁, (n₁ + i)).primeFactors =
      (∏ j ∈ Finset.Icc 1 k₂, (n₂ + j)).primeFactors) :
    ∃ (p : ℕ), p.Prime ∧ n₁ ≤ p ∧ p ≤ n₂ :=
  sorry
