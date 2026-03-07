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
# Erdős Problem 367

*References:*
- [erdosproblems.com/367](https://www.erdosproblems.com/367)
- [ErGr80] P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, L'Enseignement Mathématique (1980).

The problem asks about bounds on products of 2-full parts over short intervals.
-/

open Asymptotics Filter

namespace Erdos367

/-- Product of primes dividing `n` with exponent exactly one. -/
def exactlyOncePrimeDivisorProduct (n : ℕ) : ℕ :=
  (n.factorization.support.filter (fun p => n.factorization p = 1)).prod id

/--
`B₂(n)` in the Erdős Problem 367 statement:
`B₂(n) = n / n'`, where `n'` is the product of all primes dividing `n` exactly once.
-/
def B2 (n : ℕ) : ℕ :=
  n / exactlyOncePrimeDivisorProduct n

/-- Product `∏_{n ≤ m < n+k} B₂(m)`. -/
def intervalB2Product (n k : ℕ) : ℕ :=
  (Finset.range k).prod (fun i => B2 (n + i))

/-- Asymptotic formulation of an `n^(2+o(1))`-type upper bound. -/
def nearlyQuadraticBound (k : ℕ) : Prop :=
  ∃ e : ℕ → ℝ,
    e =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ n in atTop, (intervalB2Product n k : ℝ) ≤ (n : ℝ) ^ (2 + e n)

/-- The stronger variant `≪_k n^2`. -/
def quadraticBound (k : ℕ) : Prop :=
  (fun n ↦ (intervalB2Product n k : ℝ)) =O[atTop] fun n ↦ (n : ℝ) ^ (2 : ℝ)

/--
For fixed `k ≥ 1`, is `∏_{n ≤ m < n+k} B₂(m) ≪ n^(2+o(1))`?
-/
@[category research open, AMS 11]
theorem erdos_367.parts.i : answer(sorry) ↔ ∀ k : ℕ, 1 ≤ k → nearlyQuadraticBound k := by
  sorry

/--
Or perhaps even `∏_{n ≤ m < n+k} B₂(m) ≪_k n^2`?
-/
@[category research open, AMS 11]
theorem erdos_367.parts.ii : answer(sorry) ↔ ∀ k : ℕ, 1 ≤ k → quadraticBound k := by
  sorry

/--
The page notes the easy range `k ≤ 2`; this variant captures that solved subregime.
-/
@[category research solved, AMS 11]
theorem erdos_367.variants.k_le_two : ∀ k : ℕ, k ≤ 2 → quadraticBound k := by
  sorry

/-- `B_r(n)`: product of prime powers `p^a ‖ n` with `a ≥ r`. -/
def Br (r n : ℕ) : ℕ :=
  (n.factorization.support.filter (fun p => r ≤ n.factorization p)).prod
    (fun p => p ^ (n.factorization p))

/-- Product `∏_{n ≤ m < n+k} B_r(m)`. -/
def intervalBrProduct (r n k : ℕ) : ℕ :=
  (Finset.range k).prod (fun i => Br r (n + i))

/--
Discrete limsup-unbounded formulation for the variant in the additional text.
-/
def brRatioUnbounded (r k : ℕ) : Prop :=
  ∀ A : ℕ, ∃ n : ℕ, 1 ≤ n ∧ A * n ≤ intervalBrProduct r n k

/--
Variant question from the additional text: for fixed `r, k ≥ 2`, does there exist `ε > 0`
with unbounded `limsup` behavior for `∏ B_r(m) / n^(1+ε)`?
-/
@[category research open, AMS 11]
theorem erdos_367.variants.higher_full_parts : answer(sorry) ↔
    ∀ r k : ℕ, 3 ≤ r → 2 ≤ k → brRatioUnbounded r k := by
  sorry

end Erdos367
