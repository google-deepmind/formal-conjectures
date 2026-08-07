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
# Erdős Problem 468

*Reference:* [erdosproblems.com/468](https://www.erdosproblems.com/468)

For a natural number `n`, let `D n` be the set of sums
`d₁, d₁ + d₂, d₁ + d₂ + d₃, ...`, where `1 < d₁ < d₂ < ...` are the divisors
of `n`.  The problem asks for the size of
`D n \ ⋃_{m < n} D m`.  It also asks whether, if `f(N)` is the least `n` with
`N ∈ D n`, one has `f(N) = o(N)`, perhaps for almost all `N`.
-/

noncomputable section

namespace Erdos468

open Classical Filter Asymptotics
open scoped Topology

/--
The partial sum of those divisors `d` of `n` satisfying `1 < d ≤ x`.
When `x` runs over the divisors of `n` greater than `1`, these are precisely
the sums `d₁`, `d₁ + d₂`, `d₁ + d₂ + d₃`, ... in increasing divisor order.
-/
def divisorPrefixSum (n x : ℕ) : ℕ := by
  classical
  exact ((Nat.divisors n).filter fun d => 1 < d ∧ d ≤ x).sum fun d => d

/-- The set `D_n` from Erdős problem 468. -/
def D (n : ℕ) : Finset ℕ := by
  classical
  exact ((Nat.divisors n).filter fun d => 1 < d).image fun d => divisorPrefixSum n d

/-- The new elements of `D n` which do not occur in any earlier `D m`. -/
def newDivisorPrefixSums (n : ℕ) : Finset ℕ := by
  classical
  exact (D n).filter fun x => ∀ m : ℕ, m < n → x ∉ D m

/-- `n` is the least index such that `N ∈ D n`. -/
def IsMinimalDPreimage (N n : ℕ) : Prop :=
  N ∈ D n ∧ ∀ m : ℕ, N ∈ D m → n ≤ m

/-- The statement that the minimal preimage function exists and is `o(N)`. -/
def Erdos468MinimalPreimageLittleO : Prop :=
  ∃ f : ℕ → ℕ,
    (∀ N : ℕ, IsMinimalDPreimage N (f N)) ∧
      (fun N : ℕ => (f N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ))

/-- Count the integers up to `N` satisfying a predicate. -/
def countWhereUpTo (P : ℕ → Prop) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter P).card

/-- A predicate on natural numbers holds for a set of natural density one. -/
def HasNaturalDensityOne (P : ℕ → Prop) : Prop :=
  Tendsto
    (fun N : ℕ => (countWhereUpTo P N : ℝ) / (N : ℝ))
    atTop
    (𝓝 1)

/--
The weaker "almost all" version: there is a function which is the minimal
preimage function on a set of natural density one and is still `o(N)`.
-/
def Erdos468MinimalPreimageLittleOAlmostAll : Prop :=
  ∃ f : ℕ → ℕ,
    HasNaturalDensityOne (fun N : ℕ => IsMinimalDPreimage N (f N)) ∧
      (fun N : ℕ => (f N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ))

/-- What is the size of `D n \ ⋃_{m < n} D m`? -/
@[category research open, AMS 11]
theorem erdos_468.parts.i :
    (fun n : ℕ => (newDivisorPrefixSums n).card) = answer(sorry) := by
  sorry

/--
If `f(N)` is the minimal `n` such that `N ∈ D n`, is it true that
`f(N) = o(N)`?
-/
@[category research open, AMS 11]
theorem erdos_468.parts.ii : answer(sorry) ↔ Erdos468MinimalPreimageLittleO := by
  sorry

/-- The "perhaps just for almost all `N`" variant from the problem page. -/
@[category research open, AMS 11]
theorem erdos_468.variants.almost_all :
    answer(sorry) ↔ Erdos468MinimalPreimageLittleOAlmostAll := by
  sorry

end Erdos468

end

