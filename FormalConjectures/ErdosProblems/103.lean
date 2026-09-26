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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 103

*References:*
- [erdosproblems.com/103](https://www.erdosproblems.com/103)
-/

@[expose] public section

open Filter EuclideanGeometry

namespace Erdos103

/-- A finite set of points is *separated* if any two distinct points are at distance at
least $1$. -/
def IsSeparated (A : Finset ℝ²) : Prop :=
  ∀ᵉ (x ∈ A) (y ∈ A), x ≠ y → 1 ≤ dist x y

/-- `A` is a *minimiser* for `n` if it is a separated set of `n` points whose diameter is at
most the diameter of every separated set of `n` points. -/
def IsMinimiser (n : ℕ) (A : Finset ℝ²) : Prop :=
  A.card = n ∧ IsSeparated A ∧
    ∀ B : Finset ℝ², B.card = n → IsSeparated B →
      Metric.diam (A : Set ℝ²) ≤ Metric.diam (B : Set ℝ²)

/-- Two finite sets of points are *congruent* if an isometry of the plane maps one onto the
other. -/
def Congruent (A B : Finset ℝ²) : Prop :=
  ∃ f : ℝ² ≃ᵢ ℝ², f '' A = B

/-- `h n` is the number of pairwise incongruent minimisers for `n` points. It is the supremum
of the sizes of finite families of pairwise incongruent minimisers. It is `⊤` if there are
infinitely many congruence classes. -/
noncomputable def h (n : ℕ) : ℕ∞ :=
  ⨆ (S : Finset (Finset ℝ²)) (_ : (∀ A ∈ S, IsMinimiser n A) ∧
      ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ¬ Congruent A B), (S.card : ℕ∞)

/--
Let $h(n)$ count the number of incongruent sets of $n$ points in $\mathbb{R}^2$ which minimise
the diameter subject to the constraint that $d(x,y)\geq 1$ for all points $x\neq y$. Is it true
that $h(n)\to \infty$?
-/
@[category research open, AMS 52]
theorem erdos_103 : answer(sorry) ↔ Tendsto h atTop atTop := by
  sorry

/--
It is not even known whether $h(n)\geq 2$ for all large $n$.
-/
@[category research open, AMS 52]
theorem erdos_103.variants.two_le : answer(sorry) ↔ ∀ᶠ n in atTop, 2 ≤ h n := by
  sorry

end Erdos103
