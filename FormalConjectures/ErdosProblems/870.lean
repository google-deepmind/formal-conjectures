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
# Erdős Problem 870

*Reference:* [erdosproblems.com/870](https://www.erdosproblems.com/870)

[ErNa88] Erdős, P. and Nathanson, M., _Minimal asymptotic bases with prescribed densities_,
Illinois J. Math. 32 (1988), 562-574.

[ErNa79] Erdős, P. and Nathanson, M., _Systems of distinct representatives and minimal
bases in additive number theory_ (1979), 89-107.

[Ha56] Härtter, E., _Ein Beitrag zur Theorie der Minimalbasen_,
J. Reine Angew. Math. 196 (1956), 170-204.

[Na74] Nathanson, M., _Minimal bases and maximal nonbases in additive number theory_,
J. Number Theory (1974), 324-333.
-/

open Real

namespace Erdos870

/-- A set $A \subseteq \mathbb{N}$ is an additive basis of order $k$ if every sufficiently large
natural number can be represented as a sum of at most $k$ elements of $A$
(with repetition allowed). -/
def IsAdditiveBasis (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∃ (l : List ℕ), l.length ≤ k ∧ (∀ x ∈ l, x ∈ A) ∧ l.sum = n

/-- A set $A$ is a minimal additive basis of order $k$ if it is a basis of order $k$,
but removing any single element makes it no longer a basis of order $k$. -/
def IsMinimalAdditiveBasis (A : Set ℕ) (k : ℕ) : Prop :=
  IsAdditiveBasis A k ∧ ∀ a ∈ A, ¬ IsAdditiveBasis (A \ {a}) k

/-- The number of representations of $n$ as a sum of at most $k$ elements from $A$.
A representation is a weakly increasing (non-decreasing) list of elements of $A$
with length at most $k$ summing to $n$. Using weakly increasing lists gives a
canonical representative for each multiset. -/
noncomputable def repCount (A : Set ℕ) (k n : ℕ) : ℕ :=
  Set.ncard {l : List ℕ | l.length ≤ k ∧ l.Pairwise (· ≤ ·) ∧
    (∀ x ∈ l, x ∈ A) ∧ l.sum = n}

/--
Erdős Problem 870 [ErNa88]:

For every $k \geq 3$, does there exist $c > 0$ (depending only on $k$) such that for every
additive basis $A$ of order $k$, if the representation count $r(n) \geq c \cdot \log(n)$ for
all sufficiently large $n$, then $A$ contains a minimal additive basis of order $k$?

Erdős and Nathanson [ErNa79] proved this for $k = 2$ when
$1_A * 1_A(n) > (\log(4/3))^{-1} \log n$ for all large $n$.

Härtter [Ha56] and Nathanson [Na74] proved that there exist additive bases
which do not contain any minimal additive bases.

See also problem 868.
-/
@[category research open, AMS 11]
theorem erdos_870 : answer(sorry) ↔ ∀ (k : ℕ), k ≥ 3 →
    ∃ c : ℝ, c > 0 ∧
      ∀ (A : Set ℕ), IsAdditiveBasis A k →
        (∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → (repCount A k n : ℝ) ≥ c * Real.log n) →
        ∃ B : Set ℕ, B ⊆ A ∧ IsMinimalAdditiveBasis B k := by
  sorry

/-- Erdős and Nathanson [ErNa79] proved that for $k = 2$, if the convolution
$1_A * 1_A(n) > (\log \frac{4}{3})^{-1} \log n$ for all sufficiently large $n$,
then $A$ contains a minimal additive basis of order $2$. -/
@[category research solved, AMS 11]
theorem erdos_870.variants.k_eq_2 :
    answer(True) ↔ ∀ (A : Set ℕ), IsAdditiveBasis A 2 →
      (∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        (Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n} : ℝ) >
          (Real.log (4 / 3))⁻¹ * Real.log n) →
      ∃ B : Set ℕ, B ⊆ A ∧ IsMinimalAdditiveBasis B 2 := by
  sorry

/-- Härtter [Ha56] and Nathanson [Na74] proved that there exist additive bases of any
order $k \geq 2$ which do not contain any minimal additive bases. -/
@[category research solved, AMS 11]
theorem erdos_870.variants.Hartter_Nathanson (k : ℕ) (hk : 1 < k) :
    ∃ (A : Set ℕ), IsAdditiveBasis A k ∧
      ∀ B : Set ℕ, B ⊆ A → IsAdditiveBasis B k →
        ∃ b ∈ B, IsAdditiveBasis (B \ {b}) k := by
  sorry

end Erdos870
