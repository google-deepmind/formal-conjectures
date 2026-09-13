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
# Erdős Problem 1183

*References:*
- [erdosproblems.com/1183](https://www.erdosproblems.com/1183)
- [Er78] Erdős, Paul, *Problems and results in combinatorial analysis and combinatorial number
  theory*. Proceedings of the Ninth Southeastern Conference on Combinatorics, Graph Theory, and
  Computing (Florida Atlantic Univ., Boca Raton, Fla., 1978) (1978), 29-40.
-/

open Filter Set
open scoped Asymptotics

namespace Erdos1183

/-- A family of finite sets closed under pairwise unions. -/
def IsUnionClosed {α : Type*} [DecidableEq α] (A : Finset (Finset α)) : Prop :=
  ∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A

/-- A family of finite sets closed under pairwise unions and intersections. -/
def IsUnionInterClosed {α : Type*} [DecidableEq α] (A : Finset (Finset α)) : Prop :=
  IsUnionClosed A ∧ ∀ X ∈ A, ∀ Y ∈ A, X ∩ Y ∈ A

/-- A family is monochromatic under a 2-colouring if every member receives the same colour. -/
def IsMonochromatic {α : Type*} (χ : Finset α → Fin 2) (A : Finset (Finset α)) : Prop :=
  ∀ X ∈ A, ∀ Y ∈ A, χ X = χ Y

/-- A 2-colouring of subsets in which colour depends only on cardinality. -/
def IsSizeColouring {α : Type*} (χ : Finset α → Fin 2) : Prop :=
  ∀ X Y : Finset α, X.card = Y.card → χ X = χ Y

/--
The largest `k` such that every 2-colouring of the subsets of `{1, …, n}` admits a
monochromatic family of at least `k` sets satisfying `P`.
-/
noncomputable def guaranteed (n : ℕ) (P : Finset (Finset (Icc (1 : ℕ) n)) → Prop) : ℕ :=
  sSup {k | ∀ χ : Finset (Icc (1 : ℕ) n) → Fin 2,
    ∃ A : Finset (Finset (Icc (1 : ℕ) n)),
      P A ∧ IsMonochromatic χ A ∧ k ≤ A.card}

/--
$f(n)$ is maximal such that in any $2$-colouring of the subsets of $\{1,\ldots,n\}$ there is
always a monochromatic family of at least $f(n)$ sets which is closed under taking unions and
intersections.
-/
noncomputable def f (n : ℕ) : ℕ := guaranteed n IsUnionInterClosed

/--
$F(n)$ is defined as $f(n)$, except that we only require the family be closed under taking unions.
-/
noncomputable def F (n : ℕ) : ℕ := guaranteed n IsUnionClosed

/--
The analogue of `F` obtained by restricting to $2$-colourings in which all subsets of the same
size receive the same colour.
-/
noncomputable def F_size (n : ℕ) : ℕ :=
  sSup {k | ∀ χ : Finset (Icc (1 : ℕ) n) → Fin 2, IsSizeColouring χ →
    ∃ A : Finset (Finset (Icc (1 : ℕ) n)),
      IsUnionClosed A ∧ IsMonochromatic χ A ∧ k ≤ A.card}

/--
Let $f(n)$ be maximal such that in any $2$-colouring of the subsets of $\{1,\ldots,n\}$ there is
always a monochromatic family of at least $f(n)$ sets which is closed under taking unions and
intersections. Estimate $f(n)$.
-/
@[category research open, AMS 5]
theorem erdos_1183 :
    (fun n ↦ (f n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Let $F(n)$ be defined similarly, except that we only require the family be closed under taking
unions. Estimate $F(n)$.
-/
@[category research open, AMS 5]
theorem erdos_1183.variants.estimate_F :
    (fun n ↦ (F n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
In particular, is it true that $F(n)\geq n^{\omega(n)}$ for some $\omega(n)\to \infty$ as
$n\to \infty$, and $F(n)<(1+o(1))^n$?
-/
@[category research open, AMS 5]
theorem erdos_1183.variants.F_growth :
    answer(sorry) ↔
      (∃ ω : ℕ → ℝ, Tendsto ω atTop atTop ∧
        ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ ω n ≤ F n) ∧
      (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (F n : ℝ) < (1 + ε) ^ n) := by
  sorry

/--
It is trivial that $f(n)\geq \frac{n+1}{2}$, since there is a sequence of $n+1$ many nested
subsets.
-/
@[category research solved, AMS 5]
theorem erdos_1183.variants.nested (n : ℕ) : (n + 1 : ℝ) / 2 ≤ f n := by
  sorry

/--
If the colouring is such that all subsets of the same size receive the same colour then Howorka
had proved that $F(n)>n^{\omega(n)}$ for some $\omega(n)\to \infty$, but gave no reference.
-/
@[category research solved, AMS 5]
theorem erdos_1183.variants.howorka :
    ∃ ω : ℕ → ℝ, Tendsto ω atTop atTop ∧
      ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ ω n < F_size n := by
  sorry

end Erdos1183
