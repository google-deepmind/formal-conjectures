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
# Ben Green's Open Problem 18

*Reference:*
- [Gr26] [Ben Green's Open Problem 18](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.18)
- [Au16] Austin, Tim. "Ajtai–Szemerédi theorems over quasirandom groups." Recent trends in
  combinatorics. Cham: Springer International Publishing, 2016. 453-484.
- [So13] Solymosi, Jozsef. "Roth-type theorems in finite groups." European Journal of Combinatorics
  34.8 (2013): 1454-1458.
- [Go01] Gowers, William T. "A new proof of Szemerédi's theorem." Geometric & Functional Analysis
  GAFA 11.3 (2001): 465-588.
-/

open Finset

namespace Green18

/--
The number of triples $(x, y, g)$ in $G^3$ such that $g \neq e$, and $(x, y), (gx, y), (x, gy)$ are
all in $A$. These are called "naive corners" by [Au16].
-/
def numNaiveCorners {G : Type*} [Group G] [Fintype G] [DecidableEq G] (A : Finset (G × G)) : ℕ :=
  (
    (univ : Finset (G × G × G)).filter
    fun ⟨x, y, g⟩ => g ≠ 1 ∧ (x, y) ∈ A ∧ (g * x, y) ∈ A ∧ (x, g * y) ∈ A
  ).card

/--
Suppose that $G$ is a finite group, and let $A \subset G \times G$ be a subset of density $\alpha$.
Is it true that there are $\gg_\alpha |G|^3$ triples $x, y, g$ such that $(x, y), (gx, y), (x, gy)$
all lie in $A$?

Note: A is taken as $\alpha$-dense, i.e. $|A| \ge \alpha |G|^2$ [Au16, Question 2]
-/
@[category research open, AMS 05 11 20]
theorem green_18 : answer(sorry) ↔
    ∀ α > 0, ∃ c > 0, ∃ m₀ : ℕ,
      ∀ (G : Type*) [Group G] [Fintype G] [DecidableEq G] (A : Finset (G × G)),
      Fintype.card G ≥ m₀ →
      (A.card : ℝ) ≥ α * (Fintype.card G) ^ 2 →
      (numNaiveCorners A : ℝ) ≥ c * (Fintype.card G) ^ 3 := by
  sorry

/--
The number of triples $(x, y, g)$ in $G^3$ such that $g \neq e$, and $(x, y), (xg, y), (x, gy)$ are
all in $A$. These are called "BMZ corners" by [Au16].
-/
def numBmzCorners {G : Type*} [Group G] [Fintype G] [DecidableEq G] (A : Finset (G × G)) : ℕ :=
  (
    (univ : Finset (G × G × G)).filter
    fun ⟨x, y, g⟩ => g ≠ 1 ∧ (x, y) ∈ A ∧ (x * g, y) ∈ A ∧ (x, g * y) ∈ A
  ).card

/--
[So13] proved this is true for "BMZ corners". Follows from the proof of Theorem 2.1, p.1456-1457.
-/
@[category research solved, AMS 05 11 20]
theorem green_18.bmz_corners : ∀ α > 0, ∃ c > 0, ∃ m₀ : ℕ,
    ∀ (G : Type*) [Group G] [Fintype G] [DecidableEq G] (A : Finset (G × G)),
    Fintype.card G ≥ m₀ →
    (A.card : ℝ) ≥ α * (Fintype.card G) ^ 2 →
    (numBmzCorners A : ℝ) ≥ c * (Fintype.card G) ^ 3 := by
  sorry

end Green18
