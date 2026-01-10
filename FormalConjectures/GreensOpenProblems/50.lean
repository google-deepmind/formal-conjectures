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
# Ben Green's Open Problem 50

Suppose that $A \subset \mathbb{F}_2^n$ is a set of density $\alpha$. Does $10A$ contain a coset
of some subspace of dimension at least $n - O(\log(1/\alpha))$?

Here $kA$ denotes the $k$-fold iterated sumset, i.e., the set of all sums of $k$ elements from $A$
(with repetition allowed). In `Mathlib`, this is denoted `k • A` using pointwise scalar
multiplication on sets.

*Reference:* [Ben Green's Open Problem 50](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.6 Problem 50)
-/

open scoped Pointwise

namespace Green50

/-- The density of a finite subset `A` of a finite type `α` is `|A| / |α|`. -/
noncomputable def density {α : Type*} [Fintype α] (A : Finset α) : ℝ :=
  (A.card : ℝ) / (Fintype.card α : ℝ)

/--
Let $A \subset \mathbb{F}_2^n$ be a set of density $\alpha > 0$. Does $10A$ contain a coset
of some subspace of dimension at least $n - O(\log(1/\alpha))$?

More precisely: does there exist an absolute constant $C > 0$ such that for all $n \geq 1$ and all
nonempty $A \subseteq \mathbb{F}_2^n$ with density $\alpha > 0$, the sumset $10A$ contains a coset
of some subspace of dimension at least $n - C \log_2(1/\alpha)$?

The sumset $10A$ is defined as $\{a_1 + a_2 + \cdots + a_{10} : a_i \in A\}$, using the pointwise
scalar multiplication notation `10 • A` where `•` denotes the iterated addition of a set.

Note: We model $\mathbb{F}_2^n$ as `Fin n → ZMod 2`, which is an $n$-dimensional vector space
over $\mathbb{F}_2$.
-/
@[category research open, AMS 5 11]
theorem green_50 : answer(sorry) ↔
    ∃ C > (0 : ℝ), ∀ n : ℕ, ∀ A : Finset (Fin n → ZMod 2),
    A.Nonempty →
    let α := density A
    ∃ (W : Submodule (ZMod 2) (Fin n → ZMod 2)) (v : Fin n → ZMod 2),
      v +ᵥ (W : Set (Fin n → ZMod 2)) ⊆ (10 • A.toSet) ∧
      (n : ℝ) - C * Real.logb 2 (1 / α) ≤ Module.finrank (ZMod 2) W := by
  sorry

/--
A trivial lower bound: any nonempty subset $A$ of $\mathbb{F}_2^n$ satisfies $A \subseteq 10A$,
so $10A$ is nonempty.
-/
@[category undergraduate, AMS 5 11]
theorem green_50.variants.nonempty {n : ℕ} {A : Finset (Fin n → ZMod 2)} (hA : A.Nonempty) :
    Set.Nonempty (10 • A.toSet) := by
  sorry

end Green50
