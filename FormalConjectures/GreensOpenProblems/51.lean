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
# Green's Open Problem 51

Suppose that $A \subset \mathbb{F}_2^n$ is a set of density $\alpha$. What is the largest size of coset guaranteed to be contained in $2A$?

*Reference:* [Green's Open Problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.51)
-/

open scoped Pointwise

namespace Green51

/--
Suppose that $A \subset \mathbb{F}_2^n$ is a set of density $\alpha$. What is the largest size of coset
guaranteed to be contained in $2A$?

We phrase this by asking for the optimal lower bound $F(\alpha, n)$ on the dimension
of a subspace $W$ such that a coset of $W$ is contained in $2A$.
-/
@[category research open, AMS 5 11]
theorem green_51 :
    let F := (answer(sorry) : ℝ → ℕ → ℕ)
    (∀ n : ℕ, ∀ A : Finset (Fin n → ZMod 2),
      A.Nonempty →
      let α : ℝ := A.dens
      ∃ (W : Submodule (ZMod 2) (Fin n → ZMod 2)) (v : Fin n → ZMod 2),
        v +ᵥ (W : Set (Fin n → ZMod 2)) ⊆ ↑(2 • A) ∧
        F α n ≤ Module.finrank (ZMod 2) W) ∧
    (∀ F' : ℝ → ℕ → ℕ,
      (∀ n : ℕ, ∀ A : Finset (Fin n → ZMod 2),
        A.Nonempty →
        let α : ℝ := A.dens
        ∃ (W : Submodule (ZMod 2) (Fin n → ZMod 2)) (v : Fin n → ZMod 2),
          v +ᵥ (W : Set (Fin n → ZMod 2)) ⊆ ↑(2 • A) ∧
          F' α n ≤ Module.finrank (ZMod 2) W) →
      ∀ n : ℕ, ∀ A : Finset (Fin n → ZMod 2), A.Nonempty →
        F' A.dens n ≤ F A.dens n) := by
  sorry

end Green51
