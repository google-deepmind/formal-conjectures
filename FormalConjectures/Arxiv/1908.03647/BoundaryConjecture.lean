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
# The boundary conjecture for doubly stochastic matrices

A. Harlev, C. R. Johnson and D. Lim, *The Doubly Stochastic Single Eigenvalue Problem:
A Computational Approach*, [Conjecture 2.7](https://arxiv.org/pdf/1908.03647#page=4).
-/

@[expose] public section

namespace HarlevJohnsonLim

/-- The set $DS_n$ of complex eigenvalues of real doubly stochastic matrices of order $n$. -/
def eigenvalueRegion (n : ℕ) : Set ℂ :=
  {z | ∃ A ∈ doublyStochastic ℝ (Fin n), z ∈ spectrum ℂ (A.map Complex.ofReal)}

/-- Every boundary point of $DS_n$ is an eigenvalue of a convex combination of at most two
permutation matrices of order $n$. -/
@[category research open, AMS 15]
theorem boundary_conjecture (n : ℕ) (hn : 0 < n) {z : ℂ} (hz : z ∈ frontier (eigenvalueRegion n)) :
    ∃ (σ τ : Equiv.Perm (Fin n)) (t : ℝ), t ∈ Set.Icc 0 1 ∧
      z ∈ spectrum ℂ (t • σ.permMatrix ℂ + (1 - t) • τ.permMatrix ℂ) := by
  sorry

end HarlevJohnsonLim
