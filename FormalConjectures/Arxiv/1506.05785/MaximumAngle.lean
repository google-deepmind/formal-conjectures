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
# Approximation of Quantum Gates using Lattices

*Reference:* [arxiv/1506.05785](https://arxiv.org/pdf/1506.05785)
_On the Approximation of Quantum Gates using Lattices_
by *Alec Greene and Steven Damelin*
-/

namespace Arxiv.«1506.05785»

open scoped EuclideanSpace RealInnerProductSpace

/-- The integer lattice ℤ⁴ as the ℤ-span of the standard basis in 4-dimensional Euclidean space. -/
scoped[EuclideanSpace] notation "ℤ⁴" => Submodule.span ℤ (Set.range (PiLp.basisFun 2 ℝ (Fin 4)))

/--
*Conjecture 3.4*
There exists $0 < \delta < 1$ such that for any $a \in \mathbb{S}^3$,
there exists $b \in \mathbb{Z}^4$ and $k \in \mathbb{Z}$ such that $\|b\| = 5^k$ and
$\langle a, \frac{b}{\|b\|} \rangle \geq 1 - 5^{-\frac{k}{2 - \delta}}.$
-/
@[category research open, AMS 11 81]
theorem conjecture_3_4 : ∃ δ ∈ Set.Ioo (0 : ℝ) 1,
    ∀ (a : EuclideanSpace ℝ (Fin 4)) (ha : ‖a‖ = 1), ∃ (b : ℤ⁴) (k : ℕ), k > 0 ∧ ‖b‖ = 5 ^ k ∧
      1 - 5 ^ (-k / (2 - δ)) ≤ ⟪a, ‖b‖⁻¹ • b⟫ := by
  sorry

end Arxiv.«1506.05785»
