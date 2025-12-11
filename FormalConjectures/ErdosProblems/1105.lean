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
# Erdős Problem 1105

*Reference:* [erdosproblems.com/1105](https://www.erdosproblems.com/1105)
-/

namespace Erdos1105

open Classical

/-- The linear coefficient conjectured for `AR(n, C_k)`. -/
noncomputable def cycleCoeff (k : ℕ) : ℝ :=
  (Nat.choose (k - 2) 2 : ℝ) + (1 : ℝ) / (k - 1)

/-- ℓ = ⌊(k - 1)/2⌋. -/
def ell (k : ℕ) : ℕ :=
  (k - 1) / 2

/-- ε = 1 if k is odd, ε = 2 otherwise. -/
def eps (k : ℕ) : ℕ :=
  if k % 2 = 1 then 1 else 2

/--
The anti-Ramsey number AR(n, H) is the maximum number of colors in an edge-coloring of the
complete graph K_n such that there is no rainbow copy of H (a copy where all edges have
different colors). This definition uses a placeholder formalization.
-/
noncomputable def AntiRamseyNumber (n : ℕ) (_H : SimpleGraph (Fin n)) : ℕ :=
  -- Maximum number of colors c such that there exists an edge-coloring of K_n with c colors
  -- and no rainbow (all different colors) copy of H
  0  -- placeholder

/--
Cycle graph C_k with k vertices, where vertex i is adjacent to vertices (i-1) mod k and (i+1) mod k.
-/
def CycleGraph (k : ℕ) : SimpleGraph (Fin k) where
  Adj i j := i ≠ j ∧ ((i.val + 1) % k = j.val ∨ (j.val + 1) % k = i.val)
  symm := by
    intros i j h
    constructor
    · exact h.1.symm
    · exact h.2.symm
  loopless := by
    intros i h
    exact h.1 rfl

/--
Path graph P_k with k vertices, where vertex i is adjacent to vertex i+1 for i < k-1.
-/
def PathGraph (k : ℕ) : SimpleGraph (Fin k) where
  Adj i j := i ≠ j ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val)
  symm := by
    intros i j h
    constructor
    · exact h.1.symm
    · exact h.2.symm
  loopless := by
    intros i h
    exact h.1 rfl

/--
Is it true that the anti-Ramsey number $AR(n, C_k)$ for cycles satisfies
$AR(n, C_k) = \binom{k-2}{2} + \frac{1}{k-1} \cdot n + O(1)$ for $k \geq 3$?
-/
@[category research open, AMS 5]
theorem erdos_1105.cycles : sorry ↔ answer(sorry) := by
  sorry

/--
Is it true that the anti-Ramsey number $AR(n, P_k)$ for paths (where $k \geq 5$ and $n \geq k$)
is exactly $\max\left(\binom{k-2}{2} + 1, \binom{\ell-1}{2} + (\ell-1)(n-\ell+1) + \varepsilon\right)$
where $\ell = \lfloor(k-1)/2\rfloor$ and $\varepsilon = 1$ if $k$ is odd, $\varepsilon = 2$ otherwise?
-/
@[category research open, AMS 5]
theorem erdos_1105.paths : sorry ↔ answer(sorry) := by
  sorry

end Erdos1105
