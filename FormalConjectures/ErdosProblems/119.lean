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
# Erdős Problem 119

*Reference:* [erdosproblems.com/119](https://www.erdosproblems.com/119)
-/

open Filter Finset

namespace Erdos119

/--
Let zᵢ be an infinite sequence of complex numbers such that |zᵢ| = 1 for all i ≥ 1, and for
n ≥ 1 let pₙ(z) = ∏_{i ≤ n} (z - zᵢ).

Let Mₙ = max_{|z| = 1} |pₙ(z)|.

1. Is it true that lim sup Mₙ = ∞?

2. Is it true that there exists c > 0 such that for infinitely many n we have Mₙ > nᶜ?

3. Is it true that there exists c > 0 such that, for all large n, ∑_{k ≤ n} Mₖ > n^{1 + c}?
-/

/-- Definition of the set ℕ_{≥ 1}: -/
def N1 : Type := {n : ℕ // n ≥ 1}

/-- Definition of the unit sequence: -/
variable (z : N1 → ℂ) (hz : ∀ i : N1, ‖z i‖ = 1)

/-- Definition of the polynomial pₙ(z): -/
noncomputable def p (n : N1) : ℂ → ℂ :=
    fun w => ∏ i : range (n.val), (w - z ⟨i + 1, by linarith⟩)

/-- Definition of Mₙ: -/
noncomputable def M (n : N1) : ℝ :=
    sSup {x | ∃ (w : ℂ), ‖w‖ = 1 ∧ x = ‖p z n w‖}

/-- Question 1:

Wagner [Wa80] proved that there is some c > 0 with Mₙ > (log n)ᶜ infintely often.

[Wa80] Wagner, Gerold, On a problem of {E}rdős in {D}iophantine approximation. Bull. London Math. Soc. (1980), 81--88.
-/
@[category research closed, AMS 30]
theorem erdos_119_1 :
    limsup (fun n =>  M z n) atTop = ∞ ↔ answer(True) := by
  sorry

/-- Question 2:

Beck [Be91] proved that there exists some c > 0 such that max_{n ≤ N} Mₙ > Nᶜ.

[Be91] Beck, J., The modulus of polynomials with zeros on the unit circle: A problem of Erdős. Annals of Math. (1991), 609-651.
-/
@[category research closed, AMS 30]
theorem erdos_119_2 :
    ∃ (c : ℝ) (hc : c > 0), ∀ (N : ℕ), ∃ n, n ≥ N ∧ M z ⟨n + 1, by linarith⟩ > n ^ c ↔ answer(True) := by
  sorry

/-- Question 3: -/
@[category research open, AMS 30]
theorem erdos_119_3 :
    ∃ (c : ℝ) (hc : c > 0), ∃ (N : ℕ), ∀ n, n ≥ N →
      ∑ k : range n, M z ⟨k + 1, by linarith⟩ > n ^ (1 + c) ↔ answer(sorry) := by
  sorry

end Erdos119
