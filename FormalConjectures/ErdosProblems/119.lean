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

open Filter Finset Set

namespace Erdos119

/-- Let $z_i$ be an infinite sequence of complex numbers such that $|z_i| = 1$ for all $i \geq 1$. -/
variable (z : PNat → ℂ) (hz : ∀ i : PNat, ‖z i‖ = 1)

/-- For $n \geq 1$ let $p_n(z) = \prod_{i \leq n} (z - z_i)$. -/
noncomputable def p (n : PNat) : ℂ → ℂ :=
    fun w => ∏ i ∈ range n, (w - z ⟨i + 1, by linarith⟩)

/-- Let $M_n = \max_{|z| = 1} |p_n(z)|$. -/
noncomputable def M (n : PNat) : ℝ :=
    sSup { (‖p z n w‖) | (w : ℂ) (_ : ‖w‖ = 1) }

/-- Question 1:

Is it true that $\limsup M_n = \infty$?

Wagner [Wa80] proved that there is some c > 0 with Mₙ > (log n)ᶜ infintely often.

[Wa80] Wagner, Gerold, On a problem of {E}rdős in {D}iophantine approximation. Bull. London Math. Soc. (1980), 81--88.
-/
@[category research solved, AMS 30]
theorem erdos_119_1 :
    atTop.limsup (fun n => (M z n : EReal)) = ⊤ ↔ answer(True) := by
  sorry

/-- Question 2:

Is it true that there exists $c > 0$ such that for infinitely many $n$ we have $M_n > n^c$?

Beck [Be91] proved that there exists some c > 0 such that max_{n ≤ N} Mₙ > Nᶜ.

[Be91] Beck, J., The modulus of polynomials with zeros on the unit circle: A problem of Erdős. Annals of Math. (1991), 609-651.
-/
@[category research solved, AMS 30]
theorem erdos_119_2 :
    ∃ (c : ℝ) (hc : c > 0), Set.Infinite {n : PNat | M z n > n ^ c} ↔ answer(True) := by
  sorry

/-- Question 3:

Is it true that there exists $c > 0$ such that, for all large $n$, $\sum_{k \leq n} M_k > n^{1 + c}$?
-/
@[category research open, AMS 30]
theorem erdos_119_3 :
    ∃ (c : ℝ) (hc : c > 0), ∀ᶠ n in atTop,
      ∑ k ∈ range n, M z ⟨k + 1, by linarith⟩ > n ^ (1 + c) ↔ answer(sorry) := by
  sorry

end Erdos119
