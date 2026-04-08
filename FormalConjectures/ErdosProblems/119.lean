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

/-
Here we use 0-indexing for generality and convenience, while in the original problem
formulation 1-indexing was used. This change does not affect the meaning of the problem.
In the description of the problem below we remain faithful to the original one.
-/

/-- Let $z_i$ be an infinite sequence of complex numbers such that $|z_i| = 1$ for all $i \geq 1$.
For $n \geq 1$ let $p_n(z) = \prod_{i \leq n} (z - z_i)$. -/
noncomputable def p (z : ℕ → ℂ) (n : ℕ) : ℂ → ℂ :=
    fun w => ∏ i ∈ range n, (w - z i)

/-- Let $M_n = \max_{|z| = 1} |p_n(z)|$. -/
noncomputable def M (z : ℕ → ℂ) (n : ℕ) : ℝ :=
    sSup { (‖p z n w‖) | (w : ℂ) (_ : ‖w‖ = 1) }

/-- Question 1:

Is it true that $\limsup M_n = \infty$?

Wagner [Wa80] proved that there is some $c > 0$ with $M_n > (\log n)^c$ infintely often.

[Wa80] Wagner, Gerold, On a problem of {E}rdős in {D}iophantine approximation. Bull. London Math. Soc. (1980), 81--88.
-/
@[category research solved, AMS 30]
theorem erdos_119.parts.i :
    answer(True) ↔ ∀ (z : ℕ → ℂ) (hz : ∀ i : ℕ, ‖z i‖ = 1),
      atTop.limsup (fun n => (M z n : EReal)) = ⊤ := by
  sorry

/-- Question 2:

Is it true that there exists $c > 0$ such that for infinitely many $n$ we have $M_n > n^c$?

Beck [Be91] proved that there exists some $c > 0$ such that $\max_{n \leq N} M_n > N^c$.

[Be91] Beck, J., The modulus of polynomials with zeros on the unit circle: A problem of Erdős. Annals of Math. (1991), 609-651.
-/
@[category research solved, AMS 30]
theorem erdos_119.parts.ii :
    answer(True) ↔ ∀ (z : ℕ → ℂ) (hz : ∀ i : ℕ, ‖z i‖ = 1),
      ∃ (c : ℝ) (hc : c > 0), Infinite {n : ℕ | M z n > n ^ c} := by
  sorry

/-- Question 3:

Is it true that there exists $c > 0$ such that, for all large $n$, $\sum_{k \leq n} M_k > n^{1 + c}$?
-/
@[category research open, AMS 30]
theorem erdos_119.parts.iii :
    answer(sorry) ↔ ∀ (z : ℕ → ℂ) (hz : ∀ i : ℕ, ‖z i‖ = 1),
      ∃ (c : ℝ) (hc : c > 0), ∀ᶠ n in atTop,
        ∑ k ∈ range n, M z k > n ^ (1 + c) := by
  sorry

end Erdos119
