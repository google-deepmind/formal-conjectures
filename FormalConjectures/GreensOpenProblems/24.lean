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
# Green's Open Problem 24

References:
- [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.24)
- [Aa19] Aaronson, James. "Maximising the number of solutions to a linear equation in a set of integers."
  Bulletin of the London Mathematical Society 51.4 (2019): 577-594.
- [HaL28] Hardy, G. H., and J. E. Littlewood. "Notes on the theory of series (VIII): an inequality."
  Journal of the London Mathematical Society 1.2 (1928): 105-110.
-/

open Filter

namespace Green24

/--
The maximum number of $\lbrace 0,1,3 \rbrace$ affine translates that a set of size $n$ can
contain.
-/
noncomputable def max013AffineTranslates (n : ℕ) : ℕ :=
  sSup { k |
    ∃ A : Finset ℤ,
      A.card = n ∧
      -- Iterate over (x,y) = (a, a + d) in A × A (x ≠ y), and check if a + 3d = x + 3(y - x) ∈ A
      k = ((A ×ˢ A).filter (fun (x, y) ↦ x ≠ y ∧ x + 3 * (y - x) ∈ A)).card
  }

/--
If $A$ is a set of $n$ integers, what is the maximum number of affine translates of the set
$\lbrace 0,1,3 \rbrace$ that $A$ can contain?

Conjectured in [Aa19] p.579: $\left({1}{3} + o(1)\right) n^2$.
-/
@[category research open, AMS 5 11]
theorem green_24 : ∀ n, max013AffineTranslates n = answer(sorry) := by
  sorry

/-! A collection of associated bounds and conjectured values. -/

namespace variants

/-- From [Aa19] p.577: the trivial upper bound is $n^2$ (non asymptotic) -/
@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/pull/2358", AMS 5 11]
theorem upper_trivial {n : ℕ} : max013AffineTranslates n ≤ n ^ 2 := by
  apply csSup_le
  · exact ⟨_, ⟨(Finset.range n).image Int.ofNat, by
      rw [Finset.card_image_of_injective _ Int.ofNat_injective, Finset.card_range], rfl⟩⟩
  · rintro k ⟨A, hA, rfl⟩
    apply le_trans (Finset.card_filter_le _ _)
    rw [Finset.card_product, hA, pow_two]

/-- The asymptotic constant $\gamma$ defined in [Aa19] p.579. -/
noncomputable def gamma : ℝ :=
  limsup (fun n : ℕ => (max013AffineTranslates n : ℝ) / ((n : ℝ)^2)) atTop

/-- Asymptotic upper bound (1.2) in [Aa19]. Named after Hardy and Littlewood [HaL28]. -/
@[category research open, AMS 5 11]
theorem upper_HL : gamma ≤ 3/4 := by
  sorry

/-- Asymptotic lower bound (1.2) in [Aa19]. Named after Hardy and Littlewood [HaL28]. -/
@[category research open, AMS 5 11]
theorem lower_HL : gamma ≥ 1/12 := by
  sorry

/-- Conjecture p.579 in [Aa19]: $\left({1}{3} + o(1)\right) n^2$. -/
@[category research open, AMS 5 11]
theorem conjecture : gamma = 1/3 := by
  sorry

end variants

end Green24
