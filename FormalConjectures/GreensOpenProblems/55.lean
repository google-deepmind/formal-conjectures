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
import FormalConjecturesForMathlib.Combinatorics.Additive.GowersNorm

/-!
# Ben Green's Open Problem 55

*Reference:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.55)
- [Au14] T. Austin, Partial difference equations over compact Abelian groups, I: modules of solutions,
  https://arxiv.org/abs/1305.7269.
- [GrTa10] Green, Benjamin, and Terence Tao. "Linear equations in primes."
  Annals of mathematics (2010): 1753-1850.
- [GTZ12] Green, Ben, Terence Tao, and Tamar Ziegler. "An inverse theorem for the Gowers $U^{s+1}[N]$-norm."
  Annals of Mathematics (2012): 1231-1372.
-/

namespace Green55

open scoped BigOperators
open Complex

/-- Shorthand notation for `𝔽 p n` over `p, n` as variables. -/
local macro "𝔽ₚⁿ" : term => `(𝔽 $(Lean.mkIdent `p) $(Lean.mkIdent `n))

/--
The fourth power of the box norm of a function $g : G \times G \to \mathbb{C}$ on a finite type $G$.
See [GrTa10, Appendix B.1].
-/
noncomputable def boxNorm4 {G : Type*} [Fintype G] (g : G × G → ℂ) : ℝ :=
  (1 / (Nat.card G : ℝ)^4) * (∑ x₁ : G, ∑ x₂ : G, ∑ y₁ : G, ∑ y₂ : G,
    g (x₁, y₁) * star (g (x₁, y₂)) * star (g (x₂, y₁)) * g (x₂, y₂)).re

/--
Let $p$ be an odd prime and suppose that $f : \mathbb{F}_p^n \times \mathbb{F}_p^n \to \mathbb{C}$
is a function bounded pointwise by 1. Suppose that
$\mathbb{E}_h \lVert \Delta_{(h,h)} f \rVert_{\square}^4 \geq \delta$.

Does $f$ correlate with a function of the form $a(x)b(y)c(x+y)(-1)^{q(x,y)}$?

NOTE: here "correlate" means that the inner product is at least $C(\delta) > 0$, see [GTZ12, Conjecture 1.2].
-/
@[category research open, AMS 5 11]
theorem green_55 :
    answer(sorry) ↔ ∀ (p : ℕ) [Fact p.Prime] (hp : p ≠ 2), ∃ C : ℝ → ℝ, (∀ δ > 0, 0 < C δ) ∧
      ∀ (δ : ℝ) (hδ : 0 < δ) (n : ℕ)

      -- Edge case: avoid the trivial truth  $|f(0,0)| \leq 1$ if n = 0 (single point domain)
      (hn : 1 ≤ n)

      (f : 𝔽ₚⁿ × 𝔽ₚⁿ → ℂ)
      (hf : ∀ x, ‖f x‖ ≤ 1)

      -- Since f is 1-bounded, and since the box norm counts bounded configurations, the expectation
      -- of the box norm will never exceed 1. If $\delta > 1$, `h_bound` is vacuously false,
      -- rendering the entire implication trivially true.
      (hδ_le : δ ≤ 1)

      (h_bound : (1 / (p^n : ℝ)) * ∑ h : 𝔽ₚⁿ, boxNorm4 (multiplicativeDerivative (h, h) f) ≥ δ),
      ∃ (a b c : 𝔽ₚⁿ → ℂ) (q : 𝔽ₚⁿ × 𝔽ₚⁿ → ℤ),

        -- Common assumption for inverse Gowers norm theorems, prevents trivial solutions by
        -- arbitrarily scaling one of the functions (and thus the correlation).
        (∀ x, ‖a x‖ ≤ 1) ∧ (∀ x, ‖b x‖ ≤ 1) ∧ (∀ x, ‖c x‖ ≤ 1) ∧

        ‖(1 / (p^(2*n) : ℝ)) * ∑ x : 𝔽ₚⁿ, ∑ y : 𝔽ₚⁿ,
          f (x, y) * star (a x * b y * c (x + y) * (-1 : ℂ) ^ q (x, y))‖ ≥ C δ := by
  sorry

end Green55
