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
# Green's Open Problem 47

*References:*
- [Gr24] [Ben Green's 100 Open Problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.47)
- [GH14] Green, Ben, and Adam J. Harper. "Inverse questions for the large sieve."
  Geometric and Functional Analysis 24.4 (2014): 1167-1203.
- [HV09] Helfgott, Harald Andrés, and Akshay Venkatesh. "How small must ill-distributed sets be."
  Analytic number theory 2 (2009): 224-234.
- [Wa12] Walsh, Miguel N. "The inverse sieve problem in high dimensions." (2012): 2001-2022.
- [Wa14] Walsh, Miguel N. "The algebraicity of ill-distributed sets."
  Geometric and Functional Analysis 24.3 (2014): 959-967.
-/

open Filter

namespace Green47

/--
Suppose that a large sieve process leaves a set of quadratic size. Is that set quadratic?

The following very particular instance is probably the simplest [Gr24]:
Suppose that $A \subset \mathbb{N}$ is a set with the property that
$|A \pmod p| \leqslant \frac{1}{2}(p + 1)$ for all sufficiently large $p$.
Is it true that either $|A \cap [X]| \ll X^{1/2} / \log^{100} X$, or $A$ is contained in the
image of $\mathbb{Z}$ under a quadratic map $\phi : \mathbb{Q} \to \mathbb{Q}$?
-/
@[category research open, AMS 11]
theorem green_47 :
    answer(sorry) ↔ ∀ A : Set ℕ,
      (∀ᶠ p in atTop, Nat.Prime p → Set.ncard (Set.image (fun a : ℕ => (a : ZMod p)) A) ≤ (p + 1) / 2) →
      ((fun X : ℕ => ((A ∩ Set.Iic X).ncard : ℝ)) ≪ (fun X : ℕ => Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 100))
      ∨ (∃ P : Polynomial ℚ, P.degree = 2 ∧ ∀ a ∈ A, ∃ z : ℤ, (a : ℚ) = P.eval (z : ℚ)) := by
  sorry

end Green47
