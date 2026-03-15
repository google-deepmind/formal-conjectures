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
# Erdős Problem 226

Is there an entire non-linear function $f$ such that, for all $x \in \mathbb{R}$, $x$ is
rational if and only if $f(x)$ is?

*Reference:* [erdosproblems.com/226](https://www.erdosproblems.com/226)

[Er57] Erdős, P., _Some unsolved problems_, 1957.

[BaSc70] Barth, K.F. and Schneider, W.J., _Entire functions mapping countable dense subsets
of the reals onto each other monotonically_, J. London Math. Soc. (2) 2 (1970), 620–626.

[BaSc71] Barth, K.F. and Schneider, W.J., _Entire functions mapping arbitrary countable
dense sets and their complements onto each other_, J. London Math. Soc. (2) 4 (1971),
482–488.

[Ha74] Hayman, W. K., _Research problems in function theory: new problems_ (1974), 155–180.
-/

namespace Erdos226

/--
Erdős Problem #226 [Er57] — SOLVED

Is there an entire non-linear function $f$ such that, for all $x \in \mathbb{R}$, $x$ is
rational if and only if $f(x)$ is?

Solved by Barth and Schneider [BaSc70], who proved that if $A, B \subset \mathbb{R}$ are
countable dense sets then there exists a transcendental entire function $f$ such that
$f(z) \in B$ if and only if $z \in A$. In [BaSc71] they proved the same result for
countable dense subsets of $\mathbb{C}$.
-/
@[category research solved, AMS 30]
theorem erdos_226 : answer(True) ↔
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      (¬∃ a b : ℂ, ∀ z, f z = a * z + b) ∧
      (∀ x : ℝ, (∃ q : ℚ, (q : ℝ) = x) ↔ ∃ q : ℚ, (q : ℂ) = f ↑x) := by
  sorry

/--
Erdős Problem #226 (general variant) [BaSc70]

If $A, B \subseteq \mathbb{R}$ are two countable dense sets, does there exist an entire function
such that $f(A) = B$? Barth and Schneider [BaSc70] proved that such an entire function exists
and can be chosen to be transcendental. The main problem `erdos_226` is the special case
$A = B = \mathbb{Q}$.
-/
@[category research solved, AMS 30]
theorem erdos_226_general (A B : Set ℝ) (hA : A.Countable) (hB : B.Countable)
    (hAd : Dense A) (hBd : Dense B) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      (¬∃ a b : ℂ, ∀ z, f z = a * z + b) ∧
      (∀ x : ℝ, x ∈ A ↔ f ↑x ∈ ((↑) : ℝ → ℂ) '' B) := by
  sorry

end Erdos226
