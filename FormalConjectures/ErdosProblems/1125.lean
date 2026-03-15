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
# Erdős Problem 1125

*Reference:* [erdosproblems.com/1125](https://www.erdosproblems.com/1125)

If $f : \mathbb{R} \to \mathbb{R}$ satisfies $2f(x) \leq f(x+h) + f(x+2h)$ for every $x \in \mathbb{R}$
and $h > 0$, must $f$ be monotonic?

[Ke69] Kemperman, J.H.B., _On the regularity of generalized convex functions_.
Trans. Amer. Math. Soc. (1969), 69-93.

[Er81b] Erdős, P., _My Scottish Book 'Problems'_. The Scottish Book (1981), 27-35.

[La84] Laczkovich, M., _On Kemperman's inequality 2f(x)≤f(x+h)+f(x+2h)_.
Colloq. Math. (1984), 109-115.
-/

namespace Erdos1125

/--
Let $f : \mathbb{R} \to \mathbb{R}$ be such that $2f(x) \leq f(x+h) + f(x+2h)$ for every
$x \in \mathbb{R}$ and $h > 0$. Then $f$ must be monotonic.

A problem of Kemperman [Ke69], who proved it is true if $f$ is measurable.
Laczkovich [La84] solved it in the affirmative.
-/
@[category research solved, AMS 26]
theorem erdos_1125 :
    ∀ f : ℝ → ℝ,
    (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    Monotone f ∨ Antitone f := by
  sorry

end Erdos1125
