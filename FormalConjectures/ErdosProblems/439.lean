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
# Erdős Problem 439

*Reference:* [erdosproblems.com/439](https://www.erdosproblems.com/439)

Is it true that, in any finite colouring of the integers, there must be two
integers $x \ne y$ of the same colour such that $x + y$ is a square? What about
a $k$-th power?

A question of Roth, Erdős, Sárközy, and Sós. Erdős, Sárközy, and Sós proved
this for 2 or 3 colours.

This was proved by Khalfalah and Szemerédi [KhSz06], who showed the general
result with $x + y = z^2$ replaced by $x + y = f(z)$ for any non-constant
$f(z) \in \mathbb{Z}[z]$ such that $2 \mid f(z)$ for some $z \in \mathbb{Z}$.
Since $k$-th powers include even values (take $z$ even), the $k$-th power case
follows.

[KhSz06] Khalfalah, A. and Szemerédi, E., _On the number of monochromatic
solutions of $x + y = z^2$_. Combinatorics, Probability and Computing (2006),
15(1-2), 213-227.
-/

namespace Erdos439

/-- Erdős Problem 439, square case:
In any finite colouring of the natural numbers, there exist distinct $x$ and $y$
of the same colour such that $x + y$ is a perfect square.

Proved by Khalfalah and Szemerédi [KhSz06]. -/
@[category research solved, AMS 5 11]
theorem erdos_439 : answer(True) ↔
    ∀ (c : ℕ) (f : ℕ → Fin c), ∃ x y : ℕ, x ≠ y ∧ f x = f y ∧ IsSquare (x + y) := by
  sorry

/-- Erdős Problem 439, $k$-th power generalization:
In any finite colouring of the natural numbers, there exist distinct $x$ and $y$
of the same colour such that $x + y$ is a perfect $k$-th power (i.e., $z^k$ for
some $z$).

Also follows from the result of Khalfalah and Szemerédi [KhSz06]. -/
@[category research solved, AMS 5 11]
theorem erdos_439.variants.kth_powers : answer(True) ↔
    ∀ (k : ℕ), 2 ≤ k → ∀ (c : ℕ) (f : ℕ → Fin c),
      ∃ x y : ℕ, x ≠ y ∧ f x = f y ∧ ∃ z : ℕ, z ^ k = x + y := by
  sorry

end Erdos439
