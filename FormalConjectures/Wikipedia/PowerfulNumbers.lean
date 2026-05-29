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
# Asymptotic Density of Powerful Numbers

Bateman–Grosswald (1958) refined the Erdős–Szekeres (1934) asymptotic for the
counting function $Q(x) = \#\{n \leq x : n \text{ is powerful}\}$.

*References:*
- [Wikipedia: Powerful number](https://en.wikipedia.org/wiki/Powerful_number)
- [OEIS A001694](https://oeis.org/A001694)
- Bateman, P.T. and Grosswald, E., *On a theorem of Erdős and Szekeres*.
  Illinois J. Math. (1958), 88–98.
-/

namespace PowerfulNumber

open Filter Asymptotics

/-- The counting function $Q(x) = \#\{n \leq x : n \text{ is powerful}\}$. -/
noncomputable def powerfulCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter Nat.Powerful).card

/--
**Asymptotic density of powerful numbers (Bateman–Grosswald, 1958)**:
there exists a positive constant $c$ such that
$$Q(x) = c \cdot x^{1/2} + o(x^{1/2}).$$

The leading constant is $c = \zeta(3/2) / \zeta(3) \approx 2.1733$. The full
Bateman–Grosswald expansion is
$$Q(x) = \frac{\zeta(3/2)}{\zeta(3)} x^{1/2}
       + \frac{\zeta(2/3)}{\zeta(2)} x^{1/3} + O(x^{1/6}).$$

Note: the formula $\zeta(1/2)^{-1} \approx 0.3039$ occasionally cited is incorrect
($\zeta(1/2) \approx -1.46$, so its reciprocal is negative).
-/
@[category research open, AMS 11]
theorem powerful_asymptotic :
    (∃ c : ℝ, 0 < c ∧
      (fun (x : ℕ) ↦ ((powerfulCount x : ℝ) - c * (x : ℝ) ^ ((1 : ℝ) / 2)))
        =o[atTop] (fun (x : ℕ) ↦ (x : ℝ) ^ ((1 : ℝ) / 2))) ↔ answer(sorry) := by
  sorry

end PowerfulNumber