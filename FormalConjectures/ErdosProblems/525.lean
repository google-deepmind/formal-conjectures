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
# Erdős Problem 525

Is it true that almost all $\pm 1$-coefficient polynomials of degree $n$ attain modulus less
than $1$ somewhere on the unit circle?

*Reference:* [erdosproblems.com/525](https://www.erdosproblems.com/525)

[Er61] Erdős, P., _Some unsolved problems_, Magyar Tud. Akad. Mat. Kutató Int. Közl. 6 (1961),
221-254.

[Li66] Littlewood, J. E., _On polynomials ∑ⁿ±zᵐ, ∑ⁿeᵃᵐⁱzᵐ, z=eᶿⁱ_, J. London Math. Soc.
(1966), 367-376.

[Ka87] Kashin, B. S., _The properties of random trigonometric polynomials with ±1 coefficients_,
Vestnik Moskov. Univ. Ser. I Mat. Mekh. (1987), 40-46, 105.

[Ko94] Konyagin, S. V., _On the minimum modulus of random trigonometric polynomials with
coefficients ±1_, Mat. Zametki (1994), 80-101, 158.

[KoSc99] Konyagin, S. V., Schlag, W., _Lower bounds for the absolute value of random polynomials
on a neighborhood of the unit circle_, Trans. Amer. Math. Soc. (1999), 4963-4980.

[CoNg21] Cook, N. A., Nguyen, H. H., _Universality of the minimum modulus for random
trigonometric polynomials_, Discrete Analysis (2021), Paper No. 20, 46.
-/

open Finset BigOperators Filter Classical

namespace Erdos525

/-- Evaluate a $\pm 1$-coefficient polynomial of degree $n$ at $z \in \mathbb{C}$.
The sign vector $\varepsilon : \operatorname{Fin}(n+1) \to \operatorname{Bool}$ determines
coefficients ($\mathrm{true} \to +1$, $\mathrm{false} \to -1$):
$f(z) = \sum_{k=0}^{n} \varepsilon_k \cdot z^k$. -/
noncomputable def littlewoodEval (n : ℕ) (ε : Fin (n + 1) → Bool) (z : ℂ) : ℂ :=
  ∑ k : Fin (n + 1), (if ε k then (1 : ℂ) else (-1 : ℂ)) * z ^ (k : ℕ)

/-- A $\pm 1$-coefficient polynomial of degree $n$ has modulus less than $1$
somewhere on the unit circle. -/
def hasSmallValueOnCircle (n : ℕ) (ε : Fin (n + 1) → Bool) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ ‖littlewoodEval n ε z‖ < 1

/-- The number of $\pm 1$-coefficient polynomials of degree $n$ that do NOT attain
modulus less than $1$ anywhere on the unit circle. -/
noncomputable def countNoSmallValue (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun ε : Fin (n + 1) → Bool =>
    ¬hasSmallValueOnCircle n ε)).card

/--
Erdős Problem 525 [Er61, p.253]:

Is it true that all except at most $o(2^n)$ many degree $n$ polynomials with
$\pm 1$-valued coefficients $f(z)$ have $|f(z)| < 1$ for some $|z| = 1$?

Equivalently, the number of sign vectors $\varepsilon \in \{\pm 1\}^{n+1}$ for which
the polynomial $f(z) = \sum \varepsilon_k z^k$ satisfies $\min_{|z|=1} |f(z)| \geq 1$
is $o(2^n)$ as $n \to \infty$.

Proved by Kashin (1987). Konyagin (1994) showed
$\min_{|z|=1} |f(z)| \leq n^{-1/2+o(1)}$ for almost all such polynomials.
Cook and Nguyen (2021) identified the limiting distribution.
-/
@[category research solved, AMS 42]
theorem erdos_525 :
    answer(True) ↔
      Tendsto (fun n => (countNoSmallValue n : ℝ) / (2 : ℝ) ^ n) atTop (nhds 0) := by
  sorry

end Erdos525
