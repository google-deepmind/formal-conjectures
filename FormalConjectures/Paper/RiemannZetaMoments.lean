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
import FormalConjecturesUtil

/-!
# Moments of the Riemann zeta function on the critical line

The moments $\frac{1}{T}\int_0^T |\zeta(1/2 + it)|^{2k}\,dt$ are conjectured to be asymptotic
to $c_k (\log T)^{k^2}$ for some constants $c_k$. This is a theorem for $k = 1$
(Hardy–Littlewood, $c_1 = 1$) and $k = 2$ (Ingham, $c_2 = 1/(2\pi^2)$), and these are the only
proven cases. Conrey–Ghosh and Conrey–Gonek conjectured $c_3 = 42 a_3 / 9!$ and
$c_4 = 24024 a_4 / 16!$, with $a_k$ the arithmetic factor
$a_k = \prod_p (1 - 1/p)^{k^2} \sum_{m \ge 0} \bigl(\Gamma(m+k)/(m!\,\Gamma(k))\bigr)^2 p^{-m}$;
Keating–Snaith conjectured $c_k = a_k f_k$ with $f_k = \prod_{j=0}^{k-1} j!/(j+k)!$ from random
matrix theory, recovering $g_k = (k^2)!\,f_k = 1, 2, 42, 24024$.

The statements and constants below are taken from §3.4.5 of [Co26].

*References:*
- [Co26] A. Connes, *The Riemann Hypothesis: Past, Present and a Letter Through Time*,
  [arXiv:2602.04022](https://arxiv.org/abs/2602.04022), §3.4.5.
- [In26] A. E. Ingham, *Mean-value theorems in the theory of the Riemann zeta-function*,
  Proc. London Math. Soc. 27 (1926), 273–300.
- [CG98] J. B. Conrey, A. Ghosh, *A conjecture for the sixth power moment of the Riemann
  zeta-function*, Internat. Math. Res. Notices 1998, no. 15, 775–780.
- [CGo01] J. B. Conrey, S. Gonek, *High moments of the Riemann zeta-function*, Duke Math. J.
  107 (2001), no. 3, 577–604.
- [KS00] J. P. Keating, N. C. Snaith, *Random matrix theory and $\zeta(1/2+it)$*, Commun. Math.
  Phys. 214 (2000), no. 1, 57–89.
-/

open Complex Filter Real
open scoped Asymptotics Nat

namespace riemannZeta

/-- The $k$th moment of the Riemann zeta function is the integral
$$
  \frac{1}{T}\int_0^T |\zeta(1/2 + it)|^{2k}dt.
$$
-/
noncomputable def moment (k : ℕ) (T : ℝ) : ℝ :=
  1/T * ∫ t in (0 : ℝ)..(T), ‖riemannZeta (1/2 + I * t)‖ ^ (2 * k)

/-- The asymptotic behaviour of the $k$th moment of the Riemann zeta function
is conjectured to be
$$
  \frac{1}{T}\int_0^T |\zeta(1/2 + it)|^{2k}dt \sim c_k \log(T)^{k^2},
$$
for some constant $c_k$.
-/
@[category research open, AMS 11]
theorem moments (k : ℕ) : ∃ c > (0 : ℝ),
    moment k ~[atTop] fun T ↦ c * T.log ^ (k ^ 2) := by
  sorry

/-- The asymptotic behaviour of the first moment of the Riemann zeta function was proved by
Hardy and Littlewood, where $c_1 = 1$ [Co26, §3.4.5]. -/
@[category research solved, AMS 11]
theorem moments₁ : moment 1 ~[atTop] fun T ↦ T.log := by
  sorry

/-- The asymptotic behaviour of the second moment of the Riemann zeta function was proved by
Ingham [In26], where $c_2 = 1/(2\pi^2)$. -/
@[category research solved, AMS 11]
theorem moments₂ : moment 2 ~[atTop] fun T ↦ (1 / (2 * π ^ 2)) * T.log ^ 4 := by
  sorry

/-- The arithmetic factor expected to appear in the asymptotic behaviour of the $k$th moment of the
Riemann zeta function, defined by
$$
  a_k = \prod_{p \text{ prime}} (1 - 1/p)^{k^2} \sum_{m=0}^{\infty} \left(\frac{\Gamma(m+k)}{m! \Gamma(k)}\right)^2 p^{-m}.
$$
-/
noncomputable def arithmeticFactor (k : ℕ) : ℝ :=
  ∏' p : Nat.Primes, (1 - 1 / p) ^ (k ^ 2) *
    ∑' m : ℕ, (Real.Gamma (m + k) / (m ! * Real.Gamma k)) ^ 2 / p ^ m

/-- The constant in the asymptotic formula for the 3rd zeta moment is conjectured
to be $42a_3/9!$ [CG98]. -/
@[category research open, AMS 11]
theorem moments₃ : moment 3 ~[atTop] fun T ↦ 42 * arithmeticFactor 3 / 9 ! * T.log ^ 9 := by
  sorry

/-- The constant in the asymptotic formula for the 4th zeta moment is conjectured to
be $24024a_4/16!$ [CGo01]. -/
@[category research open, AMS 11]
theorem moments₄ : moment 4 ~[atTop] fun T ↦ 24024 * arithmeticFactor 4 / 16 ! * T.log ^ 16 := by
  sorry

/-- The Keating–Snaith conjecture [KS00] for the $k$th moment of the Riemann zeta function,
provides the value of $c_k$ in the asymptotic formula [Co26, §3.4.5]. -/
@[category research open, AMS 11]
theorem momentsₖ (k : ℕ) : moment k ~[atTop]
    fun T ↦ (arithmeticFactor k * ∏ j ∈ Finset.range k, (j ! : ℝ) / (j + k) !) *
      T.log ^ (k ^ 2) := by
  sorry

end riemannZeta
