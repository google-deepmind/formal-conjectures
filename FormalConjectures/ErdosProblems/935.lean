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
# Erdős Problem 935

*References:*
- [erdosproblems.com/935](https://www.erdosproblems.com/935)
- [Er76d] Erdős, P., *Problems and results on number theoretic properties of consecutive integers
  and related questions*. Proceedings of the Fifth Manitoba Conference on Numerical Mathematics
  (Univ. Manitoba, Winnipeg, Man., 1975) (1976), 25-44.
- [Fe26] T. Feng et al, *Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on the
  Erdős Problems*. arXiv:2601.22401 (2026).
- [OEIS A057521](https://oeis.org/A057521)
-/

open Filter Finset
open scoped Topology

namespace Erdos935

/--
For $n = \prod p^{k_p}$, the powerful part is
$Q_2(n) = \prod_{k_p \ge 2} p^{k_p}$.
-/
def powerfulPart (n : ℕ) : ℕ :=
  ∏ p ∈ n.factorization.support with 2 ≤ n.factorization p, p ^ n.factorization p

/-- $Q_2(12) = 4$, since $12 = 2^2 \cdot 3$. -/
@[category test, AMS 11]
theorem powerfulPart_twelve : powerfulPart 12 = 4 := by native_decide

/-- $Q_2(18) = 9$, since $18 = 2 \cdot 3^2$. -/
@[category test, AMS 11]
theorem powerfulPart_eighteen : powerfulPart 18 = 9 := by native_decide

/-- $Q_2(8) = 8$, since $8 = 2^3$. -/
@[category test, AMS 11]
theorem powerfulPart_eight : powerfulPart 8 = 8 := by native_decide

/-- $Q_2(6) = 1$, since $6 = 2 \cdot 3$ is squarefree. -/
@[category test, AMS 11]
theorem powerfulPart_six : powerfulPart 6 = 1 := by native_decide

/--
Is it true that, for every $\epsilon > 0$ and $\ell \geq 1$, if $n$ is sufficiently large then
$Q_2(n(n+1)\cdots(n+\ell)) < n^{2+\epsilon}$?
-/
@[category research open, AMS 11]
theorem erdos_935.parts.i : answer(sorry) ↔ ∀ ε > (0 : ℝ), ∀ ℓ ≥ 1, ∀ᶠ n in atTop,
    (powerfulPart (∏ i ∈ Icc n (n + ℓ), i) : ℝ) < (n : ℝ) ^ ((2 : ℝ) + ε) := by
  sorry

/--
If $\ell \geq 2$, is
$\limsup_{n \to \infty} Q_2(n(n+1)\cdots(n+\ell)) / n^2$
infinite?

The second part is essentially the same (up to constants) as
[erdosproblems.com/367](https://www.erdosproblems.com/367). van Doorn's construction there
(also given by Aletheia [Fe26]), via solutions of the Pell equation $x^2 - 8y^2 = 1$, proves
this in the affirmative even for $\ell = 2$.
-/
@[category research solved, AMS 11]
theorem erdos_935.parts.ii : answer(True) ↔ ∀ ℓ ≥ 2,
    atTop.limsup (fun n ↦
      ((powerfulPart (∏ i ∈ Icc n (n + ℓ), i) : ℝ) / (n : ℝ) ^ 2).toEReal) = ⊤ := by
  sorry

/--
If $\ell \geq 2$, is
$\lim_{n \to \infty} Q_2(n(n+1)\cdots(n+\ell)) / n^{\ell+1} = 0$?

Aletheia [Fe26] notes that the ABC conjecture implies a positive answer.
-/
@[category research open, AMS 11]
theorem erdos_935.parts.iii : answer(sorry) ↔ ∀ ℓ ≥ 2,
    Tendsto (fun n ↦ (powerfulPart (∏ i ∈ Icc n (n + ℓ), i) : ℝ) / (n : ℝ) ^ (ℓ + 1))
      atTop (𝓝 0) := by
  sorry

/--
A result of Mahler implies that, for every $\ell \geq 1$,
$\limsup_{n \to \infty} Q_2(n(n+1)\cdots(n+\ell)) / n^2 \geq 1$.
-/
@[category research solved, AMS 11]
theorem erdos_935.variants.mahler : ∀ ℓ ≥ 1,
    1 ≤ atTop.limsup (fun n ↦
      ((powerfulPart (∏ i ∈ Icc n (n + ℓ), i) : ℝ) / (n : ℝ) ^ 2).toEReal) := by
  sorry

end Erdos935
