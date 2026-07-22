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
# Erdős Problem 115

*References:*
- [erdosproblems.com/115](https://www.erdosproblems.com/115)
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [Er90] Erdős, Paul, *Some of my favourite unsolved problems*. A tribute to Paul Erdős (1990),
  467-478.
- [ErLe94] Erëmenko, A. and Lempert, L., *An extremal problem for polynomials*. Proc. Amer. Math.
  Soc. (1994), 191-193.
- [Po59a] Pommerenke, Ch., *On the derivative of a polynomial*. Michigan Math. J. (1959), 373-375.
-/

open Filter

namespace Erdos115

/--
If $p(z)$ is a polynomial of degree $n$ such that $\{z : \lvert p(z)\rvert\leq 1\}$ is connected
then is it true that
\[\max_{\substack{z\in\mathbb{C}\\ \lvert p(z)\rvert\leq 1}} \lvert p'(z)\rvert
\leq (\tfrac{1}{2}+o(1))n^2?\]

Eremenko and Lempert [ErLe94] have shown this is true, and in fact Chebyshev polynomials are the
extreme examples.
-/
@[category research solved, AMS 30]
theorem erdos_115 : answer(True) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
      IsConnected {z : ℂ | ‖p.eval z‖ ≤ 1} → ∀ z : ℂ, ‖p.eval z‖ ≤ 1 →
        ‖p.derivative.eval z‖ ≤ (1 / 2 + ε) * (n : ℝ) ^ 2 := by
  sorry

end Erdos115
