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
module

public import FormalConjecturesUtil

/-!
# Asymptotically minimal maxima of real Littlewood polynomials

*Reference:* OpenAI, *Asymptotically minimal maxima of real Littlewood polynomials*
(2026), Theorem 1.1.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Asymptotically-minimal-maxima-of-real-Littlewood-polynomials-September-23-2026/paper.pdf
-/

@[expose] public section

namespace AsymptoticallyMinimalLittlewood

/-- For every $\eta > 0$ and every sufficiently large length $N$, there is a real-sign
Littlewood polynomial whose modulus on the unit circle is at most
$(1+\eta)\sqrt N$. The assertion covers every large integer length. -/
@[category research solved, AMS 30 42]
theorem asymptotically_minimal_maximum :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∃ ε : Fin N → ℝ, (∀ k, ε k = -1 ∨ ε k = 1) ∧
        ∀ z : ℂ, ‖z‖ = 1 →
          ‖∑ k : Fin N, (ε k : ℂ) * z ^ (k : ℕ)‖ ≤ (1 + η) * Real.sqrt N := by
  sorry

end AsymptoticallyMinimalLittlewood
