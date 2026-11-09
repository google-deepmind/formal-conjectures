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
public import FormalConjectures.Millennium.RiemannHypothesis

/-!
# Landau–Siegel zeros

A Landau–Siegel zero (or exceptional zero) is a real zero $\beta$ of the Dirichlet
$L$-function of a real primitive character modulo $q$ that lies unusually close to $1$, namely
$1 - \beta = o(1 / \log q)$. The conjecture asserts that such zeros do not exist.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Siegel_zero)
- [Si35] C. L. Siegel, *Über die Classenzahl quadratischer Zahlkörper*, Acta Arith. 1 (1935),
  83–86.
- [OAI26] OpenAI, *Uniform exclusion of Landau–Siegel zeros*. OpenAI Math Release preprint
  (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026/paper.pdf
-/

@[expose] public section

namespace SiegelZero

/--
**There are no Landau–Siegel zeros.** There is an absolute constant $c > 0$ such that for every
modulus $q \ge 3$, every real primitive Dirichlet character $\chi \ne 1$ modulo $q$ and every
real zero $\beta \in (0, 1)$ of $L(s, \chi)$, we have $\beta \le 1 - c / \log q$.

This was proved by an internal OpenAI model in October 2026 [OAI26]; see OpenAI's Lean proof.
The statement is written as $c \le (1 - \beta) \log q$, as in that proof.
-/
@[category research solved, AMS 11]
theorem no_siegel_zeros :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
          c ≤ (1 - β) * Real.log (q : ℝ) := by
  sorry

/--
**Siegel's theorem** [Si35]. For every $\varepsilon > 0$ there is $c(\varepsilon) > 0$ such that
every real zero $\beta \in (0, 1)$ of $L(s, \chi)$, for a real primitive character $\chi \ne 1$
modulo $q \ge 3$, satisfies $\beta \le 1 - c(\varepsilon) q^{-\varepsilon}$. The constant
$c(\varepsilon)$ is ineffective.
-/
@[category research solved, AMS 11]
theorem siegel_theorem :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
          c * (q : ℝ) ^ (-ε) ≤ 1 - β := by
  sorry

/-- The generalized Riemann hypothesis rules out Landau–Siegel zeros, with $c = \log 3 / 2$. -/
@[category test, AMS 11]
theorem no_siegel_zeros_of_grh (h : type_of% @GRH.generalized_riemann_hypothesis) :
    type_of% no_siegel_zeros := by
  refine ⟨Real.log 3 / 2, by positivity, fun q _ hq χ hχ _ _ β hβ₀ hβ₁ hβ => ?_⟩
  have hre : ((β : ℂ)).re = 1 / 2 := by
    refine h q χ hχ β hβ ?_
    rintro ⟨n, -, hn⟩
    have hn' : (n : ℝ) = β := by exact_mod_cast hn
    have h₀ : (0 : ℤ) < n := by exact_mod_cast hn' ▸ hβ₀
    have h₁ : n < (1 : ℤ) := by exact_mod_cast hn' ▸ hβ₁
    omega
  rw [Complex.ofReal_re] at hre
  rw [hre]
  have : Real.log 3 ≤ Real.log q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  linarith

end SiegelZero
