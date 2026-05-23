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
# Bugeaud Collection of Conjectures and Open Questions: Rapidly Increasing Sequences Dense Modulo One

*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [Fur67] Furstenberg, H. "Disjointness in ergodic theory, minimal sets, and a problem
    in diophantine approximation". Math. Systems Theory 1, 1–49 (1967).
  - [Mat80] de Mathan, Bernard. "Numbers contravening a condition in density modulo 1."
    Acta Mathematica Hungarica 36.3-4 (1980): 237-241.
  - [Pol79] Pollington, Andrew Douglas. "On the density of sequence $\{n_ {k}\xi\} $."
    Illinois Journal of Mathematics 23.4 (1979): 511-515.
-/

namespace Bugeaud

open Filter

/-- The **Pollington–de Mathan theorem**. For every lacunary sequence $(m_n)_{n \ge 1}$ of
positive integers, the set of real numbers $\xi$ for which $(\{\xi m_n\})_{n \ge 1}$ is
*not* dense modulo one has full Hausdorff dimension. -/
@[category research solved, AMS 11]
theorem pollington_de_mathan (m : ℕ → ℕ) (hm : ∀ n, 0 < m n) (hlac : IsLacunary m) :
    dimH {ξ : ℝ | ¬ Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ)))} = 1 := by
  sorry

/-- The Pollington–de Mathan theorem implies that a lacunary sequence cannot answer
Problem 10.6. -/
@[category test, AMS 11]
theorem problem_lacunary_not_dense_of_pollington_de_mathan
    (h : type_of% pollington_de_mathan) :
    ∃ m : ℕ → ℕ, (∀ n, 0 < m n) ∧ IsLacunary m ∧
      ¬ ∀ ξ : ℝ, Irrational ξ →
        Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) := by
  set m₀ : ℕ → ℕ := fun n => 2 ^ n with hm₀
  have hpos : ∀ n, 0 < m₀ n := by intro n; rw [hm₀]; positivity
  have hlac : IsLacunary m₀ := by
    refine ⟨3 / 2, by norm_num, .of_forall fun k => ?_⟩
    simp only [hm₀]
    push_cast
    rw [pow_succ]
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) k]
  refine ⟨m₀, hpos, hlac, fun hd => ?_⟩
  have hdim := h m₀ hpos hlac
  have hcount :
      {ξ : ℝ | ¬ Dense (Set.range fun n => (↑(ξ * m₀ n) : AddCircle (1 : ℝ)))}.Countable :=
    Set.Countable.mono (fun ξ hξ => by by_contra hξr; exact hξ (hd ξ hξr))
      (Set.countable_range _)
  rw [hcount.dimH_zero] at hdim
  exact zero_ne_one hdim

/-- **Furstenberg's theorem** (the $\times 2, \times 3$ case). For every irrational number
$\xi$, the two-parameter family $(\{\xi \, 2^m 3^n\})_{m, n \ge 1}$ is dense modulo one. -/
@[category research solved, AMS 11]
theorem furstenberg_two_three (ξ : ℝ) (hξ : Irrational ξ) :
    Dense {x : AddCircle (1 : ℝ) |
      ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ x = ↑(ξ * (2 ^ m * 3 ^ n : ℕ))} := by
  sorry

/--
Problem 10.6. Find a very rapidly increasing sequence $(m_n)_{n \ge 1}$ of positive
integers such that $(\{\xi m_n\})_{n \ge 1}$ is dense modulo one for every irrational
number $\xi$. Note: Furstenberg's $2^m3^n$ is sublacunary but requires two parameters.
Here "very rapidly increasing" is read as sublacunary with super-polynomial growth. -/
@[category research open, AMS 11]
theorem problem_10_6 :
    ∃ m : ℕ → ℕ,
    StrictMono m ∧
    IsSublacunary m ∧
    (∀ k : ℕ, ∀ᶠ (n : ℕ) in Filter.atTop, (n : ℝ) ^ k ≤ (m n : ℝ)) ∧
    ∀ ξ : ℝ, Irrational ξ →
      Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) := by
  sorry

end Bugeaud
