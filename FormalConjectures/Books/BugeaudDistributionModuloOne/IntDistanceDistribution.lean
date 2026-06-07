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
import FormalConjecturesForMathlib.Data.Real.NearestInt
/-!
# Bugeaud Collection of Conjectures and Open Questions: Fractional Parts of Powers

Chapter 10 of the book collects open questions. This file formalizes Problems 10.1,
10.2, 10.3 and the unnumbered conjecture by Waldschmidt.

*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [Har19] Hardy, Gr H. "A problem of Diophantine approximation."
    J. Indian Math. Soc 11 (1919): 162-166.
  - [Kok45] Koksma, J. F. "Sur la théorie métrique des approximations diophantiques."
    Indag. Math 7 (1945): 54-70.
  - [Mah53] Mahler, Kurt. "On the approximation of logarithms of algebraic numbers."
    Philosophical Transactions of the Royal Society of London. Series A,
    Mathematical and Physical Sciences 245.898 (1953): 371-398.
  - [Wal03](http://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/Cetraro.pdf)
    Waldschmidt, Michel. "Linear independence measures for logarithms of algebraic numbers."
    Diophantine Approximation: Lectures given at the CIME Summer School held in Cetraro, Italy,
    June 28–July 6, 2000. Berlin, Heidelberg: Springer Berlin Heidelberg, 2003. 249-344.
-/

namespace Bugeaud

/--
Problem 10.1. Are there a transcendental number $\alpha$ and a positive real
number $\xi$ such that $\lVert \xi \alpha^n \rVert$ tends to~$0$ as~$n$ tends to infinity? [Har19]
(Trivial for $|\alpha| < 1$)
-/
@[category research open, AMS 11]
theorem problem_10_1 : answer(sorry) ↔
    ∃ (α ξ : ℝ), 1 < |α| ∧ Transcendental ℚ α ∧ 0 < ξ ∧
      Filter.Tendsto (fun n : ℕ ↦ distToNearestInt (ξ * α ^ n)) Filter.atTop (nhds 0) := by
  sorry

/--
Problem 10.2. To prove that $\lVert e^n \rVert$ does not tend to 0 as n tends to
infinity.
-/
@[category research open, AMS 11]
theorem problem_10_2 :
    ¬ Filter.Tendsto (fun n : ℕ ↦ distToNearestInt (Real.exp n)) Filter.atTop (nhds 0) := by
  sorry

/--
Problem 10.3. To prove that there exists a positive real number~$c$ such
that $\lVert e^n \rVert > e^{−cn}$, for every~$n \ge 1$. Posed by Mahler [Mah53].
-/
@[category research open, AMS 11]
theorem problem_10_3 :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → Real.exp (-c * n) < distToNearestInt (Real.exp n) := by
  sorry

/--
Waldschmidt [Wal03] conjectured that a stronger result holds, namely
that there exists a positive real number~$c$ such that $\lVert e^n \rVert > n^{−c}$ for
every~$n \ge 1$. This is supported by metrical results [Kok45].
-/
@[category research open, AMS 11]
theorem waldschmidt :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ (-c) < distToNearestInt (Real.exp n) := by
  sorry

/--
Waldschmidt's conjecture is stronger than Mahler's: since $\log n \le n$ for $n \ge 1$,
the polynomial lower bound $n^{-c}$ dominates the exponential lower bound $e^{-cn}$.
-/
@[category test, AMS 11]
theorem problem_10_3_of_waldschmidt (h : type_of% waldschmidt) : type_of% problem_10_3 := by
  obtain ⟨c, hc, hyp⟩ := h
  refine ⟨c, hc, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  refine lt_of_le_of_lt ?_ (hyp n hn)
  rw [Real.rpow_def_of_pos hn_pos]
  exact Real.exp_le_exp.mpr (by nlinarith [Real.log_le_self hn_pos.le])

end Bugeaud
