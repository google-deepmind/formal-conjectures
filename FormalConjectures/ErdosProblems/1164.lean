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
# Erdős Problem 1164

*Reference:* [erdosproblems.com/1164](https://www.erdosproblems.com/1164)

Let $S_n$ denote a simple random walk on $\mathbb{Z}^2$ starting at the origin, and let $R_n$
be the largest integer such that the walk visits every lattice point within distance $R_n$ of the
origin in its first $n$ steps. Is it true that $\log R_n \asymp \sqrt{\log n}$ almost surely?

[Va99] Vershik, A., *Random walks on random and changing graphs*, 1999, Problem 6.76.

[Re90] Révész, P., *Random Walk in Random and Non-Random Environments*, World Scientific, 1990.

[DPRZ04] Dembo, A., Peres, Y., Rosen, J. and Zeitouni, O., *Cover times for Brownian motion
and random walks in two dimensions*, Annals of Mathematics, 2004.
-/

open MeasureTheory ProbabilityTheory Filter Finset BigOperators

namespace Erdos1164

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A step distribution for a simple random walk on $\mathbb{Z}^2$: the random variable takes
values in $\{(1,0), (-1,0), (0,1), (0,-1)\}$ each with equal probability. -/
def IsUniformStep (μ : Measure Ω) (X : Ω → ℤ × ℤ) : Prop :=
  (∀ ω, X ω ∈ ({((1 : ℤ), 0), (-1, 0), (0, 1), (0, -1)} : Set (ℤ × ℤ))) ∧
  μ {ω | X ω = (1, 0)} = μ {ω | X ω = (-1, 0)} ∧
  μ {ω | X ω = (-1, 0)} = μ {ω | X ω = (0, 1)} ∧
  μ {ω | X ω = (0, 1)} = μ {ω | X ω = (0, -1)}

/-- Position of the random walk at time $n$: $S_n = X_0 + X_1 + \cdots + X_{n-1}$,
starting at the origin $S_0 = (0, 0)$. -/
def walkPosition (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) : ℤ × ℤ :=
  ∑ i ∈ Finset.range n, X i ω

/-- The covering radius $R_n(\omega)$: the largest $R \in \mathbb{N}$ such that every lattice
point $(a, b) \in \mathbb{Z}^2$ with $a^2 + b^2 \le R^2$ is visited by the walk within its
first $n$ steps. -/
noncomputable def coveringRadius (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) : ℕ :=
  sSup {R : ℕ | ∀ (a b : ℤ), a ^ 2 + b ^ 2 ≤ ↑R ^ 2 →
    ∃ k, k ≤ n ∧ walkPosition X ω k = (a, b)}

/--
Erdős Problem 1164 (Erdős–Taylor) [Va99, 6.76]:

Let $R_n$ be the maximal integer such that almost every random walk from the origin
in $\mathbb{Z}^2$ visits every $x \in \mathbb{Z}^2$ with $\|x\| \le R_n$ in at most $n$ steps.
Is it true that $\log R_n \asymp \sqrt{\log n}$?

That is, there exist constants $c_1, c_2 > 0$ such that almost surely, for all
sufficiently large $n$:
$$c_1 \cdot \sqrt{\log n} \le \log R_n \le c_2 \cdot \sqrt{\log n}.$$

Proved independently by Révész [Re90] and Kesten. The stronger conjecture
$$\lim P((\log R_n)^2 / \log n \le x) = e^{-4x} \quad \text{for all } x > 0$$
was proved by Dembo, Peres, Rosen, and Zeitouni [DPRZ04].
-/
@[category research solved, AMS 60]
theorem erdos_1164 : answer(True) ↔
    ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → ℤ × ℤ),
      (∀ i, IsUniformStep μ (X i)) → iIndepFun X μ →
        ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
          ∀ᵐ ω ∂μ, ∀ᶠ (n : ℕ) in atTop,
            c₁ * Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (coveringRadius X ω n : ℝ) ∧
            Real.log (coveringRadius X ω n : ℝ) ≤ c₂ * Real.sqrt (Real.log (n : ℝ)) := by
  sorry

end Erdos1164
