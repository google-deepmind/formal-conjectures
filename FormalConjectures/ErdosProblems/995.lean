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
# Erdős Problem 995

*Reference:* [erdosproblems.com/995](https://www.erdosproblems.com/995)

[Er49d] Erdős, P. (1949) — constructed a lacunary sequence and $f \in L^2([0,1])$ such that, for
every $\varepsilon > 0$, for almost all $\alpha$,
$\limsup_{N \to \infty} \frac{1}{N(\log \log N)^{1/2 - \varepsilon}} \sum_{k \leq N}
f(\{\alpha n_k\}) = \infty$.

[Er64b] Erdős, P. (1964) — thought that his lower bound was closer to the truth.
-/

open MeasureTheory Filter Finset Set

namespace Erdos995

/-- A sequence of positive integers is lacunary if it is strictly increasing
and there exists $q > 1$ such that $n_{k+1} \geq q \cdot n_k$ for all $k$. -/
def IsLacunary (n : ℕ → ℕ) : Prop :=
  StrictMono n ∧ ∃ q : ℝ, q > 1 ∧ ∀ k : ℕ, (n k : ℝ) * q ≤ n (k + 1)

/--
Erdős Problem 995 [Er64b]:

Is it true that for every lacunary sequence $(n_k)$ of positive integers and every
$f \in L^2([0,1])$, for almost all $\alpha \in [0,1]$,
$$\sum_{k < N} f(\{\alpha \cdot n_k\}) = o(N \cdot \sqrt{\log \log N})?$$

Formulated as: for every $\varepsilon > 0$, for almost all $\alpha$, eventually (for large $N$),
$\left|\sum_{k < N} f(\{\alpha \cdot n_k\})\right| \leq \varepsilon \cdot N \cdot
\sqrt{\log \log N}$.
-/
@[category research open, AMS 11 42]
theorem erdos_995 : answer(sorry) ↔
    ∀ (n : ℕ → ℕ), IsLacunary n →
    ∀ (f : ℝ → ℝ), Measurable f →
    Integrable (fun x => f x ^ 2) (volume.restrict (Icc (0 : ℝ) 1)) →
    ∀ ε : ℝ, ε > 0 →
    ∀ᵐ α ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        |∑ k ∈ Finset.range N, f (Int.fract (α * (n k : ℝ)))| ≤
          ε * (N : ℝ) * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  sorry

end Erdos995
