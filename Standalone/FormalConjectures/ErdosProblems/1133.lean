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

import Mathlib

/-!
# Erdős Problem 1133

*References:*
- [erdosproblems.com/1133](https://www.erdosproblems.com/1133)
- [Er67] Erdős, P., Problems and results on the convergence and divergence properties of the
  Lagrange interpolation polynomials and some extremal problems. Mathematica (Cluj) (1967), 65-73.
-/

open Filter Set

namespace Erdos1133

/--
Let $C>0$. There exists $\epsilon>0$ such that if $n$ is sufficiently large the following holds.

For any $x_1,\ldots,x_n\in [-1,1]$ there exist $y_1,\ldots,y_n\in [-1,1]$ such that, if $P$ is a
polynomial of degree $m<(1+\epsilon)n$ with $P(x_i)=y_i$ for at least $(1-\epsilon)n$ many
$1\leq i\leq n$, then \[\max_{x\in [-1,1]}\lvert P(x)\rvert >C.\]
-/
theorem erdos_1133 :
    True ↔
    ∀ C > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ x : Fin n → Icc (-1 : ℝ) 1,
        ∃ y : Fin n → Icc (-1 : ℝ) 1,
          ∀ P : Polynomial ℝ,
            (P.natDegree : ℝ) < (1 + ε) * (n : ℝ) →
            ((Finset.univ.filter (fun i ↦ P.eval (x i : ℝ) = (y i : ℝ))).card : ℝ) ≥
              (1 - ε) * (n : ℝ) →
            ∃ z ∈ Icc (-1 : ℝ) 1, |P.eval z| > C := by
  sorry

/--
Erdős proved that, for any $C>0$, there exists $\epsilon>0$ such that if $n$ is sufficiently
large and $m=\lfloor (1+\epsilon)n\rfloor$ then for any $x_1,\ldots,x_m\in [-1,1]$ there is a
polynomial $P$ of degree $n$ such that $\lvert P(x_i)\rvert\leq 1$ for $1\leq i\leq m$ and
$\max_{x\in [-1,1]}\lvert P(x)\rvert>C$. The conjectured statement would also imply this, but
Erdős in [Er67] says he could not even prove it for $m=n$.
-/
theorem erdos_1133.variants.weaker :
    ∀ C > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      let m := ⌊(1 + ε) * (n : ℝ)⌋₊;
      ∀ x : Fin m → Icc (-1 : ℝ) 1,
        ∃ P : Polynomial ℝ,
          P.natDegree = n ∧
          (∀ i : Fin m, |P.eval (x i : ℝ)| ≤ 1) ∧
          ∃ z ∈ Icc (-1 : ℝ) 1, |P.eval z| > C := by
  sorry

end Erdos1133
