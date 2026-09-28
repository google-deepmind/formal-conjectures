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
# Erdős Problem 995

*References:*
- [erdosproblems.com/995](https://www.erdosproblems.com/995)
- [Er49] Erdős, P., On the strong law of large numbers, Trans. Amer. Math. Soc. (1949),
  329-334.

Let $n_1 < n_2 < \cdots$ be a lacunary sequence of integers and $f \in L^2([0,1])$ with
$\int_0^1 f = 0$. Estimate the growth of
$$S_N(\alpha) = \sum_{k \le N} f(\{\alpha n_k\})$$
for almost all $\alpha$, where $\{\cdot\}$ denotes the fractional part. In particular, is it
true that $S_N(\alpha) = o\!\left(N \sqrt{\log\log N}\right)$ for almost all $\alpha$?

Erdős [Er49] constructed a lacunary sequence and a mean-zero $f \in L^2([0,1])$ for which, for
every $\varepsilon > 0$, $\limsup_N S_N(\alpha) / (N (\log\log N)^{1/2 - \varepsilon}) = \infty$
for almost all $\alpha$, and believed this lower bound to be close to the truth.

The mean-zero hypothesis $\int_0^1 f = 0$ is the natural normalisation: otherwise the sum has a
linear main term coming from the average of $f$.
-/

open MeasureTheory Filter Asymptotics Set

namespace Erdos995

/-- The partial sum $S_N(\alpha) = \sum_{k < N} f(\{\alpha n_k\})$. -/
noncomputable def partialSum (n : ℕ → ℕ) (f : ℝ → ℝ) (α : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, f (Int.fract (α * (n k : ℝ)))

/--
Erdős Problem 995:

For every lacunary sequence $(n_k)$ of integers and every $f \in L^2([0,1])$ with
$\int_0^1 f = 0$, is it true that for almost all $\alpha$,
$$\sum_{k < N} f(\{\alpha n_k\}) = o\!\left(N \sqrt{\log\log N}\right)?$$
-/
@[category research open, AMS 11 42]
theorem erdos_995 :
    answer(sorry) ↔
      ∀ (n : ℕ → ℕ), IsLacunary n → ∀ (f : ℝ → ℝ),
        MemLp f 2 (volume.restrict (Icc (0 : ℝ) 1)) →
        ∫ x in (0 : ℝ)..1, f x = 0 →
        ∀ᵐ α ∂(volume.restrict (Icc (0 : ℝ) 1)),
          partialSum n f α =o[atTop] fun N => (N : ℝ) * Real.sqrt (Real.log (Real.log N)) := by
  sorry

/--
Erdős [Er49] showed the growth cannot be pushed below $N (\log\log N)^{1/2}$ by more than an
arbitrarily small power: there is a lacunary sequence and a mean-zero $f \in L^2([0,1])$ such
that for every $\varepsilon > 0$, for almost all $\alpha$,
$$\limsup_{N \to \infty} \frac{\sum_{k < N} f(\{\alpha n_k\})}{N (\log\log N)^{1/2 - \varepsilon}}
  = \infty.$$
-/
@[category research solved, AMS 11 42]
theorem erdos_995.variants.erdos_lower_bound :
    ∃ (n : ℕ → ℕ), IsLacunary n ∧ ∃ (f : ℝ → ℝ),
      MemLp f 2 (volume.restrict (Icc (0 : ℝ) 1)) ∧
      ∫ x in (0 : ℝ)..1, f x = 0 ∧
      ∀ ε > (0 : ℝ),
        ∀ᵐ α ∂(volume.restrict (Icc (0 : ℝ) 1)),
          atTop.limsup (fun N => (((partialSum n f α N) /
            ((N : ℝ) * (Real.log (Real.log N)) ^ ((1 : ℝ) / 2 - ε)) : ℝ) : EReal)) = ⊤ := by
  sorry

end Erdos995
