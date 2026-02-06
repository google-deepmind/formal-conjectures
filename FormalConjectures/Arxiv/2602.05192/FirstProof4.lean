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
# Theorem 4

*Reference:* [arxiv/2602.05192](https://arxiv.org/abs/2602.05192)
**First Proof**
by *Mohammed Abouzaid, Andrew J. Blumberg, Martin Hairer, Joe Kileel, Tamara G. Kolda, Paul D. Nelson, Daniel Spielman, Nikhil Srivastava, Rachel Ward, Shmuel Weinberger, Lauren Williams*
-/

open Polynomial Finset ENNReal
open scoped Nat

open Classical

variable {k : Type} [Field k] (n : ℕ) [DecidableEq k]

/-- The finite additive convolution of two monic polynomials of degree n. -/
def finiteAdditiveConvolution (n : ℕ) (p q : k[X]) : k[X] :=
  let a := fun i => p.coeff (n - i)
  let b := fun j => q.coeff (n - j)
  Polynomial.ofFn n <| fun m  =>
    ∑ ij ∈ antidiagonal (m : ℕ),
      ((n - ij.1)! * (n - ij.2)! : k) /
       (n ! * (n - m)! : k) * a ij.1 * b ij.2

local notation p " (⊞_"n ")" q  => finiteAdditiveConvolution n p q

/-- The quantity $Φ_n(p)$ based on the sum of the squares of terms of roots. -/
noncomputable def Φ (n : ℕ) (p : ℝ[X]) : ℝ≥0∞ :=
  if p.Monic ∧ p.degree = n ∧ p.roots.Nodup then
    let roots := p.roots.toFinset
    (∑ i ∈ roots, (∑ j ∈ roots.erase i, (1 : ℝ) / (i - j))^(2 : ℝ)).toNNReal
  else
    ⊤

/--
Is it true that if $p(x)$ and $q(x)$ are monic real-rooted polynomials of
degree $n$, then
$$\frac1{\Phi_n(p\boxplus_n q)} \ge \frac1{\Phi_n(p)}+\frac1{\Phi_n(q)}?$$
-/
@[category research open, AMS 26]
theorem four : answer(sorry) ↔
    ∀ (p q : ℝ[X]) (n : ℕ), p.degree = n → q.degree = n →
    1 / Φ n (p (⊞_n) q) ≥ 1 / Φ n p + 1 / Φ n q := by
  sorry
