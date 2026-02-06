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

namespace Arxiv.«2602.05192»

variable {F : Type} [Field F]

/-- The finite additive convolution of two monic polynomials of degree n. -/
noncomputable def finiteAdditiveConvolution (n : ℕ) (p q : F[X]) : F[X] :=
  let c := fun k  => ∑ ij ∈ antidiagonal (k : ℕ),
      ((n - ij.1)! * (n - ij.2)! : F) / (n ! * (n - k)! : F) *
      (p.coeff (n - ij.1)) * (q.coeff (n - ij.2))
  ∑ k ∈ range (n + 1),  (c k) • X^(n - k)

local notation p " (⊞_"n ")" q:65  => finiteAdditiveConvolution n p q

@[category test, AMS 26]
theorem finiteAdditiveConvolution_comm (n : ℕ) (p q : F[X]) :
    p (⊞_n) q = q (⊞_n) p := by
  show ∑ a ∈_, _= ∑ a ∈_, _
  exact sum_congr rfl fun m hm  =>
    (congr_arg₂ _) (sum_equiv (.prodComm _ _) (by simp [add_comm]) fun _ _ => by ring!) rfl


/-- The quantity $Φ_n(p)$ based on the sum of the squares of terms of roots. -/
noncomputable def Φ (n : ℕ) (p : ℝ[X]) : ℝ≥0∞ :=
  if p.Monic ∧ p.degree = n ∧ p.roots.Nodup then
    let roots := p.roots.toFinset
    (∑ ij ∈ roots.offDiag, (1 : ℝ) / (ij.1 - ij.2)^(2 : ℝ)).toNNReal
  else
    ⊤

/--
Is it true that if $p(x)$ and $q(x)$ are monic real-rooted polynomials of
degree $n$, then
$$\frac{1}{\Phi_n(p\boxplus_n q)} \ge \frac{1}{\Phi_n(p)}+\frac{1}{\Phi_n(q)}?$$

Note: while no proof of this is published yet, the authors of
[arxiv/2602.05192](https://arxiv.org/abs/2602.05192) announced that a proof will be released
on 2026-02-13

TODO(firsching): update category and remove Note when proof is published.
-/
@[category research open, AMS 26]
theorem four : answer(sorry) ↔
    ∀ (p q : ℝ[X]) (n : ℕ), p.degree = n → p.roots.card = n → q.degree = n → p.Monic → q.Monic →
    1 / Φ n (p (⊞_n) q) ≥ 1 / Φ n p + 1 / Φ n q := by
  sorry

end Arxiv.«2602.05192»
