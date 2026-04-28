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

/--
Define $p \boxplus_n q(x)$ to be the polynomial
$$
(p \boxplus_n q)(x) = \sum_{k=0}^n c_k x^{n-k}
$$
where the coefficients $c_k$ are given by the formula:
$$
c_k = \sum_{i+j=k} \frac{(n-i)! (n-j)!}{n! (n-k)!} a_i b_j
$$
for $k = 0, 1, \dots, n$.
 -/
noncomputable def finiteAdditiveConvolution (n : ℕ) (p q : F[X]) : F[X] :=
  let c := fun k => ∑ ij ∈ antidiagonal (k : ℕ),
      ((n - ij.1)! * (n - ij.2)! : F) / (n ! * (n - k)! : F) *
      p.coeff (n - ij.1) * q.coeff (n - ij.2)
  ∑ k ∈ range (n + 1), c k • X^(n - k)

local notation p " (⊞_"n ")" q:65  => finiteAdditiveConvolution n p q

@[category test, AMS 26]
theorem finiteAdditiveConvolution_comm (n : ℕ) (p q : F[X]) :
    p (⊞_n) q = q (⊞_n) p := by
  show ∑ a ∈_, _= ∑ a ∈_, _
  exact sum_congr rfl fun m hm =>
    (congr_arg₂ _) (sum_equiv (.prodComm _ _) (by simp [add_comm]) fun _ _ => by ring!) rfl

@[category test, AMS 26]
theorem finiteAdditiveConvolution_degree (n : ℕ) (p q : ℝ[X])
  (hp : p.degree = n) (hq : q.degree = n):
    (p (⊞_n) q).degree = n := by
  sorry

@[category test, AMS 26]
theorem finiteAdditiveConvolution_monic' (n : ℕ) (p q : ℝ[X]) (hn : 0 < n)
    (hp : p.degree = n) (hq : q.degree = n) (hp : p.Monic) (hq : q.Monic) :
    (p (⊞_n) q).Monic := by
  sorry

/--
For a monic polynomial $p(x)=\prod_{i\le n}(x- \lambda_i)$, define
$$\Phi_n(p):=\sum_{i\le n}(\sum_{j\neq i} \frac1{\lambda_i-\lambda_j})^2$$
and $\Phi_n(p):=\infty$ if $p$ has a multiple root.
-/
noncomputable def Φ (p : ℝ[X]) : ℝ≥0∞ :=
  if p.roots.Nodup then
    let roots := p.roots.toFinset
    (∑ i ∈ roots, (∑ j ∈ roots.erase i, 1 / (i - j)) ^ 2).toNNReal
  else
    ⊤

/--
A predicate that holds if $p(x)$ and $q(x)$ are monic real-rooted polynomials of
degree $n$, then
$$\frac{1}{\Phi_n(p\boxplus_n q)} \ge \frac{1}{\Phi_n(p)}+\frac{1}{\Phi_n(q)}?$$
-/
def FourProp (p q : ℝ[X]) (n : ℕ) : Prop :=
    p.degree = n → p.roots.card = n → q.degree = n  → q.roots.card = n → p.Monic → q.Monic →
    1 / Φ p + 1 / Φ q ≤ 1 / Φ (p (⊞_n) q)

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
theorem four : answer(sorry) ↔ ∀ (p q : ℝ[X]) (n : ℕ), FourProp p q n := by
  sorry

/--
Is it true that if $p(x)$ and $q(x)$ are monic real-rooted polynomials of
degree $2$, then
$$\frac{1}{\Phi_2(p\boxplus_n q)} \ge \frac{1}{\Phi_2(p)}+\frac{1}{\Phi_2(q)}?$$
-/
@[category research open, AMS 26]
theorem four_2 : answer(sorry) ↔ ∀ (p q : ℝ[X]), FourProp p q 2 := by
  sorry

/--
Is it true that if $p(x)$ and $q(x)$ are monic real-rooted polynomials of
degree $3$, then
$$\frac{1}{\Phi_3(p\boxplus_n q)} \ge \frac{1}{\Phi_3(p)}+\frac{1}{\Phi_3(q)}?$$
-/
@[category research open, AMS 26]
theorem four_3 : answer(sorry) ↔ ∀ (p q : ℝ[X]), FourProp p q 3 := by
  sorry

end Arxiv.«2602.05192»
