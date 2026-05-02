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

*Reference:* [arxiv/2602.05192v2](https://arxiv.org/abs/2602.05192v2)
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
    (hp_deg : p.degree = n) (hq_deg : q.degree = n) (hp_monic : p.Monic) (hq_monic : q.Monic) :
    (p (⊞_n) q).Monic := by
  have hc0 : ∑ ij ∈ antidiagonal 0, ((n - ij.1)! * (n - ij.2)! : ℝ) / (n ! * (n - 0)! : ℝ) *
      p.coeff (n - ij.1) * q.coeff (n - ij.2) = 1 := by
    rw [antidiagonal_zero]
    simp
    have hp1 : p.coeff n = 1 := by
      have : p.natDegree = n := natDegree_eq_of_degree_eq_some hp_deg
      rw [← this]
      exact hp_monic
    have hq1 : q.coeff n = 1 := by
      have : q.natDegree = n := natDegree_eq_of_degree_eq_some hq_deg
      rw [← this]
      exact hq_monic
    rw [hp1, hq1]
    have h_ne : (n ! : ℝ) ≠ 0 := by positivity
    simp [h_ne]
  -- The polynomial is ∑ k ∈ range (n+1), c(k) • X^(n-k).
  -- Show coeff n equals 1 (from the k=0 term) and natDegree ≤ n.
  set r := p (⊞_n) q
  suffices h : r.coeff n = 1 ∧ r.natDegree ≤ n by
    rw [Polynomial.Monic, Polynomial.leadingCoeff]
    rcases Nat.eq_or_lt_of_le h.2 with heq | hlt
    · rw [heq]; exact h.1
    · exfalso; rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt] at h; linarith [h.1]
  constructor
  · -- coeff n of (∑ k ∈ range (n+1), c(k) • X^(n-k)) = c(0) = 1
    change (finiteAdditiveConvolution n p q).coeff n = 1
    simp only [finiteAdditiveConvolution]
    rw [Polynomial.finset_sum_coeff]
    conv_lhs =>
      arg 2; ext k
      rw [Polynomial.coeff_smul, Polynomial.coeff_X_pow]
    simp only [smul_eq_mul]
    -- Now: ∑ k ∈ range (n+1), c(k) * if n = n - k then 1 else 0
    -- Only k=0 contributes (since n = n - k ↔ k = 0 for k ≤ n)
    rw [Finset.sum_eq_single 0]
    · -- The k=0 term: simplify n - 0 = n, if-cond = true, then use hc0
      simp only [Nat.sub_zero, ite_true, mul_one]
      exact hc0
    · -- All other terms are 0
      intro k _ hk0
      have : n ≠ n - k := by omega
      simp [this]
    · -- 0 ∈ range (n+1)
      intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · -- natDegree ≤ n: each term has degree ≤ n since n - k ≤ n
    change (finiteAdditiveConvolution n p q).natDegree ≤ n
    simp only [finiteAdditiveConvolution]
    apply (Polynomial.natDegree_sum_le _ _).trans
    apply Finset.sup_le
    intro k hk
    apply (Polynomial.natDegree_smul_le _ _).trans
    exact (Polynomial.natDegree_X_pow_le (n - k)).trans (Nat.sub_le n k)

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

[arxiv/2602.05192v2](https://arxiv.org/abs/2602.05192v2) contains a proof.
-/
@[category research solved, AMS 26, formal_proof using lean4 at
"https://github.com/frenzymath/Archon-FirstProof-Results/blob/main/FirstProof/FirstProof4/Problem4.lean"]
theorem four : answer(True) ↔ ∀ (p q : ℝ[X]) (n : ℕ), FourProp p q n := by
  sorry

/--
Is it true that if $p(x)$ and $q(x)$ are monic real-rooted polynomials of
degree $2$, then
$$\frac{1}{\Phi_2(p\boxplus_n q)} \ge \frac{1}{\Phi_2(p)}+\frac{1}{\Phi_2(q)}?$$
-/
@[category research solved, AMS 26]
theorem four_2 : answer(True) ↔ ∀ (p q : ℝ[X]), FourProp p q 2 := by
  sorry

/--
Is it true that if $p(x)$ and $q(x)$ are monic real-rooted polynomials of
degree $3$, then
$$\frac{1}{\Phi_3(p\boxplus_n q)} \ge \frac{1}{\Phi_3(p)}+\frac{1}{\Phi_3(q)}?$$
-/
@[category research solved, AMS 26]
theorem four_3 : answer(True  ) ↔ ∀ (p q : ℝ[X]), FourProp p q 3 := by
  sorry

end Arxiv.«2602.05192»
