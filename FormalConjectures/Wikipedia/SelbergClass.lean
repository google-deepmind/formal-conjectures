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
module

public import FormalConjecturesUtil

/-!
# The Selberg Class and the Degree Conjecture

In 1992, Atle Selberg [Se92] introduced an axiomatic class $\mathcal{S}$ of Dirichlet series
$F(s) = \sum_{n=1}^\infty a_n n^{-s}$ ($a_1 = 1$) admitting meromorphic continuation of finite
order with at most a pole at $s = 1$, Ramanujan growth $a_n = O_\varepsilon(n^\varepsilon)$, a
$\Gamma$-factor functional equation of degree $d_F = 2 \sum_{j=1}^r \lambda_j$, and a prime-power
logarithmic Euler product with exponent $\theta < 1/2$. It is conjectured [Se92, CG93] that $d_F$
belongs to $\mathbb{N}$ for every $F \in \mathcal{S}$. Conrey and Ghosh [CG93] proved that no
member of $\mathcal{S}$ has $0 < d_F < 1$, and Kaczorowski and Perelli [KP11] ruled out
$1 < d_F < 2$, leaving integrality of $d_F$ open for $d_F > 2$.

*References:*
- [Wikipedia: Selberg class](https://en.wikipedia.org/wiki/Selberg_class)
- [Se92] A. Selberg, *Old and new conjectures and results about a class of Dirichlet series*, in
  *Proceedings of the Amalfi Conference on Analytic Number Theory* (Maiori, 1989), Univ. Salerno,
  1992, 367–385.
- [CG93] J. B. Conrey and A. Ghosh, *On the Selberg class of Dirichlet series: small degrees*, Duke
  Math. J. **72** (1993), no. 3, 673–693. https://doi.org/10.1215/S0012-7094-93-07225-0
- [KP11] J. Kaczorowski and A. Perelli, *On the structure of the Selberg class, VII: $1 < d < 2$*,
  Ann. of Math. (2) **173** (2011), no. 3, 1397–1441.
  https://doi.org/10.4007/annals.2011.173.3.4
-/

@[expose] public section

namespace SelbergClass

/-- Bundled member of Selberg's axiomatic $L$-function class $\mathcal{S}$ [Se92].
To allow a genuine pole of order at most `poleOrder` at $s = 1$ without a removable discontinuity
at $s = 1$, analyticity and finite order are stated via an entire function `entireExtension`
agreeing with $(s - 1)^{\text{poleOrder}} F(s)$ on $\mathbb{C} \setminus \{1\}$. The functional
equation is stated on the open strip $0 < \operatorname{Re}(s) < 1$, where every
$\Gamma(\lambda_j s + \mu_j)$ factor is pole-free and analytic continuation determines the global
meromorphic identity. -/
structure SelbergClassMember : Type where
  /-- Dirichlet coefficients $a_n$, normalized with $a_0 = 0$ and $a_1 = 1$. -/
  a : ℕ → ℂ
  a_zero : a 0 = 0
  a_one : a 1 = 1
  /-- Meromorphic continuation $F(s)$ of $\sum_{n \ge 1} a_n n^{-s}$ away from $s = 1$. -/
  F : ℂ → ℂ
  dirichlet_conv : ∀ s : ℂ, 1 < s.re → HasSum (fun n : ℕ ↦ a n / (n : ℂ) ^ s) (F s)
  /-- Entire finite-order witness `entireExtension` for $(s - 1)^m F(s)$ away from $s = 1$. -/
  poleOrder : ℕ
  entireExtension : ℂ → ℂ
  entireExtension_differentiable : Differentiable ℂ entireExtension
  entireExtension_eq : ∀ s : ℂ, s ≠ 1 → (s - 1) ^ poleOrder * F s = entireExtension s
  finite_order : ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
    ∀ s : ℂ, ‖entireExtension s‖ ≤ C * Real.exp (‖s‖ ^ κ)
  /-- Functional equation data $(Q, r, \lambda_j, \mu_j, \omega)$. -/
  Q : ℝ
  Q_pos : 0 < Q
  r : ℕ
  lam : Fin r → ℝ
  lam_pos : ∀ j : Fin r, 0 < lam j
  mu : Fin r → ℂ
  mu_re_nonneg : ∀ j : Fin r, 0 ≤ (mu j).re
  omega : ℂ
  omega_norm : ‖omega‖ = 1
  /-- Functional equation $\Phi(s) = \omega \overline{\Phi(1 - \bar{s})}$ on
  $0 < \operatorname{Re}(s) < 1$. -/
  functional_eq : ∀ s : ℂ, 0 < s.re → s.re < 1 →
    let gammaProd : ℂ → ℂ := fun z ↦
      (Q : ℂ) ^ z * ∏ j : Fin r, Complex.Gamma ((lam j : ℂ) * z + mu j)
    gammaProd s * F s =
      omega * starRingEnd ℂ (gammaProd (1 - starRingEnd ℂ s) * F (1 - starRingEnd ℂ s))
  /-- Ramanujan coefficient bound $a_n \ll_\varepsilon n^\varepsilon$. -/
  ramanujan_bound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ ε
  /-- Logarithmic Euler product $\log F(s) = \sum_{n \ge 1} b_n n^{-s}$ supported on prime powers
  with $|b_n| \le B n^\theta$ for some $\theta < 1/2$. -/
  b : ℕ → ℂ
  b_support : ∀ n : ℕ, ¬ IsPrimePow n → b n = 0
  theta : ℝ
  theta_lt_half : theta < 1 / 2
  b_bound : ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 1 ≤ n → ‖b n‖ ≤ B * (n : ℝ) ^ theta
  euler_product : ∀ s : ℂ, 1 < s.re →
    ∃ L : ℂ, HasSum (fun n : ℕ ↦ b n / (n : ℂ) ^ s) L ∧ Complex.exp L = F s

/-- Degree $d_F = 2 \sum_{j=1}^r \lambda_j$ of a member of the Selberg class. -/
def selbergDegree (S : SelbergClassMember) : ℝ :=
  2 * ∑ j : Fin S.r, S.lam j

/-- Every member of the Selberg class has nonnegative degree $d_F \ge 0$. -/
@[category API, AMS 11]
theorem selbergDegree_nonneg (S : SelbergClassMember) : 0 ≤ selbergDegree S := by
  unfold selbergDegree
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ ↦ (S.lam_pos j).le)

/-- Whenever a Selberg class member has at least one $\Gamma$-factor ($r \ge 1$), its degree is
strictly positive. -/
@[category API, AMS 11]
theorem selbergDegree_pos_of_pos_r (S : SelbergClassMember) (hr : 0 < S.r) :
    0 < selbergDegree S := by
  unfold selbergDegree
  have hsum : 0 < ∑ j : Fin S.r, S.lam j :=
    Finset.sum_pos (fun j _ ↦ S.lam_pos j) ⟨⟨0, hr⟩, Finset.mem_univ _⟩
  linarith

/-- The constant Dirichlet series $F(s) = 1$ ($a_1 = 1$, $a_n = 0$ for $n \ne 1$) as a concrete
degree-$0$ member of $\mathcal{S}$. -/
noncomputable def SelbergClassMember.one : SelbergClassMember where
  a n := if n = 1 then 1 else 0
  a_zero := by simp
  a_one := by simp
  F _ := 1
  dirichlet_conv s _hs := by
    have hfun : (fun n : ℕ ↦ (if n = 1 then (1 : ℂ) else 0) / (n : ℂ) ^ s) =
        fun n : ℕ ↦ if n = 1 then (1 : ℂ) else 0 := by
      ext n
      split_ifs with hn
      · subst hn; simp
      · simp
    rw [hfun]
    exact hasSum_ite_eq 1 (1 : ℂ)
  poleOrder := 0
  entireExtension _ := 1
  entireExtension_differentiable := differentiable_const 1
  entireExtension_eq _ _ := by simp
  finite_order := ⟨1, 1, one_pos, one_pos, fun s ↦ by
    rw [norm_one, one_mul]
    exact Real.one_le_exp (Real.rpow_nonneg (norm_nonneg s) 1)⟩
  Q := 1
  Q_pos := one_pos
  r := 0
  lam := Fin.elim0
  lam_pos j := Fin.elim0 j
  mu := Fin.elim0
  mu_re_nonneg j := Fin.elim0 j
  omega := 1
  omega_norm := norm_one
  functional_eq s _hs0 _hs1 := by
    dsimp only
    simp
  ramanujan_bound ε _hε := by
    refine ⟨1, one_pos, fun n _hn ↦ ?_⟩
    split_ifs with h1
    · subst h1; simp
    · simp [Real.rpow_nonneg (Nat.cast_nonneg n) ε]
  b _ := 0
  b_support _ _ := rfl
  theta := 0
  theta_lt_half := by norm_num
  b_bound := ⟨1, one_pos, fun _ _ ↦ by simp⟩
  euler_product _ _ := ⟨0, by simp, Complex.exp_zero⟩

/-- The constant Dirichlet series $F(s) = 1$ has degree $0$. -/
@[category test, AMS 11]
theorem selbergDegree_one : selbergDegree SelbergClassMember.one = 0 := by
  rw [selbergDegree]
  change 2 * ∑ j : Fin 0, Fin.elim0 j = 0
  simp

/--
**Small-Degree Classification Theorem** [CG93, KP11]: Every member $F$ of the Selberg class with
$d_F < 2$ satisfies $d_F = 0$ or $d_F = 1$.
-/
@[category research solved, AMS 11]
theorem selberg_class_degree_lt_two (S : SelbergClassMember) (hlt : selbergDegree S < 2) :
    selbergDegree S = 0 ∨ selbergDegree S = 1 := by
  sorry

/--
**Degree Conjecture for the Selberg Class** [Se92, CG93]: For every member $F$ of the Selberg
class $\mathcal{S}$, its degree $d_F$ belongs to $\mathbb{N}$.
-/
@[category research open, AMS 11]
theorem selberg_class_degree_conjecture (S : SelbergClassMember) :
    ∃ d : ℕ, selbergDegree S = (d : ℝ) := by
  sorry

end SelbergClass
