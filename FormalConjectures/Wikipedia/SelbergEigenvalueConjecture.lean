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
# Selberg's $1/4$ eigenvalue conjecture

For $N \ge 1$, the principal congruence subgroup $\Gamma(N) \le \mathrm{SL}_2(\mathbb{Z})$ acts on
the Poincaré half-plane $\mathbb{H} = \{(x, y) \in \mathbb{R}^2 \mid y > 0\}$ equipped with
hyperbolic area $dx\,dy / y^2$ and Laplace operator $\Delta = -y^2 (\partial_x^2 + \partial_y^2)$.
Atle Selberg (1965) proved that every positive eigenvalue of $\Delta$ on Maass forms for
$\Gamma(N)$ is at least $3/16$ and conjectured the lower bound $1/4$. Henry H. Kim and Peter Sarnak
(2003) improved the unconditional lower bound to $975/4096$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Selberg%27s_1/4_conjecture)
- [Se65] A. Selberg, *On the estimation of Fourier coefficients of modular forms*, Proc. Sympos.
  Pure Math., Vol. VIII, Amer. Math. Soc., Providence, R.I., 1965, pp. 1–15.
- [KS03] H. H. Kim and P. Sarnak, *Functoriality for the exterior square of $\mathrm{GL}_4$ and the
  symmetric fourth of $\mathrm{GL}_2$, Appendix 2: Refined estimates towards the Ramanujan and
  Selberg conjectures*, J. Amer. Math. Soc. 16 (2003), no. 1, 175–181.
-/

@[expose] public section

namespace SelbergEigenvalueConjecture

/-- Fractional linear action of $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ on $(x, y) \in \mathbb{R}^2$
via $z = x + i y \mapsto (a z + b) / (c z + d)$. -/
noncomputable def sl2PlaneAct (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (p : ℝ × ℝ) : ℝ × ℝ :=
  let z : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
  let w : ℂ := (((γ.1 0 0 : ℤ) : ℂ) * z + ((γ.1 0 1 : ℤ) : ℂ)) /
    (((γ.1 1 0 : ℤ) : ℂ) * z + ((γ.1 1 1 : ℤ) : ℂ))
  (w.re, w.im)

/-- A measurable subset $F \subseteq \mathbb{H}$ is a fundamental domain for
`CongruenceSubgroup.Gamma N` if elements acting nontrivially on $\mathbb{H}$ (which excludes
$\pm I$, accounting for $-I \in \Gamma(1), \Gamma(2)$) translate $F$ to sets meeting $F$ in measure
zero, and the $\Gamma(N)$-translates of $F$ cover $\mathbb{H}$ up to measure zero. -/
def IsGammaFundamentalDomain (N : ℕ) (F : Set (ℝ × ℝ)) : Prop :=
  MeasurableSet F ∧
  (∀ p ∈ F, 0 < p.2) ∧
  (∀ γ ∈ CongruenceSubgroup.Gamma N,
    ¬ (∀ p : ℝ × ℝ, 0 < p.2 → sl2PlaneAct γ p = p) →
      MeasureTheory.volume (F ∩ (sl2PlaneAct γ '' F)) = 0) ∧
  MeasureTheory.volume
    ({p : ℝ × ℝ | 0 < p.2} \ ⋃ γ ∈ CongruenceSubgroup.Gamma N, sl2PlaneAct γ '' F) = 0

/-- Smooth $\Gamma(N)$-invariant function on $\mathbb{H}$ that is square-integrable with zero
hyperbolic mean and finite Dirichlet energy over $F$. -/
def IsAdmissibleZeroMeanAutomorphic (N : ℕ) (F : Set (ℝ × ℝ)) (u : ℝ × ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ⊤ u {p : ℝ × ℝ | 0 < p.2} ∧
  (∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ p : ℝ × ℝ, 0 < p.2 → u (sl2PlaneAct γ p) = u p) ∧
  MeasureTheory.IntegrableOn (fun p : ℝ × ℝ ↦ (u p) ^ 2 / p.2 ^ 2) F MeasureTheory.volume ∧
  MeasureTheory.IntegrableOn
    (fun p : ℝ × ℝ ↦
      (deriv (fun x ↦ u (x, p.2)) p.1) ^ 2 + (deriv (fun y ↦ u (p.1, y)) p.2) ^ 2)
    F MeasureTheory.volume ∧
  (∫ p in F, u p / p.2 ^ 2) = 0

/-- The identity matrix in $\mathrm{SL}_2(\mathbb{Z})$ acts trivially on $\mathbb{R}^2$. -/
@[category API, AMS 11 35]
theorem sl2PlaneAct_one (p : ℝ × ℝ) : sl2PlaneAct 1 p = p := by
  simp [sl2PlaneAct]

/-- The upper-triangular generator $\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ acts by
horizontal translation $(x, y) \mapsto (x + 1, y)$. -/
@[category test, AMS 11 35]
theorem sl2PlaneAct_translation (p : ℝ × ℝ) :
    sl2PlaneAct ⟨!![1, 1; 0, 1], by decide⟩ p = (p.1 + 1, p.2) := by
  ext <;> simp [sl2PlaneAct, add_comm]

/-- The elliptic matrix $\begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$ fixes $(0, 1)$. -/
@[category test, AMS 11 35]
theorem sl2PlaneAct_inversion_zero_one :
    sl2PlaneAct ⟨!![0, -1; 1, 0], by decide⟩ (0, 1) = (0, 1) := by
  ext <;> simp [sl2PlaneAct]

/-- On $u(x, y) = 3x + 4y$, the Euclidean gradient-squared integrand equals $25$. -/
@[category test, AMS 11 35]
theorem dirichletIntegrand_linear (p : ℝ × ℝ) :
    let u : ℝ × ℝ → ℝ := fun q ↦ 3 * q.1 + 4 * q.2
    (deriv (fun x ↦ u (x, p.2)) p.1) ^ 2 + (deriv (fun y ↦ u (p.1, y)) p.2) ^ 2 = 25 := by
  intro u
  have hx : HasDerivAt (fun x : ℝ ↦ u (x, p.2)) 3 p.1 := by
    simpa [u] using ((hasDerivAt_id p.1).const_mul (3 : ℝ)).add_const (4 * p.2)
  have hy : HasDerivAt (fun y : ℝ ↦ u (p.1, y)) 4 p.2 := by
    simpa [u] using ((hasDerivAt_id p.2).const_mul (4 : ℝ)).const_add (3 * p.1)
  rw [hx.deriv, hy.deriv]
  norm_num

/-- The constant zero function satisfies `IsAdmissibleZeroMeanAutomorphic` on any set $F$. -/
@[category API, AMS 11 35]
theorem isAdmissibleZeroMeanAutomorphic_zero (N : ℕ) (F : Set (ℝ × ℝ)) :
    IsAdmissibleZeroMeanAutomorphic N F (fun _ ↦ 0) :=
  ⟨contDiffOn_const, fun _ _ _ _ ↦ rfl, by simp, by simp, by simp⟩

/-- The full plane $\mathbb{R}^2$ is not contained in $\mathbb{H}$ and thus is not a fundamental
domain. -/
@[category test, AMS 11 35]
theorem not_isGammaFundamentalDomain_univ (N : ℕ) :
    ¬ IsGammaFundamentalDomain N Set.univ := by
  intro h
  have h0 := h.2.1 (0, 0) (Set.mem_univ _)
  norm_num at h0

/-- **Selberg's $3/16$ Eigenvalue Bound** ([Se65]): For every congruence level $N \ge 1$,
fundamental domain $F$ of $\Gamma(N)$, and admissible zero-mean $\Gamma(N)$-invariant function $u$,
$$\frac{3}{16} \int_F \frac{u(x, y)^2}{y^2}\,dx\,dy \le
  \int_F \left((\partial_x u)^2 + (\partial_y u)^2\right) dx\,dy.$$ -/
@[category research solved, AMS 11 35]
theorem selberg_three_sixteenths_bound (N : ℕ) (hN : 1 ≤ N) (F : Set (ℝ × ℝ))
    (hF : IsGammaFundamentalDomain N F) (u : ℝ × ℝ → ℝ)
    (hu : IsAdmissibleZeroMeanAutomorphic N F u) :
    (3 / 16 : ℝ) * (∫ p in F, (u p) ^ 2 / p.2 ^ 2) ≤
      ∫ p in F, ((deriv (fun x ↦ u (x, p.2)) p.1) ^ 2 +
        (deriv (fun y ↦ u (p.1, y)) p.2) ^ 2) := by
  sorry

/-- **Kim–Sarnak $975/4096$ Eigenvalue Bound** ([KS03]): For every congruence level $N \ge 1$,
fundamental domain $F$ of $\Gamma(N)$, and admissible zero-mean $\Gamma(N)$-invariant function $u$,
$$\frac{975}{4096} \int_F \frac{u(x, y)^2}{y^2}\,dx\,dy \le
  \int_F \left((\partial_x u)^2 + (\partial_y u)^2\right) dx\,dy.$$ -/
@[category research solved, AMS 11 35]
theorem kim_sarnak_bound (N : ℕ) (hN : 1 ≤ N) (F : Set (ℝ × ℝ))
    (hF : IsGammaFundamentalDomain N F) (u : ℝ × ℝ → ℝ)
    (hu : IsAdmissibleZeroMeanAutomorphic N F u) :
    (975 / 4096 : ℝ) * (∫ p in F, (u p) ^ 2 / p.2 ^ 2) ≤
      ∫ p in F, ((deriv (fun x ↦ u (x, p.2)) p.1) ^ 2 +
        (deriv (fun y ↦ u (p.1, y)) p.2) ^ 2) := by
  sorry

/-- **Selberg's $1/4$ Eigenvalue Conjecture** ([Se65], p. 13): For every congruence level
$N \ge 1$, fundamental domain $F$ of $\Gamma(N)$, and admissible zero-mean $\Gamma(N)$-invariant
function $u$,
$$\frac{1}{4} \int_F \frac{u(x, y)^2}{y^2}\,dx\,dy \le
  \int_F \left((\partial_x u)^2 + (\partial_y u)^2\right) dx\,dy.$$

Note: We state the spectral bound $\lambda_1(\Gamma(N) \backslash \mathbb{H}) \ge 1/4$ variationally
via the Rayleigh quotient on zero-mean smooth $L^2 \cap \dot{H}^1$ functions; because the
continuous spectrum of $\Delta$ starts at $1/4$ and $\Gamma(N)$ has no non-constant residual
eigenfunctions in $(0, 1/4)$, this is equivalent to requiring all Maass cusp form eigenvalues to be
at least $1/4$. The condition $N \ge 1$ excludes `ZMod 0 = ℤ`, where `CongruenceSubgroup.Gamma 0`
has infinite hyperbolic covolume. -/
@[category research open, AMS 11 35]
theorem selberg_eigenvalue_conjecture (N : ℕ) (hN : 1 ≤ N) (F : Set (ℝ × ℝ))
    (hF : IsGammaFundamentalDomain N F) (u : ℝ × ℝ → ℝ)
    (hu : IsAdmissibleZeroMeanAutomorphic N F u) :
    (1 / 4 : ℝ) * (∫ p in F, (u p) ^ 2 / p.2 ^ 2) ≤
      ∫ p in F, ((deriv (fun x ↦ u (x, p.2)) p.1) ^ 2 +
        (deriv (fun y ↦ u (p.1, y)) p.2) ^ 2) := by
  sorry

end SelbergEigenvalueConjecture
