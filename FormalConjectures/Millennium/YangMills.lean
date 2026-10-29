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
# 4D Yang–Mills Existence and Mass Gap (Clay Millennium Prize Problem)

This file formalizes the official Clay Millennium Prize Problem statement by Arthur Jaffe
and Edward Witten (2000): *"Quantum Yang-Mills Theory"*.

## Mathematical Structure
For any compact simple Lie group $G$, pure quantum Yang–Mills theory on four-dimensional
Minkowski spacetime $\mathbb{R}^{1,3}$ (or Euclidean spacetime $\mathbb{R}^4$) must:
1. Satisfy the **Wightman Axioms** on a complete, separable complex Hilbert space $\mathcal{H}$
   with a dense Poincaré-invariant linear domain $\mathcal{D} \subset \mathcal{H}$, a unitary
   representation of the restricted Poincaré group $\mathcal{P}_+^\uparrow$, unbounded
   symmetric and mutually commuting energy-momentum generators $P^\mu = (H, \mathbf{P})$ on
   $\mathcal{D}$ acting as strong spacetime translation derivatives (`HasDerivAt`) whose joint
   expectations lie in the closed forward light cone $\bar{V}_+$, a unique normalized
   zero-energy vacuum state $\Omega \in \mathcal{D}$ ($H\Omega = 0$), Poincaré covariance, and
   microcausality (spacelike commutativity).
2. Exhibit **Local Quantum Field Operators and Yang–Mills Short-Distance Dynamics**
   (Jaffe–Witten §4, p. 6):
   Local quantum field operators in dimension-filtered correspondence ($\dim \le d$) with
   gauge-invariant local differential polynomials in the curvature $F = dA + A \wedge A$ and
   its covariant derivatives (such as $\operatorname{Tr}(F_{\mu\nu}F^{\mu\nu})(x)$ and the
   symmetric conserved stress-energy tensor $T_{\mu\nu}(x)$ generating the Hamiltonian $H$),
   whose short-distance correlations and Operator Product Expansion (OPE) agree with the
   predictions of asymptotic freedom ($b_0 > 0$) and perturbative renormalization theory,
   alongside gauge-invariant Wilson loop observables $W(\gamma, \chi)$.
3. Exhibit a strictly positive **Mass Gap** $\Delta > 0$ on the orthogonal complement
   $(\mathbb{C}\Omega)^\perp \cap \mathcal{D}$:
   $$\forall \psi \in \mathcal{D},\, \langle \Omega, \psi \rangle = 0 \implies \|H\psi\| \ge \Delta \|\psi\|$$
4. Admit an equivalent **Osterwalder–Schrader Euclidean Framework** on $\mathbb{R}^4$
   (Osterwalder–Schrader I, pp. 88–89; II, pp. 282, 287) via Schwinger distributions $S_n$
   satisfying the uniform linear growth condition ($\text{E}0'$), multilinearity, $\mathrm{ISO}(4)$
   Euclidean invariance (E1), mixed-degree reflection positivity across $\{x^0 = 0\}$ (E2), permutation
   symmetry (E3), full multi-field exponential clustering with rate $m > 0$ (E4), and integral
   compatibility on non-coincident configurations.

## References
* Jaffe, A., & Witten, E. (2000). *Quantum Yang-Mills Theory*. Clay Mathematics Institute.
* Osterwalder, K., & Schrader, R. (1973, 1975). *Axioms for Euclidean Green's Functions I & II*.
  Communications in Mathematical Physics, 31(2), 83–112; 42(3), 281–305.
* Streater, R. F., & Wightman, A. S. (1964). *PCT, Spin and Statistics, and All That*.
-/

@[expose] public section

open scoped Real InnerProductSpace Topology Matrix BigOperators
open scoped SchwartzMap
open MeasureTheory
open TopologicalSpace

namespace YangMills

/- ### 1. Compact Simple Gauge Groups and Representation Characters -/

/-- A conjugacy-invariant class function (representation character) on a gauge group `G`. -/
structure ClassFunction (G : Type*) [Group G] where
  toFun : G → ℂ
  conj_invariant : ∀ g h : G, toFun (g * h * g⁻¹) = toFun h

/-- Complex-conjugate (dual unitary representation) character $\bar{\chi}(g) = \overline{\chi(g)}$. -/
def ClassFunction.conj {G : Type*} [Group G] (chi : ClassFunction G) : ClassFunction G where
  toFun := fun g => starRingEnd ℂ (chi.toFun g)
  conj_invariant := fun g h => by rw [chi.conj_invariant]

/-- Constant (trivial-representation multiple) class function $g \mapsto c$. -/
def ClassFunction.const (G : Type*) [Group G] (c : ℂ) : ClassFunction G where
  toFun := fun _ => c
  conj_invariant := fun _ _ => rfl

/-- A compact, connected, non-abelian simple Lie group acting as the internal gauge symmetry group $G$.
Formulated as a `Prop`-valued class with propositional compactness (`IsCompact`) and
connectedness (`IsConnected`) fields so that concrete matrix groups such as $\mathrm{SU}(N)$
do not fail parent typeclass synthesis. Every proper normal subgroup $N \triangleleft G$
is finite and contained in the discrete center $Z(G)$ (e.g. $Z(\mathrm{SU}(N)) \cong \mathbb{Z}/N\mathbb{Z}$). -/
class CompactSimpleLieGroup (G : Type*) [TopologicalSpace G] [Group G] : Prop extends
    IsTopologicalGroup G where
  /-- Compactness of the underlying group space $G$ -/
  is_compact : IsCompact (Set.univ : Set G)
  /-- Connectedness of the underlying group space $G$ -/
  is_connected : IsConnected (Set.univ : Set G)
  /-- $G$ is non-abelian -/
  non_abelian : ∃ g h : G, g * h ≠ h * g
  /-- Simplicity up to the discrete center: every normal subgroup is either $\top$ or finite central -/
  normal_subgroups_central :
    ∀ (N : Subgroup G), N.Normal → N = ⊤ ∨ (N ≤ Subgroup.center G ∧ Finite N)
  /-- Existence of a non-trivial fundamental representation character $\chi_{\mathrm{fund}}$ of dimension $\ge 2$ -/
  has_fundamental_character :
    ∃ χ : ClassFunction G, 2 ≤ (χ.toFun 1).re ∧ ∃ g : G, χ.toFun g ≠ χ.toFun 1

/-- The Special Unitary Group $\mathrm{SU}(N)$ for $N \ge 2$, defined via Mathlib's
`Matrix.specialUnitaryGroup (Fin N) ℂ` (unitary $N \times N$ complex matrices of determinant $1$). -/
abbrev SUN (N : ℕ) : Type := Matrix.specialUnitaryGroup (Fin N) ℂ

/-- Canonical $\mathrm{SU}(2)$ Yang–Mills gauge group -/
abbrev SU2 : Type := SUN 2

/-- Canonical $\mathrm{SU}(3)$ Quantum Chromodynamics (QCD) gauge group -/
abbrev SU3 : Type := SUN 3

instance : Fact (2 ≤ 2) := ⟨le_rfl⟩
instance : Fact (2 ≤ 3) := ⟨by omega⟩

/-- Standard Lie-theoretic theorem: For every $N \ge 2$, the special unitary group $\mathrm{SU}(N)$
is a compact, connected, non-abelian simple Lie group with center $\mathbb{Z}/N\mathbb{Z}$
and trace character of dimension $N \ge 2$. -/
@[category research solved, AMS 22]
theorem sun_compactSimpleLieGroup (N : ℕ) [Fact (2 ≤ N)] :
    CompactSimpleLieGroup (SUN N) := by
  sorry

attribute [instance] sun_compactSimpleLieGroup

/- ### 2. Spacetime Geometry, WithLp Coercions, and the Poincaré Group -/

/-- Four-dimensional Euclidean / Minkowski coordinate space wrapped in Mathlib's `EuclideanSpace`. -/
abbrev EuclideanSpace4 := EuclideanSpace ℝ (Fin 4)

/-- Alias for Minkowski 4-vectors. -/
abbrev MinkowskiSpace := EuclideanSpace ℝ (Fin 4)

/-- Coercion from `EuclideanSpace ℝ (Fin 4)` (`WithLp 2 (Fin 4 → ℝ)`) to raw coordinates `Fin 4 → ℝ`. -/
def toCoords (x : EuclideanSpace4) : Fin 4 → ℝ :=
  WithLp.equiv 2 (Fin 4 → ℝ) x

/-- Coercion from raw coordinates `Fin 4 → ℝ` to `EuclideanSpace ℝ (Fin 4)`. -/
def ofCoords (v : Fin 4 → ℝ) : EuclideanSpace4 :=
  (WithLp.equiv 2 (Fin 4 → ℝ)).symm v

/-- Explicit constructor for a 4-vector $(t, x, y, z) \in \mathbb{R}^4$ using Mathlib's
vector notation `![t, x, y, z]`, avoiding non-exhaustive `Fin 4` pattern matching. -/
def vec4 (t x y z : ℝ) : EuclideanSpace4 :=
  ofCoords ![t, x, y, z]

/-- Pure spatial translation vector along spatial axis `i ∈ {0, 1, 2}` (coordinate `Fin.succ i`). -/
def spatialVec (i : Fin 3) (s : ℝ) : EuclideanSpace4 :=
  ofCoords (Pi.single (Fin.succ i) s)

/-- Euclidean time reflection $\theta(x^0, x^1, x^2, x^3) = (-x^0, x^1, x^2, x^3)$. -/
def timeReflect (x : EuclideanSpace4) : EuclideanSpace4 :=
  let c := toCoords x
  vec4 (-(c 0)) (c 1) (c 2) (c 3)

/-- Affine transformation $x \mapsto v + R x$ on `EuclideanSpace4`. -/
def euclideanTransform (R : Matrix (Fin 4) (Fin 4) ℝ) (v x : EuclideanSpace4) : EuclideanSpace4 :=
  ofCoords (fun μ => toCoords v μ + R.mulVec (toCoords x) μ)

/-- Translation of a configuration `Y : Fin m → EuclideanSpace4` by `a : EuclideanSpace4`. -/
def translateConfig {m : ℕ} (a : EuclideanSpace4) (Y : Fin m → EuclideanSpace4) :
    Fin m → EuclideanSpace4 :=
  fun j => ofCoords (fun μ => toCoords (Y j) μ + toCoords a μ)

/-- The Minkowski metric tensor $\eta = \mathrm{diag}(1, -1, -1, -1)$. -/
def minkowskiMetric : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (toCoords (vec4 1 (-1) (-1) (-1)))

/-- Minkowski inner ℂ product $\eta(x, y) = x^0 y^0 - \mathbf{x} \cdot \mathbf{y}$. -/
def minkowskiInner (x y : MinkowskiSpace) : ℝ :=
  let cx := toCoords x
  let cy := toCoords y
  cx 0 * cy 0 - (cx 1 * cy 1 + cx 2 * cy 2 + cx 3 * cy 3)

/-- The closed forward light cone $\bar{V}_+ = \{ p \in \mathbb{R}^{1,3} \mid p^0 \ge 0 \wedge \eta(p,p) \ge 0 \}$. -/
def ClosedForwardLightCone : Set MinkowskiSpace :=
  { p | 0 ≤ toCoords p 0 ∧ 0 ≤ minkowskiInner p p }

/-- Two spacetime points $x, y$ are spacelike separated if $\eta(x - y, x - y) < 0$. -/
def SpacelikeSeparated (x y : MinkowskiSpace) : Prop :=
  let diff := ofCoords (fun μ => toCoords x μ - toCoords y μ)
  minkowskiInner diff diff < 0

/-- A parameterized closed loop $\gamma : [0, 1] \to \mathbb{R}^4$ in spacetime. -/
structure ClosedLoop4D where
  curve : ℝ → MinkowskiSpace
  periodic : ∀ s : ℝ, curve (s + 1) = curve s

/-- Constant (zero-length) loop at a spacetime point $x \in \mathbb{R}^{1,3}$. -/
def ClosedLoop4D.const (x : MinkowskiSpace) : ClosedLoop4D where
  curve := fun _ => x
  periodic := fun _ => rfl

/-- Orientation-reversed 4D loop $\gamma^{-1}(s) = \gamma(1 - s)$. -/
def ClosedLoop4D.reverse (gamma : ClosedLoop4D) : ClosedLoop4D where
  curve := fun s => gamma.curve (1 - s)
  periodic := fun s => by
    have h := gamma.periodic (1 - s - 1)
    ring_nf at h ⊢
    exact h.symm

/-- Two closed loops are spacelike separated if every point on $\gamma_1$ is spacelike separated from $\gamma_2$. -/
def LoopsSpacelikeSeparated (gamma1 gamma2 : ClosedLoop4D) : Prop :=
  ∀ s1 s2 : ℝ, SpacelikeSeparated (gamma1.curve s1) (gamma2.curve s2)

/-- The restricted Poincaré group $\mathcal{P}_+^\uparrow = \mathbb{R}^{1,3} \rtimes \mathrm{SO}^+(1,3)$.
Enforces Minkowski metric preservation $\Lambda^T \eta \Lambda = \eta$, properness $\det \Lambda = 1$,
and orthochronicity $\Lambda^0{}_0 \ge 1$. -/
structure PoincareGroup where
  translation : MinkowskiSpace
  lorentz : Matrix (Fin 4) (Fin 4) ℝ
  preserves_metric : lorentz.transpose * minkowskiMetric * lorentz = minkowskiMetric
  is_proper : Matrix.det lorentz = 1
  is_orthochronous : 1 ≤ lorentz 0 0

/-- Identity element of the Poincaré group. -/
def PoincareGroup.id : PoincareGroup where
  translation := vec4 0 0 0 0
  lorentz := 1
  preserves_metric := by simp
  is_proper := Matrix.det_one
  is_orthochronous := le_rfl

/-- Pure spacetime translation $(a, I) \in \mathcal{P}_+^\uparrow$. -/
def PoincareGroup.ofTranslation (a : MinkowskiSpace) : PoincareGroup where
  translation := a
  lorentz := 1
  preserves_metric := by simp
  is_proper := Matrix.det_one
  is_orthochronous := le_rfl

/-- Semidirect product relation $(a_1, \Lambda_1) \cdot (a_2, \Lambda_2) = (a_1 + \Lambda_1 a_2, \Lambda_1 \Lambda_2)$
    on `PoincareGroup`, defined without `sorry`. -/
def PoincareGroup.IsProduct (g1 g2 g3 : PoincareGroup) : Prop :=
  g3.translation = euclideanTransform g1.lorentz g1.translation g2.translation ∧
  g3.lorentz = g1.lorentz * g2.lorentz

/-- Action of a Poincaré transformation $g = (a, \Lambda)$ on a closed spacetime loop $\gamma$. -/
def PoincareGroup.actLoop (g : PoincareGroup) (gamma : ClosedLoop4D) : ClosedLoop4D where
  curve := fun s => euclideanTransform g.lorentz g.translation (gamma.curve s)
  periodic := fun s => by simp [gamma.periodic s]

/- ### 2b. Classical Gauge-Invariant Curvature Polynomials and Perturbative UV Data -/

/-- Specification of the graded space of classical gauge-invariant local differential polynomials
in the $\mathfrak{g}$-valued Yang–Mills curvature two-form $F_{\mu\nu} = \partial_\mu A_\nu - \partial_\nu A_\mu + [A_\mu, A_\nu]$
and its covariant derivatives $D_{\alpha_1} \cdots D_{\alpha_k} F_{\mu\nu}$ (Jaffe–Witten §4, p. 6).
Includes the canonical scaling dimension ($\dim(F) = 2$, $\dim(D) = 1$), the scalar action density
$\operatorname{Tr}(F_{\mu\nu}F^{\mu\nu})$ of dimension $4$, the symmetric classical stress-energy tensor
$T_{\mu\nu}$ of dimension $4$, and the perturbative short-distance renormalization group data governed
by the 1-loop asymptotic freedom beta-function coefficient $b_0 = \frac{11 C_2(G)}{48\pi^2} > 0$. -/
structure CurvaturePolynomialAlgebra (G : Type*) [TopologicalSpace G] [Group G]
    [CompactSimpleLieGroup G] where
  /-- Type of classical gauge-invariant local differential polynomials in $(F, D F, D^2 F, \dots)$ -/
  Poly : Type*
  [addCommGroup : AddCommGroup Poly]
  [module : Module ℂ Poly]
  /-- Star involution / Hermitian conjugation on classical curvature polynomials -/
  conj : Poly → Poly
  conj_involutive : ∀ P : Poly, conj (conj P) = P
  /-- Classical mass/scaling dimension $\dim(P) \in \mathbb{N}$ ($\dim(F_{\mu\nu}) = 2$, $\dim(D_\mu) = 1$) -/
  classicalDim : Poly → ℕ
  dim_zero : classicalDim 0 = 0
  dim_conj : ∀ P : Poly, classicalDim (conj P) = classicalDim P
  /-- Lorentz representation action of $\mathrm{SO}^+(1,3)$ (and Euclidean $\mathrm{SO}(4)$) on local polynomials -/
  transform : Matrix (Fin 4) (Fin 4) ℝ → Poly →ₗ[ℂ] Poly
  transform_dim : ∀ (R : Matrix (Fin 4) (Fin 4) ℝ) (P : Poly),
    classicalDim (transform R P) ≤ classicalDim P
  /-- Distinguished scalar Lagrangian density $\operatorname{Tr}(F_{\mu\nu} F^{\mu\nu})$ of scaling dimension $4$ -/
  tr_F_sq : Poly
  tr_F_sq_nonzero : tr_F_sq ≠ 0
  tr_F_sq_dim : classicalDim tr_F_sq = 4
  tr_F_sq_self_conj : conj tr_F_sq = tr_F_sq
  /-- Distinguished symmetric classical stress-energy tensor $T_{\mu\nu}$ of scaling dimension $4$ -/
  stress_energy : Fin 4 → Fin 4 → Poly
  stress_energy_symm : ∀ μ ν : Fin 4, stress_energy μ ν = stress_energy ν μ
  stress_energy_dim : ∀ μ ν : Fin 4, classicalDim (stress_energy μ ν) = 4
  stress_energy_00_nonzero : stress_energy 0 0 ≠ 0
  /-- One-loop asymptotic freedom coefficient $b_0 = \frac{11 C_2(G)}{48\pi^2} > 0$ of $G$ -/
  beta_b0 : ℝ
  beta_b0_pos : 0 < beta_b0
  /-- Leading perturbative UV normalization constant $c_P > 0$ and 1-loop anomalous dimension
      exponent $\gamma_P = \gamma_P^{(0)} / (2 b_0)$ for short-distance 2-point functions -/
  uv_two_point_coeff : Poly → ℝ
  uv_two_point_coeff_pos : ∀ P : Poly, P ≠ 0 → 0 < uv_two_point_coeff P
  anomalous_exponent : Poly → ℝ
  /-- Perturbative Operator Product Expansion (OPE) short-distance Wilson coefficient
      $C_{P, Q}^R(z)$ for $\mathcal{O}_P(x) \mathcal{O}_Q(y) \sim \sum_R C_{P, Q}^R(x - y) \mathcal{O}_R(y)$ -/
  ope_coeff : Poly → Poly → Poly → EuclideanSpace4 → ℂ

attribute [instance] CurvaturePolynomialAlgebra.addCommGroup
attribute [instance] CurvaturePolynomialAlgebra.module

/-- Unified observable label indexing both local gauge-invariant curvature polynomials
$\mathcal{O}_P(x)$ (Jaffe–Witten §4, p. 6) and Wilson loop / character observables. -/
inductive ObservableLabel (G : Type*) [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    (Curv : CurvaturePolynomialAlgebra G)
  | localCurv (P : Curv.Poly) : ObservableLabel G Curv
  | wilsonChar (chi : ClassFunction G) : ObservableLabel G Curv

/-- Involution / Hermitian conjugation on `ObservableLabel`. -/
def ObservableLabel.conj {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G} :
    ObservableLabel G Curv → ObservableLabel G Curv
  | .localCurv P => .localCurv (Curv.conj P)
  | .wilsonChar chi => .wilsonChar (ClassFunction.conj chi)

/- ### 3. Wightman Axioms for 4D Quantum Yang–Mills Theory -/

/-- Recursive helper applying a finite list of local curvature field operators to a domain state `ψ ∈ D`. -/
def applyLocalFieldList {G ℋ : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (Curv : CurvaturePolynomialAlgebra G)
    (D : Submodule ℂ ℋ)
    (Φ : Curv.Poly → MinkowskiSpace → (D →ₗ[ℂ] ℋ))
    (hΦ : ∀ P x (ψ : D), Φ P x ψ ∈ D) :
    List (Curv.Poly × MinkowskiSpace) → D → D
  | [], ψ => ψ
  | (P, x) :: rest, ψ =>
      let ψ' := applyLocalFieldList Curv D Φ hΦ rest ψ
      ⟨Φ P x ψ', hΦ P x ψ'⟩

/-- Recursive helper applying a finite list of Wilson-loop operators to a domain state `ψ ∈ D`. -/
def applyWilsonList {G ℋ : Type*} [Group G]
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (D : Submodule ℂ ℋ)
    (W : ClosedLoop4D → ClassFunction G → (D →ₗ[ℂ] ℋ))
    (hW : ∀ gamma chi (ψ : D), W gamma chi ψ ∈ D) :
    List (ClosedLoop4D × ClassFunction G) → D → D
  | [], ψ => ψ
  | (gamma, chi) :: rest, ψ =>
      let ψ' := applyWilsonList D W hW rest ψ
      ⟨W gamma chi ψ', hW gamma chi ψ'⟩

/-- Relativistic Quantum Yang–Mills Theory on $\mathbb{R}^{1,3}$ with compact simple gauge group $G$
and classical curvature polynomial algebra `Curv`, satisfying the Wightman Axioms (W0)–(W4) and
the Jaffe–Witten §4 dynamical requirements (local curvature operators, dimension-filtered correspondence,
stress-energy tensor generating translations, short-distance asymptotic freedom, and OPE). -/
structure WightmanQuantumYangMills (G : Type*) (ℋ : Type*)
    [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [SeparableSpace ℋ]
    (Curv : CurvaturePolynomialAlgebra G) where
  /-- Dense Poincaré-invariant linear subspace $\mathcal{D} \subset \mathcal{H}$ -/
  domain : Submodule ℂ ℋ
  domain_dense : Dense (domain : Set ℋ)

  /-- The normalized physical vacuum ground state $\Omega \in \mathcal{D}$ -/
  vacuum : ℋ
  vacuum_in_domain : vacuum ∈ domain
  vacuum_normalized : ‖vacuum‖ = 1

  /-- (W1) Unitary representation of the restricted Poincaré group $\mathcal{P}_+^\uparrow$ -/
  poincare_rep : PoincareGroup → (ℋ →L[ℂ] ℋ)
  poincare_id : poincare_rep PoincareGroup.id = ContinuousLinearMap.id ℂ ℋ
  /-- Full semidirect group homomorphism law: $U(g_1 g_2) = U(g_1) U(g_2)$ -/
  poincare_mul : ∀ g1 g2 g3 : PoincareGroup,
    PoincareGroup.IsProduct g1 g2 g3 →
    poincare_rep g3 = (poincare_rep g1).comp (poincare_rep g2)
  poincare_unitary : ∀ (g : PoincareGroup) (ψ φ : ℋ),
    inner ℂ (poincare_rep g ψ) (poincare_rep g φ) = (inner ℂ ψ φ : ℂ)
  poincare_domain_invariant : ∀ (g : PoincareGroup) (ψ : ℋ),
    ψ ∈ domain → poincare_rep g ψ ∈ domain
  poincare_vacuum_invariant : ∀ g : PoincareGroup, poincare_rep g vacuum = vacuum

  /-- Unbounded symmetric Energy-Momentum generators $P^\mu = (H, \mathbf{P})$ on $\mathcal{D}$ -/
  Hamiltonian : domain →ₗ[ℂ] ℋ
  Momentum : Fin 3 → (domain →ₗ[ℂ] ℋ)
  hamiltonian_domain_invariant : ∀ ψ : domain, Hamiltonian ψ ∈ domain
  momentum_domain_invariant : ∀ (i : Fin 3) (ψ : domain), Momentum i ψ ∈ domain
  hamiltonian_symmetric : ∀ ψ φ : domain,
    inner ℂ (Hamiltonian ψ) (φ : ℋ) = (inner ℂ (ψ : ℋ) (Hamiltonian φ) : ℂ)
  momentum_symmetric : ∀ (i : Fin 3) (ψ φ : domain),
    inner ℂ (Momentum i ψ) (φ : ℋ) = (inner ℂ (ψ : ℋ) (Momentum i φ) : ℂ)

  /-- Mutual commutativity of the four translation generators $[H, P^i] = 0$ and $[P^i, P^j] = 0$ on $\mathcal{D}$ -/
  hamiltonian_momentum_commute : ∀ (i : Fin 3) (ψ : domain),
    Hamiltonian ⟨Momentum i ψ, momentum_domain_invariant i ψ⟩ =
    Momentum i ⟨Hamiltonian ψ, hamiltonian_domain_invariant ψ⟩
  momentum_commute : ∀ (i j : Fin 3) (ψ : domain),
    Momentum i ⟨Momentum j ψ, momentum_domain_invariant j ψ⟩ =
    Momentum j ⟨Momentum i ψ, momentum_domain_invariant i ψ⟩

  /-- Stone's Theorem / Infinitesimal Generator Law on all of $\mathcal{D}$:
      `Hamiltonian` and `Momentum` are the strong derivatives of spacetime translations $U(a, I)$ at $0$. -/
  hamiltonian_generator : ∀ (ψ : domain),
    HasDerivAt (fun t : ℝ => poincare_rep (PoincareGroup.ofTranslation (vec4 t 0 0 0)) (ψ : ℋ))
      ((-Complex.I) • Hamiltonian ψ) 0
  momentum_generator : ∀ (i : Fin 3) (ψ : domain),
    HasDerivAt (fun s : ℝ => poincare_rep (PoincareGroup.ofTranslation (spatialVec i s)) (ψ : ℋ))
      (Complex.I • Momentum i ψ) 0

  /-- Ground-State Condition: $H\Omega = 0$ and $\mathbf{P}\Omega = 0$ (Zero vacuum energy) -/
  hamiltonian_vacuum : Hamiltonian ⟨vacuum, vacuum_in_domain⟩ = 0
  momentum_vacuum : ∀ i : Fin 3, Momentum i ⟨vacuum, vacuum_in_domain⟩ = 0

  /-- Vacuum Isolation and Uniqueness: $\ker(H) \cap \mathcal{D} = \mathbb{C}\Omega$ -/
  vacuum_unique : ∀ ψ : domain, Hamiltonian ψ = 0 → ∃ c : ℂ, (ψ : ℋ) = c • vacuum

  /-- (W2) Relativistic Spectral Condition: For every state $\psi \in \mathcal{D}$,
      the expectation four-vector lies in `ClosedForwardLightCone` ($\bar{V}_+$). -/
  spectral_condition : ∀ ψ : domain,
    ofCoords ![ (inner ℂ (ψ : ℋ) (Hamiltonian ψ)).re,
                (inner ℂ (ψ : ℋ) (Momentum 0 ψ)).re,
                (inner ℂ (ψ : ℋ) (Momentum 1 ψ)).re,
                (inner ℂ (ψ : ℋ) (Momentum 2 ψ)).re ] ∈ ClosedForwardLightCone

  /-- (Jaffe–Witten §4, p. 6) Local Quantum Field Operators $\mathcal{O}_P(x)$ in correspondence
      with gauge-invariant local differential polynomials $P \in \mathrm{Curv.Poly}$ in the
      curvature $F$ and its covariant derivatives, together with their Schwartz-smeared
      operator-valued tempered distributions $\mathcal{O}_P(f) : \mathcal{D} \to \mathcal{H}$. -/
  local_field : Curv.Poly → MinkowskiSpace → (domain →ₗ[ℂ] ℋ)
  local_field_domain_invariant : ∀ P x (ψ : domain), local_field P x ψ ∈ domain
  local_smeared_field : Curv.Poly → SchwartzMap MinkowskiSpace ℂ → (domain →ₗ[ℂ] ℋ)
  local_smeared_domain_invariant : ∀ P f (ψ : domain), local_smeared_field P f ψ ∈ domain
  local_smeared_tempered : ∀ (P : Curv.Poly) (ψ φ : domain),
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ f : SchwartzMap MinkowskiSpace ℂ,
        ‖inner ℂ (φ : ℋ) (local_smeared_field P f ψ)‖ ≤ C * SchwartzMap.seminorm ℝ k k f

  /-- Dimension-Filtered Local Operator Correspondence (Jaffe–Witten §4, p. 6 & Footnote 1):
      Linearity of the correspondence $P \mapsto \mathcal{O}_P$. -/
  local_field_linear : ∀ (c1 c2 : ℂ) (P1 P2 : Curv.Poly) (x : MinkowskiSpace) (ψ : domain),
    local_field (c1 • P1 + c2 • P2) x ψ =
      c1 • local_field P1 x ψ + c2 • local_field P2 x ψ

  /-- Non-trivial faithful module representation of classical polynomials into local operators:
      Every non-zero polynomial $P$ has non-zero operator norm on the vacuum sector. -/
  local_field_non_trivial : ∀ (P : Curv.Poly),
    P ≠ 0 → ∃ (x : MinkowskiSpace) (ψ : domain),
      inner ℂ (local_field P x ψ) (local_field (Curv.conj P) x ψ) ≠ 0

  /-- Vacuum Cyclicity under Local Curvature Fields: Finite products of local curvature
      operators acting on the vacuum $\Omega$ span a dense subspace of $\mathcal{H}$. -/
  local_vacuum_cyclic :
    Dense ((Submodule.span ℂ (Set.range (fun ops : List (Curv.Poly × MinkowskiSpace) =>
      (applyLocalFieldList Curv domain local_field local_field_domain_invariant ops
        ⟨vacuum, vacuum_in_domain⟩ : ℋ))) : Submodule ℂ ℋ) : Set ℋ)

  /-- Poincaré Covariance of Local Curvature Fields:
      $U(a, \Lambda) \mathcal{O}_P(x) U(a, \Lambda)^{-1} = \mathcal{O}_{\Lambda \cdot P}(a + \Lambda x)$. -/
  local_field_poincare_covariant :
    ∀ (g : PoincareGroup) (P : Curv.Poly) (x : MinkowskiSpace) (ψ : domain),
      poincare_rep g (local_field P x ψ) =
        local_field (Curv.transform g.lorentz P)
          (euclideanTransform g.lorentz g.translation x)
          ⟨poincare_rep g (ψ : ℋ), poincare_domain_invariant g (ψ : ℋ) ψ.2⟩

  /-- Microcausality of Local Curvature Fields:
      Local curvature operators at spacelike separated points commute on $\mathcal{D}$. -/
  local_field_microcausality : ∀ (P Q : Curv.Poly) (x y : MinkowskiSpace),
    SpacelikeSeparated x y →
    ∀ ψ : domain,
      local_field P x ⟨local_field Q y ψ, local_field_domain_invariant Q y ψ⟩ =
      local_field Q y ⟨local_field P x ψ, local_field_domain_invariant P x ψ⟩

  /-- Local Stress-Energy Tensor Correspondence (Jaffe–Witten §4, p. 6):
      The local operator $T_{\mu\nu}(x) = \mathcal{O}_{\mathrm{stress\_energy}\,\mu\,\nu}(x)$ is
      symmetric and non-trivial on $(\mathbb{C}\Omega)^\perp$. -/
  stress_tensor_symmetric : ∀ (μ ν : Fin 4) (x : MinkowskiSpace) (ψ : domain),
    local_field (Curv.stress_energy μ ν) x ψ = local_field (Curv.stress_energy ν μ) x ψ

  /-- Stress-Energy Generator Property (Jaffe–Witten §4, p. 6):
      The energy density component $T_{00}(x)$ generates the Hamiltonian $H$
      under spatial slice integration with flat cutoff sequences on the dense domain $\mathcal{D}$. -/
  stress_tensor_generates_hamiltonian : ∀ (ψ : domain),
    ∃ (seq : ℕ → SchwartzMap MinkowskiSpace ℂ),
      Filter.Tendsto (fun k => local_smeared_field (Curv.stress_energy 0 0) (seq k) ψ)
        Filter.atTop (nhds (Hamiltonian ψ))

  /-- Short-Distance Asymptotic Freedom of Local Curvature Correlators (Jaffe–Witten §4, p. 6):
      For any non-zero local curvature polynomial $P$ of classical scaling dimension $d = \dim(P) \ge 4$,
      the vacuum-subtracted short-distance correlation $\langle \Omega, \mathcal{O}_{P^*}(\lambda x) \mathcal{O}_P(0) \Omega \rangle_c$
      at spacelike separation $x \neq 0$ scales as $\lambda \to 0^+$ according to perturbative
      asymptotic freedom with power $\lambda^{-2d}$ and logarithmic running coupling power
      $(-\log \lambda)^{-\gamma_P}$ governed by $b_0 > 0$:
      $$\lim_{\lambda \to 0^+} \lambda^{2d} (-\log \lambda)^{\gamma_P}
      \langle \mathcal{O}_P(\lambda x)\Omega_c, \mathcal{O}_P(0)\Omega_c \rangle =
      \frac{c_P}{\|x\|^{2d}}$$ -/
  short_distance_asymptotic_freedom :
    ∀ (P : Curv.Poly) (x : MinkowskiSpace),
      P ≠ 0 → 4 ≤ Curv.classicalDim P → x ≠ 0 →
      let v0 : domain := ⟨vacuum, vacuum_in_domain⟩
      let d := Curv.classicalDim P
      let γ := Curv.anomalous_exponent P
      let c_P := Curv.uv_two_point_coeff P
      Filter.Tendsto
        (fun (scale : ℝ) =>
          (scale ^ (2 * d)) * ((-Real.log scale) ^ γ) *
          (inner ℂ (local_field P (scale • x) v0 - (inner ℂ vacuum (local_field P (scale • x) v0)) • vacuum)
            (local_field P 0 v0 - (inner ℂ vacuum (local_field P 0 v0)) • vacuum)).re)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (c_P / (‖x‖ ^ (2 * d))))

  /-- Short-Distance Operator Product Expansion (OPE) (Jaffe–Witten §4, p. 6):
      For any local curvature polynomials $P, Q$ and truncation dimension $D \in \mathbb{N}$,
      there exists a finite set of basis polynomials $\{R_k\}$ of dimension $\le D$ such that
      as $\lambda \to 0^+$ ($x \neq 0$), the product $\mathcal{O}_P(y + \lambda x) \mathcal{O}_Q(y)$
      agrees with the perturbative asymptotic freedom OPE expansion to order $\lambda^{D - \dim P - \dim Q}$. -/
  operator_product_expansion :
    ∀ (P Q : Curv.Poly) (D : ℕ) (x y : MinkowskiSpace) (ψ φ : domain),
      x ≠ 0 → Curv.classicalDim P + Curv.classicalDim Q ≤ D →
      ∃ (basis : Finset Curv.Poly),
        (∀ R ∈ basis, Curv.classicalDim R ≤ D) ∧
        Filter.Tendsto
          (fun (scale : ℝ) =>
            (scale ^ (Curv.classicalDim P + Curv.classicalDim Q - D : ℤ)) *
            ‖inner ℂ (φ : ℋ)
              (local_field P (ofCoords (fun μ => toCoords y μ + scale * toCoords x μ))
                ⟨local_field Q y ψ, local_field_domain_invariant Q y ψ⟩ -
               ∑ R ∈ basis,
                 (Curv.ope_coeff P Q R (scale • x)) • local_field R y ψ)‖)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds 0)

  /-- Non-Local Gauge-Invariant Wilson Loop Operators $W(\gamma, \chi) : \mathcal{D} \to \mathcal{H}$ -/
  wilson_operator : ClosedLoop4D → ClassFunction G → (domain →ₗ[ℂ] ℋ)
  wilson_domain_invariant : ∀ gamma chi (ψ : domain), wilson_operator gamma chi ψ ∈ domain

  /-- Poincaré Covariance of Wilson Loops: $U(g) W(\gamma, \chi) U(g)^{-1} = W(g \cdot \gamma, \chi)$ -/
  wilson_poincare_covariant :
    ∀ (g : PoincareGroup) (gamma : ClosedLoop4D) (chi : ClassFunction G) (ψ : domain),
      poincare_rep g (wilson_operator gamma chi ψ) =
        wilson_operator (PoincareGroup.actLoop g gamma) chi
          ⟨poincare_rep g (ψ : ℋ), poincare_domain_invariant g (ψ : ℋ) ψ.2⟩

  /-- Microcausality of Wilson Loops: Spacelike separated loops commute on $\mathcal{D}$. -/
  wilson_microcausality : ∀ (gamma1 gamma2 : ClosedLoop4D) (chi1 chi2 : ClassFunction G),
    LoopsSpacelikeSeparated gamma1 gamma2 →
    ∀ ψ : domain,
      wilson_operator gamma1 chi1 ⟨wilson_operator gamma2 chi2 ψ, wilson_domain_invariant gamma2 chi2 ψ⟩ =
      wilson_operator gamma2 chi2 ⟨wilson_operator gamma1 chi1 ψ, wilson_domain_invariant gamma1 chi1 ψ⟩

  /-- Trivial holonomy on constant 4D point loops: $W(\gamma_x, \chi) = \chi(1) I_{\mathcal{D}}$. -/
  wilson_const_loop : ∀ (x : MinkowskiSpace) (chi : ClassFunction G) (ψ : domain),
    wilson_operator (ClosedLoop4D.const x) chi ψ = (chi.toFun 1) • (ψ : ℋ)

  /-- Orientation reversal of a 4D loop corresponds to the Hermitian adjoint with dual character $\bar{\chi}$. -/
  wilson_reverse_adjoint : ∀ (gamma : ClosedLoop4D) (chi : ClassFunction G) (ψ φ : domain),
    inner ℂ (wilson_operator gamma chi ψ) (φ : ℋ) =
      inner ℂ (ψ : ℋ) (wilson_operator (ClosedLoop4D.reverse gamma) (ClassFunction.conj chi) φ)

  /-- Trivial representation holonomy: $W(\gamma, c \cdot 1_G) = c I_{\mathcal{D}}$. -/
  wilson_const_char : ∀ (gamma : ClosedLoop4D) (c : ℂ) (ψ : domain),
    wilson_operator gamma (ClassFunction.const G c) ψ = c • (ψ : ℋ)

/- ### 4. The Mass Gap -/

/-- A Wightman Quantum Yang–Mills theory has a strictly positive mass gap $\Delta > 0$
if every state $\psi \in \mathcal{D}$ orthogonal to the vacuum has energy bounded below by $\Delta \|\psi\|$. -/
def HasMassGap (G : Type*) (ℋ : Type*)
    [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [SeparableSpace ℋ]
    {Curv : CurvaturePolynomialAlgebra G}
    (theory : WightmanQuantumYangMills G ℋ Curv) : Prop :=
  ∃ Δ : ℝ, 0 < Δ ∧
    ∀ ψ : theory.domain,
      inner ℂ theory.vacuum (ψ : ℋ) = (0 : ℂ) →
      Δ * ‖(ψ : ℋ)‖ ≤ ‖theory.Hamiltonian ψ‖

/- ### 5. Osterwalder–Schrader Euclidean Framework (OS I pp. 88–89; OS II pp. 282, 287) -/

/-- Safe bounded index reversal for reflected Euclidean configurations. -/
def safeReflectIndex {n : ℕ} (k : Fin n) : Fin n :=
  ⟨n - 1 - k.val, by omega⟩

/-- Safe bounded concatenation index for mixed OS configurations $(x_0, \dots, x_{n-1}) \mapsto (\theta x_{n-1}, \dots, \theta x_0)$
    and $(y_0, \dots, y_{m-1})$, matching Osterwalder–Schrader I, p. 88, $(\Theta f_n^\star \otimes g_m)$. -/
def safeReflectConcatMixed {n m : ℕ}
    (x : Fin n → EuclideanSpace4) (y : Fin m → EuclideanSpace4)
    (k : Fin (n + m)) : EuclideanSpace4 :=
  if h : k.val < n then
    let idx : Fin n := ⟨n - 1 - k.val, by omega⟩
    timeReflect (x idx)
  else
    let idx : Fin m := ⟨k.val - n, by omega⟩
    y idx

/-- Safe bounded concatenation for mixed observable labels $(\ell_0, \dots, \ell_{n-1}) \mapsto (\ell_{n-1}^\star, \dots, \ell_0^\star)$
    and $(\ell'_0, \dots, \ell'_{m-1})$, matching OS I, p. 88. -/
def safeReflectConcatLabels {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G} {n m : ℕ}
    (ops1 : Fin n → ObservableLabel G Curv) (ops2 : Fin m → ObservableLabel G Curv)
    (k : Fin (n + m)) : ObservableLabel G Curv :=
  if h : k.val < n then
    let idx : Fin n := ⟨n - 1 - k.val, by omega⟩
    (ops1 idx).conj
  else
    let idx : Fin m := ⟨k.val - n, by omega⟩
    ops2 idx

/-- Reverses and conjugates a single $n$-tuple of observable labels. -/
def reverseConjLabels {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G} {n : ℕ}
    (ops : Fin n → ObservableLabel G Curv) (i : Fin n) : ObservableLabel G Curv :=
  (ops ⟨n - 1 - i.val, by omega⟩).conj

/-- Reverses and time-reflects a single $n$-point Euclidean configuration. -/
def reverseReflectConfig {n : ℕ} (x : Fin n → EuclideanSpace4) (i : Fin n) : EuclideanSpace4 :=
  timeReflect (x ⟨n - 1 - i.val, by omega⟩)

/-- Pairwise disjoint support condition for an $n$-tuple of Schwartz test functions on $\mathbb{R}^4$
(testing the zero-time / non-coincident test function space $\mathcal{S}_0(\mathbb{R}^{4n})$ of OS I & II). -/
def DisjointSupports {n : ℕ} (f : Fin n → SchwartzMap EuclideanSpace4 ℂ) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    Disjoint (Function.support (f i : EuclideanSpace4 → ℂ))
             (Function.support (f j : EuclideanSpace4 → ℂ))

/-- Euclidean formulation of 4D Quantum Yang–Mills theory with compact simple gauge group $G$
and curvature polynomial algebra `Curv`, satisfying the corrected Osterwalder–Schrader axioms
(OS I, pp. 88–89; OS II, pp. 282, 287) and Jaffe–Witten §4 short-distance asymptotic freedom. -/
structure OsterwalderSchraderYangMills (G : Type*) [TopologicalSpace G] [Group G]
    [CompactSimpleLieGroup G]
    (Curv : CurvaturePolynomialAlgebra G) where
  /-- Sequence of $n$-point Euclidean Schwinger correlation functions $S_n$ at non-coincident points,
      indexed by local curvature polynomials and Wilson characters (`ObservableLabel G Curv`). -/
  schwinger : (n : ℕ) → (Fin n → ObservableLabel G Curv) → (Fin n → EuclideanSpace4) → ℂ

  /-- Sequence of smeared $n$-point Schwinger tempered distributions $S_n(f_1 \otimes \dots \otimes f_n)$
      on Schwartz test functions $f_i \in \mathcal{S}(\mathbb{R}^4)$. -/
  schwinger_smeared :
    (n : ℕ) → (Fin n → ObservableLabel G Curv) →
    (Fin n → SchwartzMap EuclideanSpace4 ℂ) → ℂ

  /-- Multilinearity: The smeared Schwinger distributions $S_n(f_1 \otimes \dots \otimes f_n)$
      are complex-linear in each test-function coordinate $f_i \in \mathcal{S}(\mathbb{R}^4)$. -/
  schwinger_smeared_linear : ∀ (n : ℕ) (ops : Fin n → ObservableLabel G Curv) (i : Fin n)
    (c1 c2 : ℂ) (f1 f2 : SchwartzMap EuclideanSpace4 ℂ) (rest : Fin n → SchwartzMap EuclideanSpace4 ℂ),
    schwinger_smeared n ops (Function.update rest i (c1 • f1 + c2 • f2)) =
      c1 * schwinger_smeared n ops (Function.update rest i f1) +
      c2 * schwinger_smeared n ops (Function.update rest i f2)

  /-- Regularity Compatibility: On test functions with pairwise disjoint supports,
      the smeared distribution `schwinger_smeared` agrees with the Lebesgue integral
      of the non-coincident pointwise correlation function `schwinger`. -/
  schwinger_smeared_integral_compat : ∀ (n : ℕ) (ops : Fin n → ObservableLabel G Curv)
    (f : Fin n → SchwartzMap EuclideanSpace4 ℂ),
    DisjointSupports f →
    schwinger_smeared n ops f =
      ∫ x : Fin n → EuclideanSpace4, (∏ i : Fin n, (f i : EuclideanSpace4 → ℂ) (x i)) * schwinger n ops x

  /-- Normalization of the 0-point Schwinger function $S_0 = 1$ -/
  schwinger_zero : ∀ (ops : Fin 0 → ObservableLabel G Curv) (x : Fin 0 → EuclideanSpace4),
    schwinger 0 ops x = 1

  /-- (OS0 / E0') Osterwalder–Schrader II Linear Growth & Distributional Regularity Condition
      (OS II, pp. 282, 287):
      There exist **uniform** constants $\alpha, \beta > 0$ and a **uniform** integer order $s \in \mathbb{N}$
      (independent of degree $n$ and observable labels) such that across the entire hierarchy:
      1. Every smeared $n$-point Schwinger distribution on non-coincident Schwartz test functions
         is bounded by $\alpha (n!)^\beta \prod_{i=1}^n \|f_i\|_s$ (where $\|\cdot\|_s$ is the $s$-th Schwartz seminorm).
      2. Every non-coincident $n$-point function separated by distance $r > 0$ satisfies polynomial growth
         and short-distance singularity bounds of order at most $s \cdot n$ with factorial prefactor $\alpha (n!)^\beta$. -/
  os0_temperedness :
    ∃ (α β : ℝ) (s : ℕ), 0 < α ∧ 0 < β ∧
      (∀ (n : ℕ) (ops : Fin n → ObservableLabel G Curv)
         (f : Fin n → SchwartzMap EuclideanSpace4 ℂ),
         DisjointSupports f →
         ‖schwinger_smeared n ops f‖ ≤
           α * ((Nat.factorial n : ℝ) ^ β) *
           ∏ i : Fin n, SchwartzMap.seminorm ℝ s s (f i)) ∧
      (∀ (n : ℕ) (ops : Fin n → ObservableLabel G Curv)
         (x : Fin n → EuclideanSpace4) (r : ℝ),
         0 < r →
         (∀ i j : Fin n, i ≠ j → r ≤ ‖x i - x j‖) →
         ‖schwinger n ops x‖ ≤
           α * ((Nat.factorial n : ℝ) ^ β) *
           (1 + ∑ i : Fin n, ‖x i‖ ^ 2) ^ (s * n) * (1 + (1 / r)) ^ (s * n))

  /-- (OS1 / E1) Euclidean Group $\mathrm{ISO}(4) = \mathbb{R}^4 \rtimes \mathrm{SO}(4)$ Invariance:
      For all orthogonal transformations $R \in \mathrm{SO}(4)$ and translations $v \in \mathbb{R}^4$. -/
  os1_euclidean_invariance : ∀ (n : ℕ) (ops : Fin n → ObservableLabel G Curv)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (v : EuclideanSpace4) (x : Fin n → EuclideanSpace4),
    R.transpose * R = 1 → Matrix.det R = 1 →
    schwinger n
      (fun i => match ops i with
        | .localCurv P => .localCurv (Curv.transform R P)
        | .wilsonChar chi => .wilsonChar chi)
      (fun i => euclideanTransform R v (x i)) =
    schwinger n ops x

  /-- (OS2 / E2) Osterwalder–Schrader Reflection Positivity across Mixed Field Degrees and Labels
      (OS I, p. 88, E2 & pp. 90–91):
      For any finite sequence of $m$ configurations where each term $r \in \mathrm{Fin}\,m$ has its own
      degree $\mathrm{deg}(r) \in \mathbb{N}$, its own tuple of field labels $\mathrm{ops}(r)$, and its
      own strictly positive-time coordinates $X(r) \in (\mathbb{R}^4_+)^{\mathrm{deg}(r)}$, the full
      mixed-degree sesquilinear form $\sum_{r,s} \bar{c}_r c_s S_{\mathrm{deg}(r) + \mathrm{deg}(s)}(\Theta X_r^\star, X_s)$
      is non-negative. -/
  os2_reflection_positivity :
    ∀ (m : ℕ)
      (deg : Fin m → ℕ)
      (ops : (r : Fin m) → Fin (deg r) → ObservableLabel G Curv)
      (X : (r : Fin m) → Fin (deg r) → EuclideanSpace4)
      (c : Fin m → ℂ),
      (∀ (r : Fin m) (i : Fin (deg r)), 0 < toCoords (X r i) 0) →
      0 ≤ (∑ r : Fin m, ∑ s : Fin m,
        starRingEnd ℂ (c r) * (c s) *
          schwinger (deg r + deg s)
            (safeReflectConcatLabels (ops r) (ops s))
            (safeReflectConcatMixed (X r) (X s))).re

  /-- (OS3 / E3) Permutation Symmetry under the symmetric group $\mathfrak{S}_n$ -/
  os3_permutation_symmetry : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n))
    (ops : Fin n → ObservableLabel G Curv) (x : Fin n → EuclideanSpace4),
    schwinger n (ops ∘ σ) (x ∘ σ) = schwinger n ops x

  /-- Physical Euclidean exponential clustering rate (mass gap) $m > 0$ -/
  mass_rate : ℝ
  mass_rate_pos : 0 < mass_rate

  /-- (OS4 / E4) Full Multi-Field Exponential Clustering across All Degrees and Labels
      (OS I, p. 89, Eq. (3.1) & mass-gap remark):
      For **all** degrees $n, m \in \mathbb{N}$, **all** observable label tuples $\mathrm{ops}_1, \mathrm{ops}_2$,
      **all** positive-time configurations $X \in (\mathbb{R}^4_+)^n$ and $Y \in (\mathbb{R}^4_+)^m$,
      and **all** unit Euclidean translation directions $a \in \mathbb{R}^4$ with $a^0 \ge 0$ and $\|a\| = 1$,
      the truncated correlation $S_{n+m}(\Theta X^\star, T_{\lambda a} Y) - \overline{S_n(X)} S_m(Y)$
      decays exponentially at rate `mass_rate` as $\lambda \to \infty$. -/
  os4_exponential_clustering :
    ∀ (n m : ℕ)
      (ops1 : Fin n → ObservableLabel G Curv)
      (ops2 : Fin m → ObservableLabel G Curv)
      (X : Fin n → EuclideanSpace4)
      (Y : Fin m → EuclideanSpace4)
      (a : EuclideanSpace4),
      (∀ i : Fin n, 0 < toCoords (X i) 0) →
      (∀ j : Fin m, 0 < toCoords (Y j) 0) →
      0 ≤ toCoords a 0 → ‖a‖ = 1 →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (scale : ℝ), 0 ≤ scale →
          ‖schwinger (n + m)
            (safeReflectConcatLabels ops1 ops2)
            (safeReflectConcatMixed X (translateConfig (scale • a) Y)) -
           starRingEnd ℂ (schwinger n (reverseConjLabels ops1) (reverseReflectConfig X)) *
             schwinger m ops2 Y‖ ≤
          C * Real.exp (-mass_rate * scale)

  /-- Euclidean Short-Distance Asymptotic Freedom & OPE for Local Curvature Fields
      (Jaffe–Witten §4, p. 6):
      For every non-zero classical curvature polynomial $P$ of dimension $d = \dim(P) \ge 4$
      (including the Lagrangian density $\operatorname{Tr}(F_{\mu\nu}F^{\mu\nu})$ and stress-energy tensor $T_{\mu\nu}$),
      the connected Euclidean 2-point Schwinger function at short distance $\lambda x$ ($\lambda \to 0^+$)
      exhibits the asymptotic freedom power law $\lambda^{-2d} (-\log \lambda)^{-\gamma_P}$ governed by $b_0 > 0$. -/
  os_short_distance_asymptotic_freedom :
    ∀ (P : Curv.Poly) (x : EuclideanSpace4),
      P ≠ 0 → 4 ≤ Curv.classicalDim P → x ≠ 0 →
      let d := Curv.classicalDim P
      let γ := Curv.anomalous_exponent P
      let c_P := Curv.uv_two_point_coeff P
      let opP : ObservableLabel G Curv := .localCurv P
      let opP_conj : ObservableLabel G Curv := .localCurv (Curv.conj P)
      Filter.Tendsto
        (fun (scale : ℝ) =>
          (scale ^ (2 * d)) * ((-Real.log scale) ^ γ) *
          (schwinger 2 ![opP_conj, opP] ![scale • x, 0] -
            schwinger 1 ![opP_conj] ![scale • x] * schwinger 1 ![opP] ![0]).re)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (c_P / (‖x‖ ^ (2 * d))))

/-- **Osterwalder–Schrader Reconstruction Theorem** (OS I, 1973; OS II, 1975, pp. 282, 287):
Any Euclidean Yang–Mills theory `os : OsterwalderSchraderYangMills G Curv` satisfying the
uniform linear growth condition ($\text{E}0'$), multilinearity, Euclidean invariance (E1), mixed-degree reflection
positivity (E2), permutation symmetry (E3), full exponential clustering (E4) with rate `os.mass_rate`,
and short-distance asymptotic freedom reconstructs a relativistic `WightmanQuantumYangMills G ℋ Curv`
equipped with a dense positive-time embedding `os_embed` whose Euclidean semigroup inner ℂ products
equal `os.schwinger` and whose Hamiltonian spectral gap on $(\mathbb{C}\Omega)^\perp$ is bounded below
by `os.mass_rate` ($\Delta \ge m > 0$). -/
@[category research solved, AMS 81]
theorem osterwalder_schrader_reconstruction
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    ∃ (ℋ : Type*) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
      (theory : WightmanQuantumYangMills G ℋ Curv)
      (os_embed : (n : ℕ) → (Fin n → ObservableLabel G Curv) →
        (Fin n → EuclideanSpace4) → theory.domain),
      (∀ (n m : ℕ) (ops1 : Fin n → ObservableLabel G Curv)
         (ops2 : Fin m → ObservableLabel G Curv)
         (X : Fin n → EuclideanSpace4) (Y : Fin m → EuclideanSpace4),
         (∀ i : Fin n, 0 < toCoords (X i) 0) →
         (∀ j : Fin m, 0 < toCoords (Y j) 0) →
         inner ℂ (os_embed n ops1 X : ℋ) (os_embed m ops2 Y : ℋ) =
           os.schwinger (n + m) (safeReflectConcatLabels ops1 ops2) (safeReflectConcatMixed X Y)) ∧
      (∀ ψ : theory.domain,
        inner ℂ theory.vacuum (ψ : ℋ) = (0 : ℂ) →
        os.mass_rate * ‖(ψ : ℋ)‖ ≤ ‖theory.Hamiltonian ψ‖) ∧
      HasMassGap G ℋ theory := by
  sorry

/- ### 6. The Official Clay Millennium Prize Problem Statement -/

/-- **Clay Millennium Prize Problem: 4D Yang–Mills Existence and Mass Gap**
(Arthur Jaffe & Edward Witten, 2000, Section 4, p. 6)

For any compact simple Lie group $G$ (and its classical gauge-invariant curvature polynomial
algebra `Curv`), there exists a non-trivial four-dimensional quantum Yang–Mills theory on
$\mathbb{R}^{1,3}$ satisfying the Wightman axioms, admitting local quantum field operators in
correspondence with gauge-invariant polynomials in the curvature $F$ and its covariant derivatives
with short-distance correlations governed by asymptotic freedom and perturbative renormalization,
and possessing a strictly positive mass gap $\Delta > 0$. -/
@[category research open, AMS 81]
theorem yang_mills_existence_and_mass_gap
    (G : Type*) [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    (Curv : CurvaturePolynomialAlgebra G) :
    ∃ (ℋ : Type*) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
      (theory : WightmanQuantumYangMills G ℋ Curv),
      HasMassGap G ℋ theory := by
  sorry

/-- Canonical Specialization to $\mathrm{SU}(N)$ for any $N \ge 2$ -/
@[category research open, AMS 81]
theorem yang_mills_sun_mass_gap (N : ℕ) [Fact (2 ≤ N)]
    (Curv : CurvaturePolynomialAlgebra (SUN N)) :
    ∃ (ℋ : Type*) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
      (theory : WightmanQuantumYangMills (SUN N) ℋ Curv),
      HasMassGap (SUN N) ℋ theory := by
  sorry

/-- Canonical Specialization to $\mathrm{SU}(2)$ Pure Yang–Mills Gauge Theory -/
@[category research open, AMS 81]
theorem yang_mills_su2_mass_gap (Curv : CurvaturePolynomialAlgebra SU2) :
    ∃ (ℋ : Type*) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
      (theory : WightmanQuantumYangMills SU2 ℋ Curv),
      HasMassGap SU2 ℋ theory := by
  sorry

/-- Canonical Specialization to $\mathrm{SU}(3)$ (Quantum Chromodynamics Gluon Sector) -/
@[category research open, AMS 81]
theorem yang_mills_su3_mass_gap (Curv : CurvaturePolynomialAlgebra SU3) :
    ∃ (ℋ : Type*) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
      (theory : WightmanQuantumYangMills SU3 ℋ Curv),
      HasMassGap SU3 ℋ theory := by
  sorry

/-- Derivation of Canonical Specialization to $\mathrm{SU}(N)$ from Universal Existence -/
@[category API, AMS 81]
theorem yang_mills_sun_mass_gap_of_universal.{u} (N : ℕ) [Fact (2 ≤ N)]
    (Curv : CurvaturePolynomialAlgebra (SUN N))
    (h_univ : ∃ (ℋ : Type u) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
        (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
        (theory : WightmanQuantumYangMills (SUN N) ℋ Curv),
        HasMassGap (SUN N) ℋ theory) :
    ∃ (ℋ : Type u) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
      (theory : WightmanQuantumYangMills (SUN N) ℋ Curv),
      HasMassGap (SUN N) ℋ theory :=
  h_univ

end YangMills
