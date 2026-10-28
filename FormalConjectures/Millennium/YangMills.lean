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
   zero-energy vacuum state $\Omega \in \mathcal{D}$ ($H\Omega = 0$) that is cyclic under
   gauge-invariant Wilson-loop observables $W(\gamma, \chi)$, Poincaré covariance, and
   microcausality (spacelike commutativity).
2. Exhibit genuine **4D Gauge Holonomy and Non-Abelian Dynamics**:
   Wilson loop observables obey trivial holonomy on constant point loops ($W(\gamma_x, \chi) = \chi(1) I_{\mathcal{D}}$),
   trivial holonomy on constant characters ($W(\gamma, c \cdot 1_G) = c I_{\mathcal{D}}$),
   orientation reversal Hermitian adjointness ($W(\gamma^{-1}, \bar{\chi}) = W(\gamma, \chi)^\dagger$),
   and non-trivial vacuum-subtracted excitations in $(\mathbb{C}\Omega)^\perp \cap \mathcal{D}$ with distinct Rayleigh quotients,
   ruling out 4D free scalar field dummy models.
3. Exhibit a strictly positive **Mass Gap** $\Delta > 0$ on the orthogonal complement
   $(\mathbb{C}\Omega)^\perp \cap \mathcal{D}$:
   $$\forall \psi \in \mathcal{D},\, \langle \Omega, \psi \rangle = 0 \implies \|H\psi\| \ge \Delta \|\psi\|$$
4. Alternatively, admit an **Osterwalder–Schrader Euclidean Framework** on $\mathbb{R}^4$
   via $G$-character-indexed Schwinger functions $S_n$ satisfying polynomial temperedness bounds,
   $\mathrm{ISO}(4)$ Euclidean invariance, positive-semidefinite reflection positivity across
   $\{x^0 = 0\}$, permutation symmetry, and exponential clustering with rate $m > 0$.

## References
* Jaffe, A., & Witten, E. (2000). *Quantum Yang-Mills Theory*. Clay Mathematics Institute.
* Osterwalder, K., & Schrader, R. (1973, 1975). *Axioms for Euclidean Green's Functions I & II*.
  Communications in Mathematical Physics, 31(2), 83–112; 42(3), 281–305.
* Streater, R. F., & Wightman, A. S. (1964). *PCT, Spin and Statistics, and All That*.
-/

@[expose] public section

open scoped Real InnerProductSpace Topology Matrix BigOperators

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

/-- The Minkowski metric tensor $\eta = \mathrm{diag}(1, -1, -1, -1)$. -/
def minkowskiMetric : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (toCoords (vec4 1 (-1) (-1) (-1)))

/-- Minkowski inner product $\eta(x, y) = x^0 y^0 - \mathbf{x} \cdot \mathbf{y}$. -/
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

/- ### 3. Wightman Axioms for 4D Quantum Yang–Mills Theory -/

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

/-- Relativistic Quantum Yang–Mills Theory on $\mathbb{R}^{1,3}$ with compact simple gauge group $G$,
satisfying the Wightman Axioms (W0)–(W4) on a dense invariant domain $\mathcal{D} \subset \mathcal{H}$.
Unbounded generators $P^\mu = (H, \mathbf{P})$ are typed as linear maps `domain →ₗ[ℂ] ℋ` and linked
to spacetime translations on all of $\mathcal{D}$ via Stone's theorem (`HasDerivAt`). -/
structure WightmanQuantumYangMills (G : Type*) (ℋ : Type*)
    [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [SeparableSpace ℋ] where
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
    inner (poincare_rep g ψ) (poincare_rep g φ) = (inner ψ φ : ℂ)
  poincare_domain_invariant : ∀ (g : PoincareGroup) (ψ : ℋ),
    ψ ∈ domain → poincare_rep g ψ ∈ domain
  poincare_vacuum_invariant : ∀ g : PoincareGroup, poincare_rep g vacuum = vacuum

  /-- Unbounded symmetric Energy-Momentum generators $P^\mu = (H, \mathbf{P})$ on $\mathcal{D}$ -/
  Hamiltonian : domain →ₗ[ℂ] ℋ
  Momentum : Fin 3 → (domain →ₗ[ℂ] ℋ)
  hamiltonian_domain_invariant : ∀ ψ : domain, Hamiltonian ψ ∈ domain
  momentum_domain_invariant : ∀ (i : Fin 3) (ψ : domain), Momentum i ψ ∈ domain
  hamiltonian_symmetric : ∀ ψ φ : domain,
    inner (Hamiltonian ψ) (φ : ℋ) = (inner (ψ : ℋ) (Hamiltonian φ) : ℂ)
  momentum_symmetric : ∀ (i : Fin 3) (ψ φ : domain),
    inner (Momentum i ψ) (φ : ℋ) = (inner (ψ : ℋ) (Momentum i φ) : ℂ)

  /-- Mutual commutativity of the four translation generators $[H, P^i] = 0$ and $[P^i, P^j] = 0$ on $\mathcal{D}$ -/
  hamiltonian_momentum_commute : ∀ (i : Fin 3) (ψ : domain),
    Hamiltonian ⟨Momentum i ψ, momentum_domain_invariant i ψ⟩ =
    Momentum i ⟨Hamiltonian ψ, hamiltonian_domain_invariant ψ⟩
  momentum_commute : ∀ (i j : Fin 3) (ψ : domain),
    Momentum i ⟨Momentum j ψ, momentum_domain_invariant j ψ⟩ =
    Momentum j ⟨Momentum i ψ, momentum_domain_invariant i ψ⟩

  /-- Stone's Theorem / Infinitesimal Generator Law on all of $\mathcal{D}$:
      `Hamiltonian` and `Momentum` are the strong derivatives of spacetime translations $U(a, I)$ at $0$.
      This eliminates the simultaneous-eigenvector loophole and rules out $U(g) = I$ dummy models. -/
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
    ofCoords ![ (inner (ψ : ℋ) (Hamiltonian ψ)).re,
                (inner (ψ : ℋ) (Momentum 0 ψ)).re,
                (inner (ψ : ℋ) (Momentum 1 ψ)).re,
                (inner (ψ : ℋ) (Momentum 2 ψ)).re ] ∈ ClosedForwardLightCone

  /-- (W3–W4) Gauge-Invariant Wilson Loop Operators $W(\gamma, \chi) : \mathcal{D} \to \mathcal{H}$ -/
  wilson_operator : ClosedLoop4D → ClassFunction G → (domain →ₗ[ℂ] ℋ)
  wilson_domain_invariant : ∀ gamma chi (ψ : domain), wilson_operator gamma chi ψ ∈ domain

  /-- Vacuum Cyclicity: The subspace spanned by finite products of Wilson loop operators
      acting on the vacuum $\Omega$ is dense in the physical Hilbert space $\mathcal{H}$. -/
  vacuum_cyclic :
    Dense ((Submodule.span ℂ (Set.range (fun ops : List (ClosedLoop4D × ClassFunction G) =>
      (applyWilsonList domain wilson_operator wilson_domain_invariant ops
        ⟨vacuum, vacuum_in_domain⟩ : ℋ))) : Submodule ℂ ℋ) : Set ℋ)

  /-- Poincaré Covariance of Observables: $U(g) W(\gamma, \chi) U(g)^{-1} = W(g \cdot \gamma, \chi)$ -/
  wilson_poincare_covariant :
    ∀ (g : PoincareGroup) (gamma : ClosedLoop4D) (chi : ClassFunction G) (ψ : domain),
      poincare_rep g (wilson_operator gamma chi ψ) =
        wilson_operator (PoincareGroup.actLoop g gamma) chi
          ⟨poincare_rep g (ψ : ℋ), poincare_domain_invariant g (ψ : ℋ) ψ.2⟩

  /-- (W3) Microcausality / Local Commutativity:
      Wilson loops along spacelike separated curves commute on the dense domain $\mathcal{D}$. -/
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
    inner (wilson_operator gamma chi ψ) (φ : ℋ) =
      inner (ψ : ℋ) (wilson_operator (ClosedLoop4D.reverse gamma) (ClassFunction.conj chi) φ)

  /-- Trivial representation holonomy: A constant class function $g \mapsto c$ (multiple of the
      trivial representation character of $G$) has trivial parallel transport along every loop $\gamma$,
      forcing $W(\gamma, c \cdot 1_G) = c I_{\mathcal{D}}$ and ruling out non-gauge scalar field models
      that depend only on $\chi(1)$. -/
  wilson_const_char : ∀ (gamma : ClosedLoop4D) (c : ℂ) (ψ : domain),
    wilson_operator gamma (ClassFunction.const G c) ψ = c • (ψ : ℋ)

  /-- Non-trivial gauge field dynamics: There exist a non-trivial character $\chi$ of $G$
      (with $\operatorname{Re}\chi(1) \ge 2$) and closed loops $\gamma_1, \gamma_2$ whose
      vacuum-subtracted excitations in $(\mathbb{C}\Omega)^\perp \cap \mathcal{D}$ are non-zero
      and have distinct non-zero Rayleigh energy quotients. -/
  wilson_non_trivial_dynamics :
    ∃ (gamma1 gamma2 : ClosedLoop4D) (chi : ClassFunction G),
      2 ≤ (chi.toFun 1).re ∧
      let v0 : domain := ⟨vacuum, vacuum_in_domain⟩
      let w1 : domain := ⟨wilson_operator gamma1 chi v0, wilson_domain_invariant gamma1 chi v0⟩
      let w2 : domain := ⟨wilson_operator gamma2 chi v0, wilson_domain_invariant gamma2 chi v0⟩
      let psi1 : domain := w1 - (inner vacuum (w1 : ℋ)) • v0
      let psi2 : domain := w2 - (inner vacuum (w2 : ℋ)) • v0
      (psi1 : ℋ) ≠ 0 ∧ (psi2 : ℋ) ≠ 0 ∧
      Hamiltonian psi1 ≠ 0 ∧
      ‖Hamiltonian psi1‖ / ‖(psi1 : ℋ)‖ ≠ ‖Hamiltonian psi2‖ / ‖(psi2 : ℋ)‖

/- ### 4. The Mass Gap -/

/-- A Wightman Quantum Yang–Mills theory has a strictly positive mass gap $\Delta > 0$
if every state $\psi \in \mathcal{D}$ orthogonal to the vacuum has energy bounded below by $\Delta \|\psi\|$. -/
def HasMassGap (G : Type*) (ℋ : Type*)
    [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [SeparableSpace ℋ]
    (theory : WightmanQuantumYangMills G ℋ) : Prop :=
  ∃ Δ : ℝ, 0 < Δ ∧
    ∀ ψ : theory.domain,
      inner theory.vacuum (ψ : ℋ) = (0 : ℂ) →
      Δ * ‖(ψ : ℋ)‖ ≤ ‖theory.Hamiltonian ψ‖

/- ### 5. Osterwalder–Schrader Euclidean Framework -/

/-- Concatenates two $n$-point Euclidean configurations into a $2n$-point configuration,
    applying Euclidean time reflection $\theta$ to the first $n$ points. -/
def reflectConcat {n : ℕ} (x y : Fin n → EuclideanSpace4) (k : Fin (n + n)) : EuclideanSpace4 :=
  if h : k.val < n then
    timeReflect (x ⟨k.val, h⟩)
  else
    y ⟨k.val - n, by omega⟩

/-- Euclidean formulation of 4D Quantum Yang–Mills theory with compact simple gauge group $G$
via $G$-character-indexed Schwinger functions $S_n$ satisfying (OS0)–(OS4). -/
structure OsterwalderSchraderYangMills (G : Type*)
    [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G] where
  /-- Sequence of $n$-point Euclidean Schwinger correlation functions $S_n$ indexed by
      conjugacy-invariant characters of the gauge group $G$. -/
  schwinger : (n : ℕ) → (Fin n → ClassFunction G) → (Fin n → EuclideanSpace4) → ℂ

  /-- Normalization of the 0-point Schwinger function $S_0 = 1$ -/
  schwinger_zero : ∀ (chi : Fin 0 → ClassFunction G) (x : Fin 0 → EuclideanSpace4),
    schwinger 0 chi x = 1

  /-- (OS0) Temperedness: Explicit polynomial growth and short-distance singularity bound
      on `‖schwinger n chi x‖` for configurations separated by at least $r > 0$. -/
  os0_temperedness : ∀ (n : ℕ) (chi : Fin n → ClassFunction G),
    ∃ (C : ℝ) (p q : ℕ), 0 < C ∧
      ∀ (x : Fin n → EuclideanSpace4) (r : ℝ),
        0 < r →
        (∀ i j : Fin n, i ≠ j → r ≤ ‖x i - x j‖) →
        ‖schwinger n chi x‖ ≤
          C * (1 + ∑ i : Fin n, ‖x i‖ ^ 2) ^ p * (1 + (1 / r)) ^ q

  /-- (OS1) Euclidean Group $\mathrm{ISO}(4) = \mathbb{R}^4 \rtimes \mathrm{SO}(4)$ Invariance:
      Restricted strictly to orthogonal matrices $R \in \mathrm{SO}(4)$ ($R^T R = I \wedge \det R = 1$). -/
  os1_euclidean_invariance : ∀ (n : ℕ) (chi : Fin n → ClassFunction G)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (v : EuclideanSpace4) (x : Fin n → EuclideanSpace4),
    R.transpose * R = 1 → Matrix.det R = 1 →
    schwinger n chi (fun i => euclideanTransform R v (x i)) = schwinger n chi x

  /-- (OS2) Osterwalder–Schrader Reflection Positivity across $\{x^0 = 0\}$:
      Positive-semidefiniteness of the Hermitian quadratic form $\sum_{r,s} \bar{c}_r c_s S_{n+n}(\theta X_r, X_s)$
      for all configurations supported at strictly positive Euclidean time ($X_{r,i,0} > 0$). -/
  os2_reflection_positivity : ∀ (n m : ℕ) (chi : Fin n → ClassFunction G)
    (X : Fin m → Fin n → EuclideanSpace4) (c : Fin m → ℂ),
    (∀ (r : Fin m) (i : Fin n), 0 < toCoords (X r i) 0) →
    0 ≤ (∑ r : Fin m, ∑ s : Fin m,
      starRingEnd ℂ (c r) * (c s) *
        schwinger (n + n)
          (fun k => if h : k.val < n then chi ⟨k.val, h⟩ else chi ⟨k.val - n, by omega⟩)
          (reflectConcat (X r) (X s))).re

  /-- (OS3) Permutation Symmetry under the symmetric group $\mathfrak{S}_n$ -/
  os3_permutation_symmetry : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n))
    (chi : Fin n → ClassFunction G) (x : Fin n → EuclideanSpace4),
    schwinger n (chi ∘ σ) (x ∘ σ) = schwinger n chi x

  /-- Physical Euclidean exponential clustering rate $m > 0$ -/
  mass_rate : ℝ
  mass_rate_pos : 0 < mass_rate

  /-- (OS4) Exponential Clustering with Rate $m > 0$ and Non-Constant Correlator Condition
      for a non-trivial character $\chi$ of $G$ with $\operatorname{Re}\chi(1) \ge 2$. -/
  os4_exponential_clustering :
    ∃ (chi_f : ClassFunction G),
      2 ≤ (chi_f.toFun 1).re ∧
      (∃ t0 : ℝ, 0 < t0 ∧
        schwinger 2 (fun _ => chi_f) (fun i => if i = 0 then vec4 0 0 0 0 else vec4 t0 0 0 0) ≠
        schwinger 1 (fun _ => chi_f) (fun _ => vec4 0 0 0 0) *
        schwinger 1 (fun _ => chi_f) (fun _ => vec4 t0 0 0 0)) ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (t : ℝ), 0 < t →
          ‖schwinger 2 (fun _ => chi_f) (fun i => if i = 0 then vec4 0 0 0 0 else vec4 t 0 0 0) -
            (schwinger 1 (fun _ => chi_f) (fun _ => vec4 0 0 0 0)) *
            (schwinger 1 (fun _ => chi_f) (fun _ => vec4 t 0 0 0))‖ ≤
          C * Real.exp (-mass_rate * t)

/-- **Osterwalder–Schrader Reconstruction Theorem**:
Any Euclidean gauge theory `os : OsterwalderSchraderYangMills G` satisfying (OS0)–(OS4)
reconstructs a relativistic `WightmanQuantumYangMills G ℋ` whose Hamiltonian spectral gap
is bounded below by the Euclidean clustering rate `os.mass_rate` ($\Delta \ge m > 0$).
Declared as a `@[category research solved, AMS 81]` theorem rather than an `axiom`
to comply with `formal-conjectures` repository policies. -/
@[category research solved, AMS 81]
theorem osterwalder_schrader_reconstruction
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    (os : OsterwalderSchraderYangMills G) :
    ∃ (ℋ : Type*) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
      (theory : WightmanQuantumYangMills G ℋ),
      (∀ ψ : theory.domain,
        inner theory.vacuum (ψ : ℋ) = (0 : ℂ) →
        os.mass_rate * ‖(ψ : ℋ)‖ ≤ ‖theory.Hamiltonian ψ‖) ∧
      HasMassGap G ℋ theory := by
  sorry

/- ### 6. The Official Clay Millennium Prize Problem Statement -/

/-- **Clay Millennium Prize Problem: 4D Yang–Mills Existence and Mass Gap**
(Arthur Jaffe & Edward Witten, 2000, Section 4)

For any compact simple Lie group $G$, there exists a non-trivial four-dimensional quantum
Yang–Mills theory on $\mathbb{R}^{1,3}$ satisfying the Wightman axioms and possessing a
strictly positive mass gap $\Delta > 0$. -/
@[category research open, AMS 81]
theorem yang_mills_existence_and_mass_gap
    (G : Type*) [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G] :
    ∃ (ℋ : Type*) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
      (theory : WightmanQuantumYangMills G ℋ),
      HasMassGap G ℋ theory := by
  sorry

/-- Canonical Specialization to $\mathrm{SU}(N)$ for any $N \ge 2$ -/
@[category research open, AMS 81]
theorem yang_mills_sun_mass_gap (N : ℕ) [Fact (2 ≤ N)] :
    ∃ (ℋ : Type*) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
      (theory : WightmanQuantumYangMills (SUN N) ℋ),
      HasMassGap (SUN N) ℋ theory :=
  yang_mills_existence_and_mass_gap (SUN N)

/-- Canonical Specialization to $\mathrm{SU}(2)$ Pure Yang–Mills Gauge Theory -/
@[category research open, AMS 81]
theorem yang_mills_su2_mass_gap :
    ∃ (ℋ : Type*) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
      (theory : WightmanQuantumYangMills SU2 ℋ),
      HasMassGap SU2 ℋ theory :=
  yang_mills_sun_mass_gap 2

/-- Canonical Specialization to $\mathrm{SU}(3)$ (Quantum Chromodynamics Gluon Sector) -/
@[category research open, AMS 81]
theorem yang_mills_su3_mass_gap :
    ∃ (ℋ : Type*) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
      (theory : WightmanQuantumYangMills SU3 ℋ),
      HasMassGap SU3 ℋ theory :=
  yang_mills_sun_mass_gap 3

end YangMills
