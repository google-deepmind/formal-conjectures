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
# Open Quantum Problem 27: The power of CGLMP inequalities

**Problem** (proposed by R. Gill, 2006). Consider the Bell scenario with two parties, two inputs per
party and $d$ outputs per input.

* **Part A.** Show that every face of the local polytope that is not contained in a face of the
  no-signalling polytope is of CGLMP type (Collins, Gisin, Linden, Massar and Popescu), possibly
  lifted from fewer outputs by fusing outputs together.
* **Part B.** Numerically, the observables that maximally violate the CGLMP inequality on a maximally
  entangled state are of a very specific form: measurements in the computational basis, transformed
  only by the discrete Fourier transform and diagonal unitaries (Durt, Kaszlikowski and Zukowski,
  "DKZ"). Show that this is necessarily the case. Show also that these measurements realize the
  highest resistance of the violation to noise, and the best discrimination against local realism
  in the sense of the Kullback-Leibler divergence.

This file formalizes Part B in the formulation of Formal Conjectures issue #3444: the maximally
entangled state $\Phi_d$ of $\mathbb{C}^d \otimes \mathbb{C}^d$ is fixed, and the CGLMP functional
is optimized over complete von Neumann $d$-outcome measurements (orthonormal bases), one for each
input of each party.

**Definitions.**
- `Behaviour d`, `deterministicBehaviour`, `IsLocalBehaviour`: behaviours $p(a,b \mid x,y)$ and the
  local polytope.
- `cglmpFunctional`: the CGLMP functional of the problem page,
  $E[m(A_1 - B_1)] + E[m(B_1 - A_2)] + E[m(A_2 - B_2)] + E[m(B_2 - A_1 - 1)]$ with
  $m(t) = t \bmod d$. Local models give at least $d - 1$ (`le_cglmpFunctional_of_isLocalBehaviour`);
  a smaller value is a violation. `cglmpExpr` is the form $I_d$ of Collins et al. (2002), and
  `cglmpExpr_eq_cglmpFunctional` relates the two.
- `maxEntangledState`, `densityMatrix`, `bornProb`, `quantumBehaviour`: the state $\Phi_D$ and the
  quantum behaviours $p(a,b \mid x,y) = \operatorname{Tr}[\rho (A_{x,a} \otimes B_{y,b})]$.
- `vonNeumannMeasurement`, `vonNeumannBehaviour`: the complete von Neumann measurement in the
  orthonormal basis given by the columns of a unitary $U$.
- `dkzUnitaryA`, `dkzUnitaryB`: the DKZ measurements.
- `whiteNoiseState`, `noisyVonNeumannBehaviour`: white noise,
  $\rho_v = v \, |\Phi_d\rangle\langle\Phi_d| + (1 - v) \, \mathbb{1}/d^2$.
- `statisticalStrength`: the statistical strength of van Dam, Gill and Grünwald for uniformly random
  inputs, the smallest Kullback-Leibler divergence from a local behaviour.

**Status.**
- Part A is false: Bancal, Gisin and Pironio (2010) found facets of the local polytope for $d = 4$
  that are not of CGLMP type. It is not formalized here.
- Optimality and uniqueness of the DKZ measurements (`dkz_optimal`, `dkz_unique`) and the noise
  clause for the violation of the CGLMP inequality (`dkz_noise`) are proved in Lean for
  $2 \le d \le 20$ in [MS26] (`dkz_optimal_of_le_twenty`, `dkz_unique_of_le_twenty`,
  `dkz_noise_of_le_twenty`). For $d \ge 21$, [MS26] gives a proof that also uses
  interval-arithmetic certificates checked outside Lean; it has not been refereed.
- The noise clause for the violation of local realism (all Bell inequalities) with complete von
  Neumann measurements (`dkz_noise_allBell`) is open for $d \ge 4$. It holds for $d = 2$ (Tsirelson's
  bound and Fine's theorem); [MS26] reports a computer-assisted proof for $d = 3$.
- The Kullback-Leibler clause (`dkz_klOptimal`): [MS26] reports explicit complete von Neumann
  measurements that beat DKZ for every $d \ge 4$ (for $d = 4$ first found by Y. Zhang, 2026), with
  exact certificates; $d = 3$ is open (`dkz_klOptimal_three`).

*References:*
- Open Quantum Problems, problem 27:
  <https://oqp.iqoqi.oeaw.ac.at/the-power-of-cglmp-inequalities>
- Formal Conjectures issue #3444:
  <https://github.com/google-deepmind/formal-conjectures/issues/3444>
- D. Collins, N. Gisin, N. Linden, S. Massar and S. Popescu, *Bell inequalities for arbitrarily
  high-dimensional systems*, Phys. Rev. Lett. 88, 040404 (2002).
- T. Durt, D. Kaszlikowski and M. Zukowski, *Violations of local realism with quantum systems
  described by N-dimensional Hilbert spaces up to N = 16*, Phys. Rev. A 64, 024101 (2001).
- W. van Dam, R. D. Gill and P. D. Grünwald, *The statistical strength of nonlocality proofs*,
  IEEE Trans. Inf. Theory 51, 2812 (2005), arXiv:quant-ph/0307125.
- A. Acín, T. Durt, N. Gisin and J. I. Latorre, *Quantum nonlocality in two three-level systems*,
  Phys. Rev. A 65, 052325 (2002).
- J.-D. Bancal, N. Gisin and S. Pironio, *Looking for symmetric Bell inequalities*,
  J. Phys. A 43, 385303 (2010).
- R. D. Gill, *Better Bell inequalities (passion at a distance)*, IMS Lecture Notes 55 (2007),
  arXiv:math/0610115.
- [MS26] A. Mishra and A. Senthilkumar, *Optimal CGLMP measurements in every dimension and the clauses
  of IQOQI Vienna Open Quantum Problem 27B* (2026), with the Lean proofs referred to below:
  <https://github.com/anshM123/IQOQI-OQP-27>
-/

@[expose] public section

namespace OpenQuantumProblem27

open Matrix
open scoped Kronecker

/-! ### The Bell scenario and the CGLMP functional -/

/-- A behaviour of the Bell scenario with two inputs and `d` outputs per party: `p x y a b` is the
probability $p(a, b \mid x, y)$ of Alice's output `a` and Bob's output `b` on Alice's input `x` and
Bob's input `y`. The inputs `0, 1 : Fin 2` are the inputs $1, 2$ of the problem page. -/
abbrev Behaviour (d : ℕ) := Fin 2 → Fin 2 → Fin d → Fin d → ℝ

/-- The deterministic local strategy in which Alice outputs `f x` on input `x` and Bob outputs
`g y` on input `y`: $p(a,b \mid x,y) = \delta_{a,f(x)} \delta_{b,g(y)}$. -/
noncomputable def deterministicBehaviour {d : ℕ} (f g : Fin 2 → Fin d) : Behaviour d :=
  fun x y a b => if a = f x ∧ b = g y then 1 else 0

/-- `p` lies in the local polytope: it is a convex combination of deterministic local strategies. -/
def IsLocalBehaviour {d : ℕ} (p : Behaviour d) : Prop :=
  ∃ q : (Fin 2 → Fin d) × (Fin 2 → Fin d) → ℝ, (∀ s, 0 ≤ q s) ∧ ∑ s, q s = 1 ∧
    ∀ x y a b, p x y a b = ∑ s, q s * deterministicBehaviour s.1 s.2 x y a b

/-- **The CGLMP functional**, in the form of the problem page and of issue #3444:
$$E[m(A_1 - B_1)] + E[m(B_1 - A_2)] + E[m(A_2 - B_2)] + E[m(B_2 - A_1 - 1)],$$
where $A_x$ and $B_y$ are the outputs on the inputs $x, y \in \{1, 2\}$ and
$m(t) = t \bmod d \in \{0, \dots, d - 1\}$. Every local model satisfies the CGLMP inequality
$\ge d - 1$ (`le_cglmpFunctional_of_isLocalBehaviour`); a smaller value is a violation. -/
noncomputable def cglmpFunctional {d : ℕ} (p : Behaviour d) : ℝ :=
  ∑ a : Fin d, ∑ b : Fin d,
    (p 0 0 a b * ((((a : ℕ) - (b : ℕ) : ℤ) % d : ℤ) : ℝ) +
      p 1 0 a b * ((((b : ℕ) - (a : ℕ) : ℤ) % d : ℤ) : ℝ) +
      p 1 1 a b * ((((a : ℕ) - (b : ℕ) : ℤ) % d : ℤ) : ℝ) +
      p 0 1 a b * ((((b : ℕ) - (a : ℕ) - 1 : ℤ) % d : ℤ) : ℝ))

/-! ### Quantum behaviours -/

/-- A pure state of two $D$-level systems: a vector of $\mathbb{C}^D \otimes \mathbb{C}^D$, whose
coordinate `(i, j)` is the amplitude of $|i\rangle_A |j\rangle_B$ (Alice's system first). -/
abbrev BipartiteState (D : ℕ) := EuclideanSpace ℂ (Fin D × Fin D)

/-- The maximally entangled state $|\Phi_D\rangle = D^{-1/2} \sum_{j<D} |j\rangle_A |j\rangle_B$. -/
noncomputable def maxEntangledState (D : ℕ) : BipartiteState D :=
  WithLp.toLp 2 fun ij => if ij.1 = ij.2 then ((Real.sqrt D : ℝ) : ℂ)⁻¹ else 0

/-- The density matrix $|\psi\rangle\langle\psi|$ of a pure state. -/
noncomputable def densityMatrix {D : ℕ} (ψ : BipartiteState D) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ))

/-- The maximally entangled state of two qudits mixed with white noise:
$\rho_v = v \, |\Phi_d\rangle\langle\Phi_d| + (1 - v) \, \mathbb{1} / d^2$. -/
noncomputable def whiteNoiseState (d : ℕ) (v : ℝ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (v : ℂ) • densityMatrix (maxEntangledState d) + (((1 - v) / (d : ℝ) ^ 2 : ℝ) : ℂ) • 1

/-- The Born rule: in the state `ρ`, the probability of the joint outcome with projections `A`
(Alice) and `B` (Bob) is $\operatorname{Tr}[\rho (A \otimes B)]$. -/
noncomputable def bornProb {D : ℕ} (ρ : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (A B : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  (ρ * (A ⊗ₖ B)).trace.re

/-- The quantum behaviour $p(a,b \mid x,y) = \operatorname{Tr}[\rho (A_{x,a} \otimes B_{y,b})]$ when
Alice measures `A x` and Bob measures `B y` on the state `ρ`. -/
noncomputable def quantumBehaviour {d D : ℕ} (ρ : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (A B : Fin 2 → Fin d → Matrix (Fin D) (Fin D) ℂ) : Behaviour d :=
  fun x y a b => bornProb ρ (A x a) (B y b)

/-- `P` is a projective measurement with outcomes `Fin m` on $\mathbb{C}^D$: every `P a` is an
orthogonal projection (Hermitian and idempotent), and $\sum_a P_a = 1$. -/
def IsProjectiveMeasurement {m D : ℕ} (P : Fin m → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  (∀ a, (P a).IsHermitian ∧ P a * P a = P a) ∧ ∑ a, P a = 1

/-- The complete von Neumann measurement in the orthonormal basis formed by the columns
$u_0, \dots, u_{d-1}$ of a unitary `U`: outcome `a` has the rank-one projection
$|u_a\rangle\langle u_a| = U |a\rangle\langle a| U^{\dagger}$. -/
noncomputable def vonNeumannMeasurement {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (a : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  U * single a a 1 * Uᴴ

/-- The behaviour of complete von Neumann measurements in the bases `UA x` (Alice) and `UB y` (Bob)
on the maximally entangled state $\Phi_d$ of two qudits. -/
noncomputable def vonNeumannBehaviour (d : ℕ) (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) :
    Behaviour d :=
  quantumBehaviour (densityMatrix (maxEntangledState d)) (fun x => vonNeumannMeasurement (UA x))
    (fun y => vonNeumannMeasurement (UB y))

/-! ### The Fourier-phase (DKZ) measurements -/

/-- The discrete Fourier transform $F_{jk} = d^{-1/2} e^{2\pi i jk/d}$. -/
noncomputable def dftMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun j k => ((Real.sqrt d : ℝ) : ℂ)⁻¹ *
    Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) : ℂ) * ((k : ℕ) : ℂ) / d)

/-- The diagonal phase unitary $\mathrm{diag}(e^{2\pi i j \theta / d})_{j<d}$. -/
noncomputable def phaseDiagonal (d : ℕ) (θ : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  diagonal fun j => Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) : ℂ) * (θ : ℂ) / d)

/-- Alice's DKZ phases $\alpha = (1/2, 0)$ for the inputs $1, 2$. -/
noncomputable def dkzAlpha : Fin 2 → ℝ := ![1 / 2, 0]

/-- Bob's DKZ phases $\beta = (-1/4, 1/4)$ for the inputs $1, 2$. -/
noncomputable def dkzBeta : Fin 2 → ℝ := ![-1 / 4, 1 / 4]

/-- Alice's DKZ basis for input `x` (Durt, Kaszlikowski and Zukowski 2001; Collins et al. 2002):
the computational basis transformed by the inverse discrete Fourier transform and the diagonal
unitary $\mathrm{diag}(e^{-2\pi i j \alpha_x / d})$, that is the basis
$|k\rangle_{A,x} = d^{-1/2} \sum_j e^{-2\pi i j (k + \alpha_x)/d} |j\rangle$. -/
noncomputable def dkzUnitaryA (d : ℕ) (x : Fin 2) : Matrix (Fin d) (Fin d) ℂ :=
  phaseDiagonal d (-dkzAlpha x) * (dftMatrix d)ᴴ

/-- Bob's DKZ basis for input `y`: the computational basis transformed by the discrete Fourier
transform and the diagonal unitary $\mathrm{diag}(e^{-2\pi i j \beta_y / d})$, that is the basis
$|l\rangle_{B,y} = d^{-1/2} \sum_j e^{2\pi i j (l - \beta_y)/d} |j\rangle$. -/
noncomputable def dkzUnitaryB (d : ℕ) (y : Fin 2) : Matrix (Fin d) (Fin d) ℂ :=
  phaseDiagonal d (-dkzBeta y) * dftMatrix d

/-- The uniqueness condition: a unitary `u` such that the local unitary $u \otimes \bar u$ maps the
measurements `A`, `B` on $\mathbb{C}^d$ to the DKZ measurements. The local unitaries
$u \otimes \bar u$ are exactly those that leave $\Phi_d$ invariant
(`kronecker_mulVec_maxEntangledState_eq_iff`). -/
def IsDKZUpToLocalUnitary {d : ℕ} (A B : Fin 2 → Fin d → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ u ∈ unitaryGroup (Fin d) ℂ,
    (∀ x a, u * A x a * uᴴ = vonNeumannMeasurement (dkzUnitaryA d x) a) ∧
    (∀ y b, u.map star * B y b * (u.map star)ᴴ = vonNeumannMeasurement (dkzUnitaryB d y) b)

/-! ### White noise -/

/-- The behaviour of complete von Neumann measurements in the bases `UA x`, `UB y` on the noisy
state $\rho_v = v \, |\Phi_d\rangle\langle\Phi_d| + (1 - v) \, \mathbb{1} / d^2$. -/
noncomputable def noisyVonNeumannBehaviour (d : ℕ) (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ)
    (v : ℝ) : Behaviour d :=
  quantumBehaviour (whiteNoiseState d v) (fun x => vonNeumannMeasurement (UA x))
    (fun y => vonNeumannMeasurement (UB y))

/-! ### The statistical strength (Kullback-Leibler divergence) -/

/-- The Kullback-Leibler divergence (in nats) of the behaviour `p` from the behaviour `q` when the
four input pairs are equally likely:
$\frac14 \sum_{x,y} \sum_{a,b} p(a,b \mid x,y) \log \frac{p(a,b \mid x,y)}{q(a,b \mid x,y)}$. -/
noncomputable def klDivUniform {d : ℕ} (p q : Behaviour d) : ℝ :=
  (1 / 4) * ∑ x : Fin 2, ∑ y : Fin 2, ∑ a : Fin d, ∑ b : Fin d,
    p x y a b * Real.log (p x y a b / q x y a b)

/-- **The statistical strength against local realism** (van Dam, Gill and Grünwald), for uniformly
random inputs: the infimum of `klDivUniform p q` over the local behaviours `q` with positive
entries. (Allowing zero entries does not change the infimum; van Dam, Gill and Grünwald also
consider strengths with optimized input distributions.) -/
noncomputable def statisticalStrength {d : ℕ} (p : Behaviour d) : ℝ :=
  ⨅ q : {q : Behaviour d // IsLocalBehaviour q ∧ ∀ x y a b, 0 < q x y a b}, klDivUniform p q.1

/-! ### The CGLMP expression of Collins et al. (2002), eq. (4) -/

/-- $P(A_x = B_y + k)$ for the behaviour `p`: the probability that Alice's output equals Bob's
output plus `k`, modulo `d`. -/
noncomputable def probAEqBAdd {d : ℕ} (p : Behaviour d) (x y : Fin 2) (k : ℤ) : ℝ :=
  ∑ a : Fin d, ∑ b : Fin d,
    if ((a : ℕ) : ZMod d) = ((b : ℕ) : ZMod d) + (k : ZMod d) then p x y a b else 0

/-- $P(B_y = A_x + k)$ for the behaviour `p`, modulo `d`. -/
noncomputable def probBEqAAdd {d : ℕ} (p : Behaviour d) (x y : Fin 2) (k : ℤ) : ℝ :=
  ∑ a : Fin d, ∑ b : Fin d,
    if ((b : ℕ) : ZMod d) = ((a : ℕ) : ZMod d) + (k : ZMod d) then p x y a b else 0

/-- The CGLMP expression of Collins, Gisin, Linden, Massar and Popescu (2002), eq. (4):
$$I_d = \sum_{k=0}^{\lfloor d/2 \rfloor - 1} \Big(1 - \frac{2k}{d-1}\Big)
\Big(\big[P(A_1 = B_1 + k) + P(B_1 = A_2 + k + 1) + P(A_2 = B_2 + k) + P(B_2 = A_1 + k)\big]$$
$$- \big[P(A_1 = B_1 - k - 1) + P(B_1 = A_2 - k) + P(A_2 = B_2 - k - 1)
+ P(B_2 = A_1 - k - 1)\big]\Big),$$
with $P(A_x = B_y + k)$ the probability that $A_x - B_y \equiv k \pmod d$; local models give
$I_d \le 2$. -/
noncomputable def cglmpExpr {d : ℕ} (p : Behaviour d) : ℝ :=
  ∑ k ∈ Finset.range (d / 2), (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) *
    ((probAEqBAdd p 0 0 k + probBEqAAdd p 1 0 (k + 1) + probAEqBAdd p 1 1 k +
        probBEqAAdd p 0 1 k) -
      (probAEqBAdd p 0 0 (-(k : ℤ) - 1) + probBEqAAdd p 1 0 (-(k : ℤ)) +
        probAEqBAdd p 1 1 (-(k : ℤ) - 1) + probBEqAAdd p 0 1 (-(k : ℤ) - 1)))

/-- Exchange the two inputs of both parties. -/
def swapInputs {d : ℕ} (p : Behaviour d) : Behaviour d := fun x y a b => p x.rev y.rev a b

/-- $I_{ME}(d) = \frac{4}{d(d-1)} \sum_{j=1}^{d-1} \frac{d - j}{\cos(\pi j / (2d))}$, the value of
`cglmpExpr` for the DKZ measurements on $\Phi_d$ (`cglmpFunctional_dkz`). -/
noncomputable def cglmpMaxEntValue (d : ℕ) : ℝ :=
  4 / ((d : ℝ) * ((d : ℝ) - 1)) *
    ∑ j ∈ Finset.Ico 1 d, ((d : ℝ) - j) / Real.cos (Real.pi * j / (2 * d))

/-- The state $(|00\rangle + \gamma |11\rangle + |22\rangle) / \sqrt{2 + \gamma^2}$ of two qutrits
(Acín, Durt, Gisin and Latorre 2002). -/
noncomputable def adglState (γ : ℝ) : BipartiteState 3 :=
  WithLp.toLp 2 fun ij => if ij.1 = ij.2 then
    ((((if (ij.1 : ℕ) = 1 then γ else 1) / Real.sqrt (2 + γ ^ 2)) : ℝ) : ℂ) else 0

/-! ### Checks of the definitions -/

/-- The maximally entangled state is a unit vector. -/
@[category test, AMS 15 81]
theorem norm_maxEntangledState (D : ℕ) [NeZero D] : ‖maxEntangledState D‖ = 1 := by
  have hD : (0 : ℝ) < D := Nat.cast_pos.2 (NeZero.pos D)
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fintype.sum_prod_type]
  have h : ∀ i : Fin D, ∑ j : Fin D, ‖(maxEntangledState D) (i, j)‖ ^ 2 = (D : ℝ)⁻¹ := by
    intro i
    rw [Finset.sum_eq_single i (fun j _ hji => by simp [maxEntangledState, Ne.symm hji])
      (by simp)]
    simp [maxEntangledState, norm_inv, Real.sq_sqrt hD.le]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-- $\operatorname{Tr}(|u\rangle\langle v| M) = \langle v| M |u\rangle$. -/
@[category API, AMS 15 81]
theorem trace_vecMulVec_mul {n : Type*} [Fintype n] (u v : n → ℂ) (M : Matrix n n ℂ) :
    (vecMulVec u v * M).trace = v ⬝ᵥ (M *ᵥ u) := by
  simp only [Matrix.trace, Matrix.diag, mul_apply, vecMulVec_apply, dotProduct, mulVec]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The Born rule on the maximally entangled state**:
$\operatorname{Tr}[|\Phi_D\rangle\langle\Phi_D| (A \otimes B)] = \operatorname{Tr}(A^{T} B) / D$. -/
@[category API, AMS 15 81]
theorem bornProb_maxEntangledState {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℂ) :
    bornProb (densityMatrix (maxEntangledState D)) A B = (Aᵀ * B).trace.re / D := by
  set c : ℂ := ((Real.sqrt D : ℝ) : ℂ)⁻¹ with hc
  have hcc : c * star c = ((D : ℝ) : ℂ)⁻¹ := by
    rw [hc, star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (Nat.cast_nonneg D)]
  set φ : Fin D × Fin D → ℂ := fun ij => if ij.1 = ij.2 then c else 0 with hφ
  have hφ' : WithLp.ofLp (maxEntangledState D) = φ := rfl
  have hrow : ∀ i : Fin D, ((A ⊗ₖ B) *ᵥ φ) (i, i) = ∑ k, A i k * B i k * c := by
    intro i
    simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type, hφ]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k (fun l _ hlk => by simp [Ne.symm hlk]) (by simp)]
    simp
  have hdiag : ∀ i : Fin D, ∑ j : Fin D, ((A ⊗ₖ B) *ᵥ φ) (i, j) * star (φ (i, j)) =
      ((A ⊗ₖ B) *ᵥ φ) (i, i) * star c := by
    intro i
    rw [Finset.sum_eq_single i (fun j _ hji => by simp [hφ, Ne.symm hji]) (by simp)]
    simp [hφ]
  have htr : (Aᵀ * B).trace = ∑ i : Fin D, ∑ k : Fin D, A i k * B i k := by
    rw [Matrix.trace, Finset.sum_comm]
    simp [Matrix.diag, mul_apply, transpose_apply]
  have key : ((A ⊗ₖ B) *ᵥ φ) ⬝ᵥ star φ = ((D : ℝ) : ℂ)⁻¹ * (Aᵀ * B).trace := by
    rw [dotProduct, Fintype.sum_prod_type]
    simp only [Pi.star_apply]
    rw [Finset.sum_congr rfl fun i _ => hdiag i, htr, ← hcc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrow i, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [bornProb, densityMatrix, hφ', trace_vecMulVec_mul, dotProduct_comm, key,
    ← Complex.ofReal_inv, Complex.re_ofReal_mul, inv_mul_eq_div]

@[category API, AMS 15 81]
lemma unitary_conjTranspose_mul {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ unitaryGroup (Fin d) ℂ) : Uᴴ * U = 1 := by
  have h := mem_unitaryGroup_iff'.1 hU
  rwa [star_eq_conjTranspose] at h

@[category API, AMS 15 81]
lemma unitary_mul_conjTranspose {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ unitaryGroup (Fin d) ℂ) : U * Uᴴ = 1 := by
  have h := mem_unitaryGroup_iff.1 hU
  rwa [star_eq_conjTranspose] at h

@[category API, AMS 15 81]
lemma sum_single_self_one (d : ℕ) : ∑ a : Fin d, single a a (1 : ℂ) = 1 := by
  ext i j
  rw [Matrix.sum_apply, Finset.sum_eq_single i]
  · by_cases hij : i = j <;> simp [one_apply, hij]
  · intro b _ hbi
    simp [hbi]
  · simp

/-- A complete von Neumann measurement is a projective measurement. -/
@[category test, AMS 15 81]
theorem isProjectiveMeasurement_vonNeumannMeasurement {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ unitaryGroup (Fin d) ℂ) : IsProjectiveMeasurement (vonNeumannMeasurement U) := by
  have h1 := unitary_conjTranspose_mul hU
  have h2 := unitary_mul_conjTranspose hU
  refine ⟨fun a => ⟨?_, ?_⟩, ?_⟩
  · unfold vonNeumannMeasurement
    rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      conjTranspose_single, star_one, Matrix.mul_assoc]
  · unfold vonNeumannMeasurement
    calc U * single a a 1 * Uᴴ * (U * single a a 1 * Uᴴ)
        = U * (single a a 1 * (Uᴴ * U) * single a a 1) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * single a a 1 * Uᴴ := by
          rw [h1, Matrix.mul_one, single_mul_single_same, mul_one, Matrix.mul_assoc]
  · unfold vonNeumannMeasurement
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_single_self_one, Matrix.mul_one, h2]

/-- The projections of a complete von Neumann measurement have rank one (trace $1$). -/
@[category test, AMS 15 81]
theorem trace_vonNeumannMeasurement {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ unitaryGroup (Fin d) ℂ) (a : Fin d) : (vonNeumannMeasurement U a).trace = 1 := by
  rw [vonNeumannMeasurement, trace_mul_comm, ← Matrix.mul_assoc, unitary_conjTranspose_mul hU,
    Matrix.one_mul, trace_single_eq_same]

/-- The DKZ bases are orthonormal: Alice's DKZ matrices are unitary. -/
@[category test, AMS 15 81, formal_proof using lean4 at
  "https://github.com/anshM123/IQOQI-OQP-27/blob/e3d6e5b2c474e2d834c603688b218ac98752a464/formal-conjectures-27/27.lean#L34730"]
theorem dkzUnitaryA_mem_unitaryGroup (d : ℕ) [NeZero d] (x : Fin 2) :
    dkzUnitaryA d x ∈ unitaryGroup (Fin d) ℂ := by
  sorry

/-- The DKZ bases are orthonormal: Bob's DKZ matrices are unitary. -/
@[category test, AMS 15 81, formal_proof using lean4 at
  "https://github.com/anshM123/IQOQI-OQP-27/blob/e3d6e5b2c474e2d834c603688b218ac98752a464/formal-conjectures-27/27.lean#L34739"]
theorem dkzUnitaryB_mem_unitaryGroup (d : ℕ) [NeZero d] (y : Fin 2) :
    dkzUnitaryB d y ∈ unitaryGroup (Fin d) ℂ := by
  sorry

/-- $(u \otimes v) \Phi_d$ has the coordinates of $d^{-1/2} \, u v^{T}$. -/
@[category API, AMS 15 81]
theorem kronecker_mulVec_maxEntangledState_apply {d : ℕ} (u v : Matrix (Fin d) (Fin d) ℂ)
    (i j : Fin d) :
    ((u ⊗ₖ v) *ᵥ WithLp.ofLp (maxEntangledState d)) (i, j) =
      ((Real.sqrt d : ℝ) : ℂ)⁻¹ * (u * vᵀ) i j := by
  simp only [maxEntangledState, mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_apply, transpose_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The local unitaries that leave $\Phi_d$ invariant** are the $u \otimes \bar u$: for a unitary
`u` and any matrix `v`, $(u \otimes v) \Phi_d = \Phi_d$ if and only if $v = \bar u$. These are the
local unitaries of the uniqueness condition `IsDKZUpToLocalUnitary`. -/
@[category test, AMS 15 81]
theorem kronecker_mulVec_maxEntangledState_eq_iff {d : ℕ} [NeZero d]
    (u v : Matrix (Fin d) (Fin d) ℂ) (hu : u ∈ unitaryGroup (Fin d) ℂ) :
    (u ⊗ₖ v) *ᵥ WithLp.ofLp (maxEntangledState d) = WithLp.ofLp (maxEntangledState d) ↔
      v = u.map star := by
  have hc : ((Real.sqrt d : ℝ) : ℂ)⁻¹ ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos d)
    exact inv_ne_zero (by exact_mod_cast this.ne')
  have h1 := unitary_mul_conjTranspose hu
  have h2 := unitary_conjTranspose_mul hu
  have key : (u ⊗ₖ v) *ᵥ WithLp.ofLp (maxEntangledState d) = WithLp.ofLp (maxEntangledState d) ↔
      u * vᵀ = 1 := by
    constructor
    · intro h
      ext i j
      have e := congrFun h (i, j)
      rw [kronecker_mulVec_maxEntangledState_apply] at e
      simp only [maxEntangledState] at e
      rw [one_apply]
      split_ifs at e ⊢ with hij
      · exact mul_left_cancel₀ hc (e.trans (mul_one _).symm)
      · exact (mul_eq_zero.1 e).resolve_left hc
    · intro h
      funext ⟨i, j⟩
      rw [kronecker_mulVec_maxEntangledState_apply, h, one_apply]
      simp only [maxEntangledState]
      split_ifs <;> simp
  rw [key]
  constructor
  · intro h
    have hvT : vᵀ = uᴴ := by
      calc vᵀ = (uᴴ * u) * vᵀ := by rw [h2, Matrix.one_mul]
        _ = uᴴ * (u * vᵀ) := Matrix.mul_assoc _ _ _
        _ = uᴴ := by rw [h, Matrix.mul_one]
    rw [← transpose_transpose v, hvT]
    ext i j
    rfl
  · intro h
    have hT : (u.map star)ᵀ = uᴴ := by
      ext i j
      rfl
    rw [h, hT, h1]

@[category API, AMS 15 81]
lemma sum_sum_deterministicBehaviour_mul {d : ℕ} (f g : Fin 2 → Fin d) (x y : Fin 2)
    (F : Fin d → Fin d → ℝ) :
    ∑ a : Fin d, ∑ b : Fin d, deterministicBehaviour f g x y a b * F a b = F (f x) (g y) := by
  simp only [deterministicBehaviour, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (f x), Finset.sum_eq_single (g y)]
  · simp
  · intro b _ hb
    simp [hb]
  · simp
  · intro a _ ha
    exact Finset.sum_eq_zero fun b _ => by simp [ha]
  · simp

/-- The value of the CGLMP functional for a deterministic strategy. -/
@[category API, AMS 15 81]
theorem cglmpFunctional_deterministicBehaviour {d : ℕ} (f g : Fin 2 → Fin d) :
    cglmpFunctional (deterministicBehaviour f g) =
      ((((f 0 : ℕ) - (g 0 : ℕ) : ℤ) % d : ℤ) : ℝ) + ((((g 0 : ℕ) - (f 1 : ℕ) : ℤ) % d : ℤ) : ℝ) +
        ((((f 1 : ℕ) - (g 1 : ℕ) : ℤ) % d : ℤ) : ℝ) +
        ((((g 1 : ℕ) - (f 0 : ℕ) - 1 : ℤ) % d : ℤ) : ℝ) := by
  simp only [cglmpFunctional, Finset.sum_add_distrib]
  rw [sum_sum_deterministicBehaviour_mul f g 0 0 (fun a b => ((((a : ℕ) - (b : ℕ) : ℤ) % d : ℤ) : ℝ)),
    sum_sum_deterministicBehaviour_mul f g 1 0 (fun a b => ((((b : ℕ) - (a : ℕ) : ℤ) % d : ℤ) : ℝ)),
    sum_sum_deterministicBehaviour_mul f g 1 1 (fun a b => ((((a : ℕ) - (b : ℕ) : ℤ) % d : ℤ) : ℝ)),
    sum_sum_deterministicBehaviour_mul f g 0 1
      (fun a b => ((((b : ℕ) - (a : ℕ) - 1 : ℤ) % d : ℤ) : ℝ))]

/-- **The CGLMP inequality for deterministic strategies**: the functional is at least $d - 1$. -/
@[category test, AMS 15 81]
theorem cglmpFunctional_deterministicBehaviour_ge {d : ℕ} [NeZero d] (f g : Fin 2 → Fin d) :
    (d : ℝ) - 1 ≤ cglmpFunctional (deterministicBehaviour f g) := by
  rw [cglmpFunctional_deterministicBehaviour]
  have hd : (0 : ℤ) < d := by exact_mod_cast NeZero.pos d
  set t₁ : ℤ := ((f 0 : ℕ) - (g 0 : ℕ) : ℤ)
  set t₂ : ℤ := ((g 0 : ℕ) - (f 1 : ℕ) : ℤ)
  set t₃ : ℤ := ((f 1 : ℕ) - (g 1 : ℕ) : ℤ)
  set t₄ : ℤ := ((g 1 : ℕ) - (f 0 : ℕ) - 1 : ℤ)
  have hsum : t₁ + t₂ + t₃ + t₄ = -1 := by ring
  have e₁ := Int.mul_ediv_add_emod t₁ d
  have e₂ := Int.mul_ediv_add_emod t₂ d
  have e₃ := Int.mul_ediv_add_emod t₃ d
  have e₄ := Int.mul_ediv_add_emod t₄ d
  have n₁ := Int.emod_nonneg t₁ hd.ne'
  have n₂ := Int.emod_nonneg t₂ hd.ne'
  have n₃ := Int.emod_nonneg t₃ hd.ne'
  have n₄ := Int.emod_nonneg t₄ hd.ne'
  set Q : ℤ := t₁ / d + t₂ / d + t₃ / d + t₄ / d with hQ
  have hS : t₁ % d + t₂ % d + t₃ % d + t₄ % d = -1 - d * Q := by
    rw [hQ]
    linear_combination e₁ + e₂ + e₃ + e₄ + hsum
  have hQneg : Q ≤ -1 := by
    rcases le_or_gt Q (-1) with h | h
    · exact h
    · have : 0 ≤ (d : ℤ) * Q := mul_nonneg hd.le (by omega)
      linarith
  have hdQ : (d : ℤ) * Q ≤ -(d : ℤ) := by nlinarith
  have hZ : (d : ℤ) - 1 ≤ t₁ % d + t₂ % d + t₃ % d + t₄ % d := by linarith
  have hR : (((d : ℤ) - 1 : ℤ) : ℝ) ≤ ((t₁ % d + t₂ % d + t₃ % d + t₄ % d : ℤ) : ℝ) := by
    exact_mod_cast hZ
  push_cast at hR
  exact hR

/-- The local bound $d - 1$ is attained, by the strategy in which both parties always output `0`. -/
@[category test, AMS 15 81]
theorem cglmpFunctional_deterministicBehaviour_zero {d : ℕ} [NeZero d] :
    cglmpFunctional (deterministicBehaviour (d := d) (fun _ => 0) (fun _ => 0)) = (d : ℝ) - 1 := by
  rw [cglmpFunctional_deterministicBehaviour]
  have hd : (0 : ℤ) < d := by exact_mod_cast NeZero.pos d
  have hm : ((-1 : ℤ) % d) = d - 1 :=
    ((Int.ediv_emod_unique (q := -1) (r := (d : ℤ) - 1) hd).2 ⟨by ring, by omega, by omega⟩).2
  simp only [Fin.val_zero, Nat.cast_zero, sub_self, Int.zero_emod, Int.cast_zero, zero_add,
    zero_sub, hm]
  push_cast
  ring

@[category API, AMS 15 81]
lemma sum_four_linear {d : ℕ} {ι : Type*} (S : Finset ι) (q : ι → ℝ) (P : ι → Behaviour d)
    (c₁ c₂ c₃ c₄ : Fin d → Fin d → ℝ) :
    ∑ a : Fin d, ∑ b : Fin d, ((∑ i ∈ S, q i * P i 0 0 a b) * c₁ a b +
      (∑ i ∈ S, q i * P i 1 0 a b) * c₂ a b + (∑ i ∈ S, q i * P i 1 1 a b) * c₃ a b +
      (∑ i ∈ S, q i * P i 0 1 a b) * c₄ a b) =
    ∑ i ∈ S, q i * ∑ a : Fin d, ∑ b : Fin d, (P i 0 0 a b * c₁ a b + P i 1 0 a b * c₂ a b +
      P i 1 1 a b * c₃ a b + P i 0 1 a b * c₄ a b) := by
  have inner : ∀ a b : Fin d, (∑ i ∈ S, q i * P i 0 0 a b) * c₁ a b +
      (∑ i ∈ S, q i * P i 1 0 a b) * c₂ a b + (∑ i ∈ S, q i * P i 1 1 a b) * c₃ a b +
      (∑ i ∈ S, q i * P i 0 1 a b) * c₄ a b =
      ∑ i ∈ S, q i * (P i 0 0 a b * c₁ a b + P i 1 0 a b * c₂ a b + P i 1 1 a b * c₃ a b +
        P i 0 1 a b * c₄ a b) := by
    intro a b
    simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [inner]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]

/-- **The CGLMP inequality**: every local model gives at least $d - 1$. -/
@[category test, AMS 15 81]
theorem le_cglmpFunctional_of_isLocalBehaviour {d : ℕ} [NeZero d] {p : Behaviour d}
    (hp : IsLocalBehaviour p) : (d : ℝ) - 1 ≤ cglmpFunctional p := by
  obtain ⟨q, hq0, hq1, hpq⟩ := hp
  have hp' : p = fun x y a b => ∑ s, q s * deterministicBehaviour s.1 s.2 x y a b := by
    funext x y a b
    exact hpq x y a b
  have hlin : cglmpFunctional p = ∑ s, q s * cglmpFunctional (deterministicBehaviour s.1 s.2) := by
    rw [hp']
    exact sum_four_linear Finset.univ q (fun s => deterministicBehaviour s.1 s.2) _ _ _ _
  rw [hlin]
  calc (d : ℝ) - 1 = ∑ s, q s * ((d : ℝ) - 1) := by rw [← Finset.sum_mul, hq1, one_mul]
    _ ≤ ∑ s, q s * cglmpFunctional (deterministicBehaviour s.1 s.2) :=
        Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (cglmpFunctional_deterministicBehaviour_ge s.1 s.2) (hq0 s)

/-- **The two forms of the CGLMP functional agree**: for every behaviour `p` in which each
$p(\cdot,\cdot \mid x,y)$ is a probability distribution, the CGLMP expression of Collins et al. is
$I_d(p) = 4 - \frac{2}{d-1} F(p')$, where $F$ is the functional of the problem page and $p'$ is `p`
with the two inputs exchanged. In particular $I_d(p) \le 2$ if and only if $F(p') \ge d - 1$. -/
@[category API, AMS 15 81, formal_proof using lean4 at
  "https://github.com/anshM123/IQOQI-OQP-27/blob/e3d6e5b2c474e2d834c603688b218ac98752a464/formal-conjectures-27/27.lean#L777"]
theorem cglmpExpr_eq_cglmpFunctional {d : ℕ} (hd : 2 ≤ d) (p : Behaviour d)
    (hp : ∀ x y, ∑ a, ∑ b, p x y a b = 1) :
    cglmpExpr p = 4 - 2 * cglmpFunctional (swapInputs p) / ((d : ℝ) - 1) := by
  sorry

/-- On the maximally entangled state, measuring both systems in the computational basis gives
perfectly correlated, uniformly random outputs. -/
@[category test, AMS 15 81]
theorem bornProb_maxEntangledState_single {D : ℕ} (a b : Fin D) :
    bornProb (densityMatrix (maxEntangledState D)) (single a a 1) (single b b 1) =
      if a = b then 1 / (D : ℝ) else 0 := by
  rw [bornProb_maxEntangledState, transpose_single]
  by_cases h : a = b
  · subst h
    rw [single_mul_single_same, trace_single_eq_same, if_pos rfl]
    simp
  · rw [if_neg h]
    simp [h]

@[category API, AMS 15 81]
lemma vonNeumannMeasurement_one {d : ℕ} (a : Fin d) :
    vonNeumannMeasurement 1 a = single a a 1 := by
  simp [vonNeumannMeasurement]

/-- On $\Phi_d$, measuring both systems in the computational basis for both inputs gives exactly
the local bound $d - 1$: there is no violation without the Fourier-phase bases. -/
@[category test, AMS 15 81]
theorem cglmpFunctional_computationalBasis {d : ℕ} [NeZero d] :
    cglmpFunctional (vonNeumannBehaviour d (fun _ => 1) (fun _ => 1)) = (d : ℝ) - 1 := by
  have hd : (0 : ℤ) < d := by exact_mod_cast NeZero.pos d
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  have hp : ∀ x y : Fin 2, ∀ a b : Fin d,
      vonNeumannBehaviour d (fun _ => 1) (fun _ => 1) x y a b =
        if a = b then 1 / (d : ℝ) else 0 := by
    intro x y a b
    simp only [vonNeumannBehaviour, quantumBehaviour, vonNeumannMeasurement_one]
    exact bornProb_maxEntangledState_single a b
  have hm : ((((0 : ℤ) - 1) % d : ℤ)) = d - 1 :=
    ((Int.ediv_emod_unique (q := -1) (r := (d : ℤ) - 1) hd).2 ⟨by ring, by omega, by omega⟩).2
  simp only [cglmpFunctional, hp]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_eq_single a (fun b _ hba => by simp [Ne.symm hba])
    (by simp)]
  simp only [if_true, sub_self, Int.zero_emod, Int.cast_zero, mul_zero, zero_add, add_zero, hm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-- $I_{ME}(2) = 2\sqrt{2}$, Tsirelson's bound for the CHSH expression. -/
@[category test, AMS 15 81]
theorem cglmpMaxEntValue_two : cglmpMaxEntValue 2 = 2 * Real.sqrt 2 := by
  have hI : Finset.Ico 1 2 = {1} := rfl
  have hc : Real.cos (Real.pi * ((1 : ℕ) : ℝ) / (2 * ((2 : ℕ) : ℝ))) = Real.sqrt 2 / 2 := by
    rw [show Real.pi * ((1 : ℕ) : ℝ) / (2 * ((2 : ℕ) : ℝ)) = Real.pi / 4 by push_cast; ring]
    exact Real.cos_pi_div_four
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  rw [cglmpMaxEntValue, hI, Finset.sum_singleton, hc]
  push_cast
  field_simp
  nlinarith [hs]

/-- **The value of the DKZ measurements**: $F(\mathrm{DKZ}) = \frac{d-1}{2} (4 - I_{ME}(d))$. -/
@[category research solved, AMS 15 81, formal_proof using lean4 at
  "https://github.com/anshM123/IQOQI-OQP-27/blob/e3d6e5b2c474e2d834c603688b218ac98752a464/formal-conjectures-27/27.lean#L34763"]
theorem cglmpFunctional_dkz {d : ℕ} [NeZero d] (h2 : 2 ≤ d) :
    cglmpFunctional (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) =
      ((d : ℝ) - 1) * (4 - cglmpMaxEntValue d) / 2 := by
  sorry

/-- The DKZ measurements violate the CGLMP inequality: $F(\mathrm{DKZ}) < d - 1$. -/
@[category research solved, AMS 15 81, formal_proof using lean4 at
  "https://github.com/anshM123/IQOQI-OQP-27/blob/e3d6e5b2c474e2d834c603688b218ac98752a464/formal-conjectures-27/27.lean#L34774"]
theorem cglmpFunctional_dkz_lt {d : ℕ} [NeZero d] (h2 : 2 ≤ d) :
    cglmpFunctional (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) < (d : ℝ) - 1 := by
  sorry

/-! ### Part B, first statement: the DKZ measurements are optimal and necessarily of DKZ form -/

/-- **OQP 27B, optimality of the DKZ measurements.** For every $d \ge 2$, on the maximally entangled
state $\Phi_d$ no complete von Neumann measurements give a smaller value of the CGLMP functional (a
larger violation of the CGLMP inequality) than the DKZ measurements. -/
@[category research open, AMS 15 81]
theorem dkz_optimal (d : ℕ) [NeZero d] (h2 : 2 ≤ d)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) :
    cglmpFunctional (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) ≤
      cglmpFunctional (vonNeumannBehaviour d UA UB) := by
  sorry

/-- **OQP 27B, the optimal measurements are necessarily the DKZ measurements.** For every $d \ge 2$,
complete von Neumann measurements on $\Phi_d$ attain the DKZ value of the CGLMP functional if and
only if a local unitary $u \otimes \bar u$ (one that leaves $\Phi_d$ invariant) maps them to the
DKZ measurements. -/
@[category research open, AMS 15 81]
theorem dkz_unique (d : ℕ) [NeZero d] (h2 : 2 ≤ d)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) :
    cglmpFunctional (vonNeumannBehaviour d UA UB) =
        cglmpFunctional (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) ↔
      IsDKZUpToLocalUnitary (fun x => vonNeumannMeasurement (UA x))
        (fun y => vonNeumannMeasurement (UB y)) := by
  sorry

/-- `dkz_optimal` for $2 \le d \le 20$. -/
@[category research solved, AMS 15 81, formal_proof using lean4 at
  "https://github.com/anshM123/IQOQI-OQP-27/blob/e3d6e5b2c474e2d834c603688b218ac98752a464/formal-conjectures-27/27.lean#L34917"]
theorem dkz_optimal_of_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) :
    cglmpFunctional (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) ≤
      cglmpFunctional (vonNeumannBehaviour d UA UB) := by
  sorry

/-- `dkz_unique` for $2 \le d \le 20$. -/
@[category research solved, AMS 15 81, formal_proof using lean4 at
  "https://github.com/anshM123/IQOQI-OQP-27/blob/e3d6e5b2c474e2d834c603688b218ac98752a464/formal-conjectures-27/27.lean#L34941"]
theorem dkz_unique_of_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) :
    cglmpFunctional (vonNeumannBehaviour d UA UB) =
        cglmpFunctional (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) ↔
      IsDKZUpToLocalUnitary (fun x => vonNeumannMeasurement (UA x))
        (fun y => vonNeumannMeasurement (UB y)) := by
  sorry

/-- **Optimality for all projective measurements on maximally entangled states of every local
dimension**, for $2 \le d \le 20$: no $d$-outcome projective measurements (of any ranks) on
$\Phi_D$ give a smaller value of the CGLMP functional than $\frac{d-1}{2}(4 - I_{ME}(d))$. -/
@[category research solved, AMS 15 81, formal_proof using lean4 at
  "https://github.com/anshM123/IQOQI-OQP-27/blob/e3d6e5b2c474e2d834c603688b218ac98752a464/formal-conjectures-27/27.lean#L35177"]
theorem dkz_optimal_any_dim_of_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20) (D : ℕ)
    (hD : 0 < D) (A B : Fin 2 → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ x, IsProjectiveMeasurement (A x)) (hB : ∀ y, IsProjectiveMeasurement (B y)) :
    ((d : ℝ) - 1) * (4 - cglmpMaxEntValue d) / 2 ≤
      cglmpFunctional (quantumBehaviour (densityMatrix (maxEntangledState D)) A B) := by
  sorry

/-- **Uniqueness for all projective measurements on $\Phi_D$, every $D$**, for $2 \le d \le 20$:
the bound of `dkz_optimal_any_dim_of_le_twenty` is attained if and only if $D = dK$ and a unitary
$V : \mathbb{C}^D \to \mathbb{C}^d \otimes \mathbb{C}^K$ maps the measurements to the DKZ
measurements tensored with the identity. -/
@[category research solved, AMS 15 81, formal_proof using lean4 at
  "https://github.com/anshM123/IQOQI-OQP-27/blob/e3d6e5b2c474e2d834c603688b218ac98752a464/formal-conjectures-27/27.lean#L35197"]
theorem dkz_unique_any_dim_of_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20) (D : ℕ)
    (hD : 0 < D) (A B : Fin 2 → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ x, IsProjectiveMeasurement (A x)) (hB : ∀ y, IsProjectiveMeasurement (B y)) :
    cglmpFunctional (quantumBehaviour (densityMatrix (maxEntangledState D)) A B) =
        ((d : ℝ) - 1) * (4 - cglmpMaxEntValue d) / 2 ↔
      ∃ K : ℕ, D = d * K ∧ ∃ V : Matrix (Fin d × Fin K) (Fin D) ℂ, V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧
        (∀ x a, V * A x a * Vᴴ =
          vonNeumannMeasurement (dkzUnitaryA d x) a ⊗ₖ (1 : Matrix (Fin K) (Fin K) ℂ)) ∧
        (∀ y b, V.map star * B y b * (V.map star)ᴴ =
          vonNeumannMeasurement (dkzUnitaryB d y) b ⊗ₖ (1 : Matrix (Fin K) (Fin K) ℂ)) := by
  sorry

/-- **The case $d = 2$: Tsirelson's bound.** For $d = 2$ the CGLMP functional is
$\frac{4 - \mathrm{CHSH}}{2}$; on two maximally entangled qubits no complete von Neumann measurements
go below $2 - \sqrt{2}$ (that is, CHSH $\le 2\sqrt{2}$), and the DKZ measurements attain it. -/
@[category research solved, AMS 15 81, formal_proof using lean4 at
  "https://github.com/anshM123/IQOQI-OQP-27/blob/e3d6e5b2c474e2d834c603688b218ac98752a464/formal-conjectures-27/27.lean#L35229"]
theorem dkz_tsirelson (UA UB : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (hUA : ∀ x, UA x ∈ unitaryGroup (Fin 2) ℂ) (hUB : ∀ y, UB y ∈ unitaryGroup (Fin 2) ℂ) :
    2 - Real.sqrt 2 ≤ cglmpFunctional (vonNeumannBehaviour 2 UA UB) ∧
      cglmpFunctional (vonNeumannBehaviour 2 (dkzUnitaryA 2) (dkzUnitaryB 2)) = 2 - Real.sqrt 2 := by
  sorry

/-- **A related question: the maximally entangled state is not optimal for $d = 3$** (Acín, Durt,
Gisin and Latorre 2002). With the DKZ measurements, the state
$(|00\rangle + \tfrac{4}{5} |11\rangle + |22\rangle)/\sqrt{2 + 16/25}$ gives a smaller value of the
CGLMP functional than any complete von Neumann measurements on $\Phi_3$. So the restriction to
$\Phi_d$ in the problem matters. -/
@[category research solved, AMS 15 81, formal_proof using lean4 at
  "https://github.com/anshM123/IQOQI-OQP-27/blob/e3d6e5b2c474e2d834c603688b218ac98752a464/formal-conjectures-27/27.lean#L35250"]
theorem adglState_beats_maxEntangledState (UA UB : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ)
    (hUA : ∀ x, UA x ∈ unitaryGroup (Fin 3) ℂ) (hUB : ∀ y, UB y ∈ unitaryGroup (Fin 3) ℂ) :
    cglmpFunctional (quantumBehaviour (densityMatrix (adglState (4 / 5)))
      (fun x => vonNeumannMeasurement (dkzUnitaryA 3 x))
      (fun y => vonNeumannMeasurement (dkzUnitaryB 3 y))) <
      cglmpFunctional (vonNeumannBehaviour 3 UA UB) := by
  sorry

/-! ### Part B, second statement: resistance to noise -/

/-- **OQP 27B, noise clause for the violation of the CGLMP inequality** (the formulation of issue
#3444). Mix $\Phi_d$ with white noise,
$\rho_v = v \, |\Phi_d\rangle\langle\Phi_d| + (1 - v) \, \mathbb{1}/d^2$ with $v \ge 0$. Whenever
complete von Neumann measurements violate the CGLMP inequality on $\rho_v$, so do the DKZ
measurements; and measurements that violate it at every visibility at which DKZ does are DKZ up to
a local unitary $u \otimes \bar u$. -/
@[category research open, AMS 15 81]
theorem dkz_noise (d : ℕ) [NeZero d] (h2 : 2 ≤ d)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) :
    (∀ v : ℝ, 0 ≤ v → cglmpFunctional (noisyVonNeumannBehaviour d UA UB v) < (d : ℝ) - 1 →
      cglmpFunctional (noisyVonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d) v) < (d : ℝ) - 1) ∧
    ((∀ v : ℝ,
        cglmpFunctional (noisyVonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d) v) < (d : ℝ) - 1 →
          cglmpFunctional (noisyVonNeumannBehaviour d UA UB v) < (d : ℝ) - 1) →
      IsDKZUpToLocalUnitary (fun x => vonNeumannMeasurement (UA x))
        (fun y => vonNeumannMeasurement (UB y))) := by
  sorry

/-- `dkz_noise` for $2 \le d \le 20$. -/
@[category research solved, AMS 15 81, formal_proof using lean4 at
  "https://github.com/anshM123/IQOQI-OQP-27/blob/e3d6e5b2c474e2d834c603688b218ac98752a464/formal-conjectures-27/27.lean#L35064"]
theorem dkz_noise_of_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) :
    (∀ v : ℝ, 0 ≤ v → cglmpFunctional (noisyVonNeumannBehaviour d UA UB v) < (d : ℝ) - 1 →
      cglmpFunctional (noisyVonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d) v) < (d : ℝ) - 1) ∧
    ((∀ v : ℝ,
        cglmpFunctional (noisyVonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d) v) < (d : ℝ) - 1 →
          cglmpFunctional (noisyVonNeumannBehaviour d UA UB v) < (d : ℝ) - 1) →
      IsDKZUpToLocalUnitary (fun x => vonNeumannMeasurement (UA x))
        (fun y => vonNeumannMeasurement (UB y))) := by
  sorry

/-- **OQP 27B, noise clause for the violation of local realism** (all Bell inequalities), with
complete von Neumann measurements on $\Phi_d$: whenever the DKZ measurements on the noisy state
$\rho_v$ give a local behaviour, so do all other complete von Neumann measurements. Equivalently,
the DKZ measurements have the smallest critical visibility. True for $d = 2$ (Tsirelson's bound and
Fine's theorem). -/
@[category research open, AMS 15 52 81]
theorem dkz_noise_allBell (d : ℕ) [NeZero d] (h2 : 2 ≤ d)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    IsLocalBehaviour (noisyVonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d) v) →
      IsLocalBehaviour (noisyVonNeumannBehaviour d UA UB v) := by
  sorry

/-! ### Part B, third statement: Kullback-Leibler discrimination -/

/-- **OQP 27B, the Kullback-Leibler clause** (statistical strength with uniformly random inputs):
is it true that for every $d \ge 2$ the DKZ measurements have the largest statistical strength
against local realism among all complete von Neumann measurements on $\Phi_d$? -/
@[category research open, AMS 15 81 94]
theorem dkz_klOptimal : answer(sorry) ↔
    ∀ d ≥ 2, ∀ UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ, (∀ x, UA x ∈ unitaryGroup (Fin d) ℂ) →
      (∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) →
        statisticalStrength (vonNeumannBehaviour d UA UB) ≤
          statisticalStrength (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) := by
  sorry

/-- **The Kullback-Leibler clause for $d = 3$.** The DKZ measurements on $\Phi_3$ have the largest
statistical strength against local realism among all complete von Neumann measurements on
$\Phi_3$. -/
@[category research open, AMS 15 81 94]
theorem dkz_klOptimal_three (UA UB : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ)
    (hUA : ∀ x, UA x ∈ unitaryGroup (Fin 3) ℂ) (hUB : ∀ y, UB y ∈ unitaryGroup (Fin 3) ℂ) :
    statisticalStrength (vonNeumannBehaviour 3 UA UB) ≤
      statisticalStrength (vonNeumannBehaviour 3 (dkzUnitaryA 3) (dkzUnitaryB 3)) := by
  sorry

end OpenQuantumProblem27
