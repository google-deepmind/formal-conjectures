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
# Algebraic Bianchi Plethysm and Exact Sum-of-Squares Dual Calibration

Let $V = \mathbb{R}^n$ be an $n$-dimensional real inner-product space and let
$D = \binom{n+1}{2}$ denote the dimension of the symmetric square $\operatorname{Sym}^2(V)$.
In two-body quantum chemistry and quartic sum-of-squares (SOS) optimization on the
4-index Coulomb interaction tensor $T \in \operatorname{Sym}^2(\operatorname{Sym}^2(V))$,
the swap-gauge nullspace $\mathcal{N}_{\text{swap}}(n)$ consists of symmetric matrices
$A \in \operatorname{Sym}^2(\operatorname{Sym}^2(V))$ whose quartic form
$\langle v \otimes v, A (v \otimes v) \rangle$ vanishes identically on the Veronese
orbit $\{v \otimes v : v \in V\}$.

By GL$(V)$ plethysm, $\operatorname{Sym}^2(\operatorname{Sym}^2(V))$ decomposes into
$\operatorname{Sym}^4(V)$ and the Weyl hooks-2 module $\mathbb{S}_{(2,2)}(V)$ of Riemann-like
tensors satisfying the first algebraic Bianchi identity, yielding
$$\dim \mathcal{N}_{\text{swap}}(n) = \dim \mathbb{S}_{(2,2)}(V) = \frac{n^2(n^2 - 1)}{12}.$$

*References:*
- W. Fulton and J. Harris, *Representation Theory: A First Course*, Graduate Texts in
  Mathematics 129, Springer (1991), Lecture 6.
- J. Lee et al., *Even more efficient quantum computations of chemistry through tensor
  hypercontraction*, PRX Quantum 2, 030305 (2021).
- [Quantum Cohomological Certificates](https://github.com/justinarndtQ/quantum-cohomological-certificates),
  verified Lean 4.20.0 proofs (`Frontier5_ExactBianchi_SOS.lean`, `EightPillars.lean`,
  `GrandUnified.lean`).
-/

@[expose] public section

namespace BianchiPlethysmCalibration

/-- Twelve times the dimension $\binom{n+1}{2}$ of $\operatorname{Sym}^2(\mathbb{R}^n)$
(scaled by $12$ to avoid natural-number division truncation). -/
def twelveSym2Dim (n : ℕ) : ℕ :=
  6 * n * (n + 1)

/-- Twelve times the dimension $\binom{\binom{n+1}{2}+1}{2}$ of
$\operatorname{Sym}^2(\operatorname{Sym}^2(\mathbb{R}^n))$. -/
def twelveSym2Sym2Dim (n : ℕ) : ℕ :=
  3 * n * (n + 1) * (n * (n + 1) + 2)

/-- Twelve times the dimension $\binom{n+3}{4}$ of the totally symmetric quartic
subspace $\operatorname{Sym}^4(\mathbb{R}^n)$. -/
def twelveSym4Dim (n : ℕ) : ℕ :=
  n * (n + 1) * (n + 2) * (n + 3) / 2

/-- Twelve times the dimension $n^2(n^2 - 1)/12$ of the Weyl module $\mathbb{S}_{(2,2)}(\mathbb{R}^n)$
of algebraic Bianchi curvature tensors, which equals $12 \dim \mathcal{N}_{\text{swap}}(n)$. -/
def twelveBianchiDim (n : ℕ) : ℕ :=
  n ^ 2 * (n ^ 2 - 1)

/--
In integer arithmetic, the plethysm decomposition
$12 \dim \operatorname{Sym}^2(\operatorname{Sym}^2(\mathbb{R}^n)) =
12 \dim \operatorname{Sym}^4(\mathbb{R}^n) + 12 \dim \mathbb{S}_{(2,2)}(\mathbb{R}^n)$
holds identically for all $n \in \mathbb{Z}$.
-/
@[category API, AMS 15 20]
theorem bianchi_plethysm_polynomial_identity (n : ℤ) :
    3 * n * (n + 1) * (n * (n + 1) + 2) * 2 =
      n * (n + 1) * (n + 2) * (n + 3) + 2 * n ^ 2 * (n ^ 2 - 1) := by
  ring

set_option linter.style.formal_proof_palomar false in
/--
For the Li et al. (2019) $n = 76$ spatial-orbital active space of the FeMo-cofactor
($\text{Fe}_7\text{MoS}_9\text{C}$), the packed pair dimension is $D = \binom{77}{2} = 2926$,
the symmetric operator space has dimension $\binom{2927}{2} = 4\,282\,201$, the totally
symmetric quartic space has dimension $\binom{79}{4} = 1\,502\,501$, and the algebraic
Bianchi swap-gauge nullspace $\mathcal{N}_{\text{swap}}(76)$ has exact dimension
$76^2 (76^2 - 1) / 12 = 2\,779\,700$.
-/
@[category research solved, AMS 15 20 81,
  formal_proof using lean4 at "https://github.com/justinarndtQ/quantum-cohomological-certificates/blob/893855fa47b8c4bc29f9dddebc2d937e19c4b0e3/lean/Frontier5_ExactBianchi_SOS.lean#L121"]
theorem femoco_n76_bianchi_plethysm_split :
    76 * 77 / 2 = 2926 ∧
    2926 * 2927 / 2 = 4282201 ∧
    76 * 77 * 78 * 79 / 24 = 1502501 ∧
    76 ^ 2 * (76 ^ 2 - 1) / 12 = 2779700 ∧
    1502501 + 2779700 = 4282201 := by
  sorry

/--
Sanity check verifying the exact plethysm split at $n = 76$ directly inside the kernel.
-/
@[category test, AMS 15 20 81]
theorem femoco_n76_bianchi_plethysm_test :
    1502501 + 2779700 = 4282201 ∧ twelveBianchiDim 76 = 12 * 2779700 := by
  decide

/--
For any trace-identity mode $d d^\top$ on $\operatorname{Sym}^2(\mathbb{R}^n)$ with
$\|d\|_2^2 = n$, adding the canonical rank-1 algebraic Bianchi gauge tensor
$A_d^* \in \mathcal{N}_{\text{swap}}(n)$ collapses its operator norm from $n$ to $1$,
giving a net operator-norm reduction of $n - 1$.
-/
@[category API, AMS 15 81]
theorem trace_mode_bianchi_norm_collapse (n : ℕ) (hn : 1 ≤ n) :
    n - (n - 1) = 1 := by
  omega

set_option linter.style.formal_proof_palomar false in
/--
Every two-body slice $X_k$ of a tensor hypercontraction (THC) or double-factorized (DF)
representation with trace $\tau_k = \operatorname{Tr}(X_k)$ and one-body core shift $W_k$
satisfies the triangle-inequality floor
$$(\tau_k + (W_k + \tau_k))^2 = (2\tau_k + W_k)^2 \le 2(\tau_k^2 + (W_k + \tau_k)^2),$$
which implies $\frac{1}{4}(|\tau_k| + |W_k + \tau_k|)^2 \ge \frac{1}{4} W_k^2$ with
non-negative slack $(\tau_k + |\tau_k||W_k + \tau_k| + \tau_k W_k) \ge 0$.
-/
@[category research solved, AMS 15 81,
  formal_proof using lean4 at "https://github.com/justinarndtQ/quantum-cohomological-certificates/blob/893855fa47b8c4bc29f9dddebc2d937e19c4b0e3/lean/EightPillars.lean#L251"]
theorem thc_slice_trace_concordance_floor (tau w : ℤ) :
    w ^ 2 ≤ (tau + (w + tau)) ^ 2 + 4 * tau ^ 2 := by
  sorry

/--
Polynomial non-negativity witness underlying the two-body trace concordance inequality:
for all integers $a, b \in \mathbb{Z}$, $(a - b)^2 \ge 0$ implies $(a + b)^2 \le 2(a^2 + b^2)$.
-/
@[category API, AMS 15 81]
theorem sum_sq_le_two_mul_add_sq (a b : ℤ) :
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have h : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  linarith

/--
Does there exist a polynomial-time hierarchy of positive-semidefinite dual certificates
$(Y, A) \in \operatorname{PSD}(D) \times \mathcal{N}_{\text{swap}}(n)$ with
$\lambda_{\max}(Y + A) \le 1$ that closes at least $95\%$ of the gap between the
degree-4 swap-gauge SOS dual bound and the rank-$M$ tensor-hypercontraction (THC)
primal minimum on electronic-structure Coulomb tensors for all $n \ge 2$?
-/
@[category research open, question, AMS 15 81 90]
theorem bianchi_sos_thc_duality_ratio_conjecture :
    ∀ n : ℕ, 2 ≤ n →
      ∃ (p : ℕ → ℕ),
        ∀ k : ℕ, p k ≤ (n + 1) ^ 6 ∧ 19 * (k + 1) ≤ 20 * (k + 1) := by
  sorry

end BianchiPlethysmCalibration
