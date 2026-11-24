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
# The Grothendieck–Katz conjecture on $p$-curvature

For a rank-$n$ linear differential system $f(X) Y'(X) = B(X) Y(X)$ with $0 \ne f \in \mathbb{Z}[X]$
and $B \in M_n(\mathbb{Z}[X])$, reducing modulo a prime $p$ not dividing $f$ gives a connection
$\nabla = \frac{d}{dX} - f^{-1} B$ over $\mathbb{F}_p(X)$ whose $p$-curvature $\psi_p = \nabla^p$
vanishes precisely when the $p$-th cleared derivative matrix $M_p \in M_n(\mathbb{Z}[X])$ vanishes
modulo $p$.

Proposed by Alexander Grothendieck (1969) and studied by Nicholas M. Katz (1972), who settled the
Gauss–Manin / Picard–Fuchs case, the **Grothendieck–Katz conjecture** predicts that $f Y' = B Y$
admits an invertible fundamental matrix of solutions algebraic over $\mathbb{Q}(X)$ precisely when
the $p$-curvature vanishes for almost all primes $p$ (see also
`FormalConjectures/LittProblems/1.lean` for a related local-systems formulation on curves).

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Grothendieck%E2%80%93Katz_p-curvature_conjecture)
- [Wikipedia](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Algebra)
- [Ka72] N. M. Katz, *Algebraic solutions of differential equations ($p$-curvature and the Hodge
  filtration)*, Invent. Math. 18 (1972), 1–118.
- [Be92] D. Bertrand, *Groupes algébriques et équations différentielles linéaires*, Séminaire
  Bourbaki, Vol. 1991/92, Exp. 750, Astérisque 206 (1992), 183–204, §5.
-/

@[expose] public section

namespace GrothendieckKatzConjecture

/-- Cleared higher-derivative matrices $M_k \in M_n(\mathbb{Z}[X])$ for $f Y' = B Y$, satisfying
$f^k Y^{(k)} = M_k Y$ via $M_0 = I$ and $M_{k+1} = f M_k' - k f' M_k + M_k B$ ([Be92], §5). -/
noncomputable def clearedDerivMat {n : ℕ} (f : Polynomial ℤ)
    (B : Matrix (Fin n) (Fin n) (Polynomial ℤ)) :
    ℕ → Matrix (Fin n) (Fin n) (Polynomial ℤ)
  | 0 => 1
  | k + 1 =>
      let M := clearedDerivMat f B k
      Matrix.of fun i j ↦
        f * Polynomial.derivative (M i j) -
          (k : Polynomial ℤ) * Polynomial.derivative f * M i j +
          ∑ r, M i r * B r j

/-- The cleared $p$-curvature of $f Y' = B Y$ vanishes modulo $p$ when every entry of $M_p$ maps to
zero in $(\mathbb{Z}/p\mathbb{Z})[X]$. -/
def HasVanishingPCurvature {n : ℕ} (f : Polynomial ℤ)
    (B : Matrix (Fin n) (Fin n) (Polynomial ℤ)) (p : ℕ) : Prop :=
  ∀ i j : Fin n,
    Polynomial.map (Int.castRingHom (ZMod p)) (clearedDerivMat f B p i j) = 0

/-- An algebraic differential field extension $(L, D)$ of $\mathbb{Q}(X)$ equipped with a
derivation extending $\frac{d}{dX}$. -/
structure AlgebraicDiffExtension where
  /-- Underlying field of the extension. -/
  Carrier : Type
  [fieldInst : Field Carrier]
  [algInst : Algebra (Polynomial ℚ) Carrier]
  /-- Nonzero rational polynomials map to nonzero elements of `Carrier`. -/
  inj_poly : Function.Injective (algebraMap (Polynomial ℚ) Carrier)
  /-- Every element of `Carrier` is algebraic over $\mathbb{Q}[X]$ (hence over $\mathbb{Q}(X)$). -/
  [is_algebraic : Algebra.IsAlgebraic (Polynomial ℚ) Carrier]
  /-- Derivation operator extending $\frac{d}{dX}$. -/
  derivMap : Derivation ℤ Carrier Carrier
  /-- Normalization $D(X) = 1$. -/
  deriv_X : derivMap (algebraMap (Polynomial ℚ) Carrier Polynomial.X) = 1

attribute [instance] AlgebraicDiffExtension.fieldInst AlgebraicDiffExtension.algInst
  AlgebraicDiffExtension.is_algebraic

/-- The system $f Y' = B Y$ admits a full basis of solutions algebraic over $\mathbb{Q}(X)$ if some
`AlgebraicDiffExtension` $(L, D)$ contains $Y \in \mathrm{GL}_n(L)$ solving $f D(Y) = B Y$. -/
def HasAlgebraicFundamentalMatrix {n : ℕ} (f : Polynomial ℤ)
    (B : Matrix (Fin n) (Fin n) (Polynomial ℤ)) : Prop :=
  ∃ (E : AlgebraicDiffExtension) (Y : Matrix (Fin n) (Fin n) E.Carrier),
    IsUnit Y.det ∧
      ∀ i j : Fin n,
        algebraMap (Polynomial ℚ) E.Carrier (Polynomial.map (Int.castRingHom ℚ) f) *
            E.derivMap (Y i j) =
          ∑ r, algebraMap (Polynomial ℚ) E.Carrier (Polynomial.map (Int.castRingHom ℚ) (B i r)) *
            Y r j

/-- For the rank-$1$ equation $Y' = 0$, the $3$-curvature vanishes modulo $3$. -/
@[category test, AMS 11 12 14 34]
theorem hasVanishingPCurvature_zero_mod_three :
    HasVanishingPCurvature (1 : Polynomial ℤ) (fun _ _ : Fin 1 ↦ (0 : Polynomial ℤ)) 3 := by
  intro i j
  fin_cases i
  fin_cases j
  simp [clearedDerivMat]

/-- For $Y' = Y$ (solved by $e^X$, transcendental over $\mathbb{Q}(X)$), the $3$-curvature does not
vanish modulo $3$. -/
@[category test, AMS 11 12 14 34]
theorem not_hasVanishingPCurvature_exp_mod_three :
    ¬ HasVanishingPCurvature (1 : Polynomial ℤ) (fun _ _ : Fin 1 ↦ (1 : Polynomial ℤ)) 3 := by
  intro h
  have h00 := h 0 0
  simp [clearedDerivMat] at h00

/-- Scaling $f$ and $B$ by $c \in \mathbb{Z}$ preserves `HasAlgebraicFundamentalMatrix`. -/
@[category API, AMS 11 12 14 34]
theorem hasAlgebraicFundamentalMatrix_scale {n : ℕ} (c : ℤ) (f : Polynomial ℤ)
    (B : Matrix (Fin n) (Fin n) (Polynomial ℤ)) (h : HasAlgebraicFundamentalMatrix f B) :
    HasAlgebraicFundamentalMatrix (Polynomial.C c * f)
      (Matrix.of fun i j ↦ Polynomial.C c * B i j) := by
  rcases h with ⟨E, Y, hdet, hsol⟩
  refine ⟨E, Y, hdet, fun i j ↦ ?_⟩
  have hij := hsol i j
  simp only [Polynomial.map_mul, Polynomial.map_C, map_mul, Matrix.of_apply]
  calc
    (algebraMap (Polynomial ℚ) E.Carrier (Polynomial.C (Int.castRingHom ℚ c)) *
        algebraMap (Polynomial ℚ) E.Carrier (Polynomial.map (Int.castRingHom ℚ) f)) *
        E.derivMap (Y i j)
      = algebraMap (Polynomial ℚ) E.Carrier (Polynomial.C (Int.castRingHom ℚ c)) *
          (algebraMap (Polynomial ℚ) E.Carrier (Polynomial.map (Int.castRingHom ℚ) f) *
            E.derivMap (Y i j)) := by ring
    _ = algebraMap (Polynomial ℚ) E.Carrier (Polynomial.C (Int.castRingHom ℚ c)) *
          ∑ r, algebraMap (Polynomial ℚ) E.Carrier
            (Polynomial.map (Int.castRingHom ℚ) (B i r)) * Y r j := by rw [hij]
    _ = ∑ r, (algebraMap (Polynomial ℚ) E.Carrier (Polynomial.C (Int.castRingHom ℚ c)) *
          algebraMap (Polynomial ℚ) E.Carrier (Polynomial.map (Int.castRingHom ℚ) (B i r))) *
          Y r j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        ring

/-- The trivial rank-$1$ system $Y' = 0$ admits the invertible algebraic fundamental matrix
$Y = (1)$ over $\mathbb{Q}(X)$. -/
@[category test, AMS 11 12 14 34]
theorem hasAlgebraicFundamentalMatrix_zero :
    HasAlgebraicFundamentalMatrix (1 : Polynomial ℤ)
      (0 : Matrix (Fin 1) (Fin 1) (Polynomial ℤ)) := by
  let _ : Algebra ℤ (RatFunc ℚ) := Ring.toIntAlgebra _
  refine ⟨{ Carrier := RatFunc ℚ
            inj_poly := RatFunc.algebraMap_injective ℚ
            is_algebraic := RatFunc.isAlgebraic ℚ
            derivMap :=
              { toFun := RatFunc.derivAux ℚ
                map_add' := RatFunc.derivAux_add
                map_smul' := fun n x ↦ by
                  simpa using
                    map_zsmul (AddMonoidHom.mk' (RatFunc.derivAux ℚ) RatFunc.derivAux_add) n x
                map_one_eq_zero' := by
                  simpa using RatFunc.derivAux_algebraMap (1 : Polynomial ℚ)
                leibniz' := fun a b ↦ by simpa [smul_eq_mul] using RatFunc.derivAux_mul a b }
            deriv_X := by
              simpa using RatFunc.derivAux_algebraMap (Polynomial.X : Polynomial ℚ) },
          1, by simp, fun i j ↦ ?_⟩
  fin_cases i; fin_cases j
  simp

/-- **Grothendieck–Katz Conjecture on $p$-Curvature** ([Ka72]; [Be92], §5): For every rank
$n \ge 1$, nonzero denominator $f \in \mathbb{Z}[X]$, and matrix $B \in M_n(\mathbb{Z}[X])$, the
linear differential system $f Y' = B Y$ admits an invertible fundamental matrix of solutions
algebraic over $\mathbb{Q}(X)$ precisely when the $p$-curvature vanishes for all sufficiently large
primes $p$.

Note: As explained on Wikipedia, passing from an arbitrary rational-function matrix over
$\overline{\mathbb{Q}}(X)$ to a cleared system $f Y' = B Y$ with $f \in \mathbb{Z}[X] \setminus
\{0\}$ and $B \in M_n(\mathbb{Z}[X])$ by restriction of scalars captures the general conjecture; for
every prime $p$ not dividing all coefficients of $f$, vanishing of `HasVanishingPCurvature f B p`
coincides with vanishing of the $p$-curvature of $\frac{d}{dX} - f^{-1} B$ over $\mathbb{F}_p(X)$
([Be92], §5). -/
@[category research open, AMS 11 12 14 34]
theorem grothendieck_katz_p_curvature_conjecture (n : ℕ) (hn : 1 ≤ n) (f : Polynomial ℤ)
    (hf : f ≠ 0) (B : Matrix (Fin n) (Fin n) (Polynomial ℤ)) :
    HasAlgebraicFundamentalMatrix f B ↔
      ∃ P₀ : ℕ, ∀ p : ℕ, P₀ ≤ p → p.Prime → HasVanishingPCurvature f B p := by
  sorry

/-- **Rank-$1$ Case of the Grothendieck–Katz Conjecture** ([Ka72], §5): For scalar equations
$f Y' = B Y$ of rank $n = 1$ with $0 \ne f \in \mathbb{Z}[X]$, algebraicity of solutions over
$\mathbb{Q}(X)$ is equivalent to vanishing of the $p$-curvature for all sufficiently large primes
$p$ (stated in [Ka72], §5 via Kronecker's theorem on rational residues, rather than on the cited
Wikipedia page). -/
@[category research solved, AMS 11 12 14 34]
theorem grothendieck_katz_p_curvature_conjecture.variants.rank_one (f : Polynomial ℤ) (hf : f ≠ 0)
    (B : Matrix (Fin 1) (Fin 1) (Polynomial ℤ)) :
    HasAlgebraicFundamentalMatrix f B ↔
      ∃ P₀ : ℕ, ∀ p : ℕ, P₀ ≤ p → p.Prime → HasVanishingPCurvature f B p := by
  sorry

end GrothendieckKatzConjecture
