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
# Prime values and primitive divisors in elliptic divisibility sequences

Morgan Ward (1948) studied integer divisibility sequences $(W_n)_{n \in \mathbb{Z}}$ satisfying
the elliptic recurrence $W_{m+n} W_{m-n} W_1^2 = W_{m+1} W_{m-1} W_n^2 - W_{n+1} W_{n-1} W_m^2$.
A normalized sequence ($W_1 = 1$) is *nonsingular* when its discriminant is nonzero—equivalently,
by Ward's representation theorem, when $(W_n)$ evaluates the division polynomials $\psi_n(x, y)$
at a rational point on an elliptic curve $E / \mathbb{Q}$ ($\Delta_E \ne 0$). In Ward's and
Einsiedler–Everest–Ward's (§2) terminology, an elliptic divisibility sequence is *proper* when
$W_0 = 0$, $W_1 = 1$, and $W_2 W_3 \ne 0$; for a normalized nonsingular sequence, non-periodicity
($W_n \ne 0$ for all $n \ne 0$, corresponding to a non-torsion rational point) automatically
ensures properness and positive quadratic logarithmic growth. Joseph H. Silverman (1988) proved
that all sufficiently large terms of a non-periodic nonsingular sequence admit primitive prime
divisors, while Manfred Einsiedler, Graham Everest, and Thomas Ward (2001) conjectured that
$|W_n|$ is prime for only finitely many indices $n \ge 1$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
- M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. **70** (1948), 31–74.
- J. H. Silverman, *Wieferich's criterion and the $abc$-conjecture*, J. Number Theory **30**
  (1988), no. 2, 226–237.
- M. Einsiedler, G. Everest, and T. Ward, *Primes in elliptic divisibility sequences*, LMS J.
  Comput. Math. **4** (2001), 1–13.
-/

@[expose] public section

namespace EllipticDivisibilitySequence

/-- `W : ℤ → ℤ` is a normalized nonsingular elliptic divisibility sequence: it satisfies
`IsEllipticDvdSequence W` with `W 1 = 1` and evaluates the division polynomials `E.ψ n` at an
affine rational point on a nonsingular curve `E : WeierstrassCurve ℚ` (`E.Δ ≠ 0`). -/
def IsNonsingularEDS (W : ℤ → ℤ) : Prop :=
  IsEllipticDvdSequence W ∧
  W 1 = 1 ∧
  ∃ (E : WeierstrassCurve ℚ) (x y : ℚ),
    E.Δ ≠ 0 ∧ E.toAffine.Equation x y ∧
    ∀ n : ℤ, (W n : ℚ) = (E.ψ n).evalEval x y

/-- Zero sequence fails the normalization condition `W 1 = 1` in `IsNonsingularEDS`. -/
@[category test, AMS 11 14]
theorem not_isNonsingularEDS_zero : ¬ IsNonsingularEDS 0 := by
  rintro ⟨_, h1, _⟩
  exact zero_ne_one h1

/-- On Cremona's curve `37a1` ($Y^2 + Y = X^3 - X$), the discriminant is `37 ≠ 0` and `(0, 0)` is
an affine rational point whose division-polynomial evaluations begin $\psi_1 = 1$, $\psi_2 = 1$,
$\psi_3 = -1$, $\psi_4 = 1$, and $\psi_5 = 2$ (`OEIS A006769`). -/
@[category test, AMS 11 14]
theorem cremona37a1_discriminant_and_point :
    let E : WeierstrassCurve ℚ := ⟨0, 0, 1, -1, 0⟩
    E.Δ = 37 ∧ E.toAffine.Equation 0 0 ∧
      (E.ψ 1).evalEval 0 0 = 1 ∧ (E.ψ 2).evalEval 0 0 = 1 ∧
      (E.ψ 3).evalEval 0 0 = -1 ∧ (E.ψ 4).evalEval 0 0 = 1 ∧
      (E.ψ 5).evalEval 0 0 = 2 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  · simp [WeierstrassCurve.Affine.equation_iff]
  · simp
  · norm_num [WeierstrassCurve.ψ, WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
  · simp [WeierstrassCurve.ψ_three, Polynomial.evalEval_C, WeierstrassCurve.Ψ₃,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  · norm_num [WeierstrassCurve.ψ_four, Polynomial.evalEval_C, WeierstrassCurve.ψ₂,
      WeierstrassCurve.preΨ₄, WeierstrassCurve.Affine.polynomialY, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  · have h5 : (5 : ℤ) = 2 * 2 + 1 := by norm_num
    rw [h5, WeierstrassCurve.ψ_odd]
    norm_num [WeierstrassCurve.ψ_four, WeierstrassCurve.ψ_three, WeierstrassCurve.ψ_two,
      WeierstrassCurve.ψ_one, Polynomial.evalEval_C, WeierstrassCurve.ψ₂, WeierstrassCurve.Ψ₃,
      WeierstrassCurve.preΨ₄, WeierstrassCurve.Affine.polynomialY, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- For $W_n = n$, $W_5 = 5$ has primitive prime divisor $5$, whereas $W_1 = 1$ has none. -/
@[category test, AMS 11 14]
theorem intId_primitivePrimeDivisor_five_and_not_one :
    HasPrimitivePrimeDivisor (id : ℤ → ℤ) 5 ∧ ¬ HasPrimitivePrimeDivisor (id : ℤ → ℤ) 1 := by
  refine ⟨⟨5, by norm_num, dvd_rfl, ?_⟩, ?_⟩
  · intro k hk1 hk5 hdiv
    have hk_pos : 0 < (k : ℤ) := by exact_mod_cast hk1
    have hle : (5 : ℤ) ≤ (k : ℤ) := Int.le_of_dvd hk_pos hdiv
    omega
  · rintro ⟨p, hp, hdiv, _⟩
    have hu : (p : ℤ) ≤ 1 := Int.le_of_dvd zero_lt_one hdiv
    have hp2 := hp.two_le
    omega

/-- Einsiedler–Everest–Ward Conjecture (2001): every non-periodic (`∀ n ≠ 0, W n ≠ 0`) normalized
nonsingular elliptic divisibility sequence takes prime values $|W_n|$ at finitely many indices
$n \ge 1$. (Einsiedler–Everest–Ward, eq. (10), p. 5 also study sequences obtained by dividing out
bad-reduction factors, which need not satisfy the elliptic divisibility recurrence.) -/
@[category research open, AMS 11 14]
theorem einsiedler_everest_ward_finite_primes :
    ∀ W : ℤ → ℤ,
      IsNonsingularEDS W →
      (∀ n : ℤ, n ≠ 0 → W n ≠ 0) →
      {n : ℕ | 1 ≤ n ∧ (W n).natAbs.Prime}.Finite := by
  sorry

/-- Silverman's Primitive Divisor Theorem (1988): every non-periodic (`∀ n ≠ 0, W n ≠ 0`)
normalized nonsingular elliptic divisibility sequence has a primitive prime divisor for all
sufficiently large $n$. -/
@[category research solved, AMS 11 14]
theorem silverman_eds_primitive_prime_divisors :
    ∀ W : ℤ → ℤ,
      IsNonsingularEDS W →
      (∀ n : ℤ, n ≠ 0 → W n ≠ 0) →
      ∀ᶠ n in Filter.atTop, HasPrimitivePrimeDivisor W n := by
  sorry

end EllipticDivisibilitySequence
