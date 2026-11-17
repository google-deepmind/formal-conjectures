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
A normalized sequence ($W_1 = 1$, $W_2 \ne 0$) is *proper* when $\gcd(W_2, W_3) = 1$ (excluding
common prime factors across all $W_n$ for $n \ge 2$, such as scalings $c^{n^2 - 1} W_n$) and
*nonsingular* when $(W_n)$ arises by evaluating the division polynomials $\psi_n(x, y)$ at a
rational point on an elliptic curve $E / \mathbb{Q}$ ($\Delta_E \ne 0$). Non-periodic nonsingular
sequences have positive quadratic logarithmic growth $\lim_{n \to \infty} (\log |W_n|) / n^2 > 0$.
Joseph H. Silverman (1988) proved that all sufficiently large terms possess primitive prime
divisors, while Manfred Einsiedler, Graham Everest, and Thomas Ward (2001) conjectured that
$|W_n|$ is prime at finitely many indices $n \ge 1$.

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

/-- `W : ℤ → ℤ` is a proper normalized nonsingular elliptic divisibility sequence: it satisfies
`IsEllipticDvdSequence W` with `W 1 = 1`, `W 2 ≠ 0`, and `Int.gcd (W 2) (W 3) = 1`, and evaluates
the division polynomials `E.ψ n` at an affine rational point on a nonsingular curve
`E : WeierstrassCurve ℚ` (`E.Δ ≠ 0`). -/
def IsProperNonsingularEDS (W : ℤ → ℤ) : Prop :=
  IsEllipticDvdSequence W ∧
  W 1 = 1 ∧
  W 2 ≠ 0 ∧
  Int.gcd (W 2) (W 3) = 1 ∧
  ∃ (E : WeierstrassCurve ℚ) (x y : ℚ),
    E.Δ ≠ 0 ∧ E.toAffine.Equation x y ∧
    ∀ n : ℤ, (W n : ℚ) = (E.ψ n).evalEval x y

/-- Positive canonical-height growth condition: $(\log |W_n|) / n^2 \to c$ for some $c > 0$ as
$n \to \infty$ (ruling out periodic sequences from torsion points). -/
def HasQuadraticLogGrowth (W : ℤ → ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    Filter.Tendsto (fun n : ℕ => Real.log |(W n : ℝ)| / (n : ℝ) ^ 2) Filter.atTop (nhds c)

/-- Prime $p$ is a primitive divisor of $W_n$ when $p \mid W_n$ and $p \nmid W_k$ for every
$1 \le k < n$. -/
def HasPrimitivePrimeDivisor (W : ℤ → ℤ) (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ W n ∧ ∀ k : ℕ, 1 ≤ k → k < n → ¬ ((p : ℤ) ∣ W k)

/-- Improper scaled sequence $W_n = 2^{n^2 - 1} n$ violates $\gcd(W_2, W_3) = 1$, so
`IsProperNonsingularEDS` rejects it. -/
@[category test, AMS 11 14]
theorem not_isProperNonsingularEDS_scaled_id :
    ¬ IsProperNonsingularEDS (fun n : ℤ => (2 : ℤ) ^ (n.natAbs ^ 2 - 1) * n) := by
  rintro ⟨_, _, _, hgcd, _⟩
  revert hgcd
  decide

/-- On Cremona's curve `37a1` ($Y^2 + Y = X^3 - X$), the discriminant is `37 ≠ 0` and `(0, 0)` is
an affine rational point whose division-polynomial evaluations begin $\psi_1 = 1$, $\psi_2 = 1$,
$\psi_3 = -1$, and $\psi_5 = 2$ (`OEIS A006769`). -/
@[category test, AMS 11 14]
theorem cremona37a1_discriminant_and_point :
    let E : WeierstrassCurve ℚ := ⟨0, 0, 1, -1, 0⟩
    E.Δ = 37 ∧ E.toAffine.Equation 0 0 ∧
      (E.ψ 1).evalEval 0 0 = 1 ∧ (E.ψ 2).evalEval 0 0 = 1 ∧
      (E.ψ 3).evalEval 0 0 = -1 ∧ (E.ψ 5).evalEval 0 0 = 2 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  · simp [WeierstrassCurve.Affine.equation_iff]
  · simp
  · norm_num [WeierstrassCurve.ψ, WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
  · simp [WeierstrassCurve.ψ_three, Polynomial.evalEval_C, WeierstrassCurve.Ψ₃,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  · have h5 : (5 : ℤ) = 2 * 2 + 1 := by norm_num
    rw [h5, WeierstrassCurve.ψ_odd]
    norm_num [WeierstrassCurve.ψ_four, WeierstrassCurve.ψ_three, WeierstrassCurve.ψ_two,
      WeierstrassCurve.ψ_one, Polynomial.evalEval_C, WeierstrassCurve.ψ₂, WeierstrassCurve.Ψ₃,
      WeierstrassCurve.preΨ₄, WeierstrassCurve.Affine.polynomialY, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- For $W_n = n$, $W_5 = 5$ has primitive prime divisor $5$, whereas $W_1 = 1$ has none. -/
@[category test, AMS 11 14]
theorem intId_primitivePrimeDivisor_five_and_not_one :
    HasPrimitivePrimeDivisor id 5 ∧ ¬ HasPrimitivePrimeDivisor id 1 := by
  refine ⟨⟨5, by norm_num, dvd_rfl, ?_⟩, ?_⟩
  · intro k hk1 hk5 hdiv
    have hk_pos : 0 < (k : ℤ) := by exact_mod_cast hk1
    have hle : (5 : ℤ) ≤ (k : ℤ) := Int.le_of_dvd hk_pos hdiv
    omega
  · rintro ⟨p, hp, hdiv, _⟩
    have hu : (p : ℤ) ≤ 1 := Int.le_of_dvd zero_lt_one hdiv
    have hp2 := hp.two_le
    omega

/-- Constant sequence $W_n = 1$ has zero logarithmic growth rate, so `HasQuadraticLogGrowth`
fails. -/
@[category test, AMS 11 14]
theorem not_hasQuadraticLogGrowth_const_one :
    ¬ HasQuadraticLogGrowth (fun _ : ℤ => 1) := by
  rintro ⟨c, hc, htend⟩
  have hzero : (fun n : ℕ => Real.log |((1 : ℤ) : ℝ)| / (n : ℝ) ^ 2) = fun _ => 0 := by
    ext n
    simp
  rw [hzero] at htend
  have hc0 : c = 0 := tendsto_nhds_unique htend tendsto_const_nhds
  linarith

/-- Einsiedler–Everest–Ward Conjecture (2001): every proper normalized nonsingular elliptic
divisibility sequence with positive quadratic logarithmic growth takes prime values $|W_n|$ at
finitely many indices $n \ge 1$. -/
@[category research open, AMS 11 14]
theorem ward_elliptic_divisibility_finite_primes :
    ∀ W : ℤ → ℤ,
      IsProperNonsingularEDS W →
      HasQuadraticLogGrowth W →
      {n : ℕ | 1 ≤ n ∧ (W n).natAbs.Prime}.Finite := by
  sorry

/-- Silverman's Primitive Divisor Theorem (1988): every proper normalized nonsingular elliptic
divisibility sequence with positive quadratic logarithmic growth has a primitive prime divisor for
all sufficiently large $n$. -/
@[category research solved, AMS 11 14]
theorem silverman_eds_primitive_prime_divisors :
    ∀ W : ℤ → ℤ,
      IsProperNonsingularEDS W →
      HasQuadraticLogGrowth W →
      ∀ᶠ n in Filter.atTop, HasPrimitivePrimeDivisor W n := by
  sorry

end EllipticDivisibilitySequence
