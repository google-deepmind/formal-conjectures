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
# Lam--Litt conjecture

A conjecture of Lam and Litt on algebraic solutions of algebraic ODEs.

Let $g \in \mathbb{Q}(z, y_0, \dots, y_{n-1})$ be a rational function in
$n + 1$ variables. Let $f$ be a power series over $\mathbb{Q}$ such that
$f^{(n)}(z) = g(z, f(z), f'(z), \dots, f^{(n-1)}(z))$.
Also, assume that $g(0, f(0), f'(0), \dots, f^{(n-1)}(0))$ is defined.
Then the following are equivalent:

1) $f$ is algebraic over $\mathbb{Q}[z]$.
2) There exists $N$ such that for all $n$, the $n$-th coefficient of $f$ is in $\mathbb{Z}[1/N]$.
3) There exists an integer-valued function $\omega$ on the set of primes with
$\lim_{p \to \infty} \omega(p) / p = \infty$ such that, for each prime $p$,
the rational numbers $a_0, a_1, \dots, a_{\omega(p)}$ are in $\mathbb{Z}_{(p)}$.

The implication 1) => 2) is due to Eisenstein, and 2) => 3) is trivial.

*References:*
- [Litt's problem 1](https://www.problemsilike.com/1)
- Yeuk Hay Joshua Lam, Daniel Litt, "Algebraicity and integrality of solutions to differential equations",
  [arxiv/2501.13175](https://arxiv.org/abs/2501.13175)
- Gotthold Eisenstein. "Über eine allgemeine Eigenschaft der Reihen-Entwicklungen aller algebraischen Funktionen",
  Bericht der Königl. Preuss. Akademie der Wissenschaften zu Berlin, 1852

TODO:
- Lam-Litt conjecture implies Grothendieck p-curvature conjecture.
- Examples in Remark 1.1.3 and 1.1.5 on the conditions of the conjecture.
-/

open Real MvPolynomial PowerSeries

namespace LamLitt

/--
A power series $f$ is a solution of an algebraic ODE defined by the rational function
$g \in \mathbb{Q}(z, y_0, \dots, y_{n-1})$ if $f^{(n)}(z) = g(z, f(z), f'(z), \dots, f^{(n-1)}(z))$.
The variable indexed by `0 : Fin (n + 1)` corresponds to $z$, and the variable indexed by
`i.succ` corresponds to $y_i = f^{(i)}(z)$.
-/
def IsSolutionOfAlgebraicODE (n : ℕ) (f : PowerSeries ℚ) (g : MvRatFunc (Fin (n + 1)) ℚ) : Prop :=
  let pt : Fin (n + 1) → PowerSeries ℚ := Fin.cases X (fun i : Fin n ↦ derivativeFun^[i.val] f)
  ∃ p q : MvPolynomial (Fin (n + 1)) ℚ,
    g = (algebraMap _ _ p) / (algebraMap _ _ q) ∧
    IsDefined (Fin (n + 1)) ℚ g (PowerSeries.constantCoeff ∘ pt) ∧
    derivativeFun^[n] f * MvPolynomial.aeval pt q = MvPolynomial.aeval pt p

def ℤAdjoinInvNat (N : ℕ) : Subalgebra ℤ ℚ := Algebra.adjoin ℤ {(1 / N : ℚ)}

/--
There exists $N$ such that for all $n$, the $n$-th coefficient of $f$ is in $\mathbb{Z}[1/N]$.
-/
def IsCoeffIntegralAdjointInvNat (f : PowerSeries ℚ) (N : ℕ) : Prop :=
  ∀ n : ℕ, coeff n f ∈ ℤAdjoinInvNat N

/--
For an integer-valued function $\omega$ on the set of primes and a sequence $a_n$ of rational
numbers, the condition $\omega$-integrality means that for each prime $p$, the rational numbers
$a_0, a_1, \dots, a_{\omega(p)}$ are in $\mathbb{Z}_{(p)}$, i.e. their denominators are not
divisible by $p$. When $\omega(p) < 0$ the constraint at $p$ is vacuous.
-/
def omegaIntegral (ω : Nat.Primes → ℤ) (a : ℕ → ℚ) : Prop :=
  ∀ p : Nat.Primes, ∀ j : ℕ, (j : ℤ) ≤ ω p → Nat.Coprime (a j).den p

/--
The growth condition on $\omega$: the ratio $\omega(p) / p$ tends to infinity as the prime $p$
tends to infinity, i.e. $\lim_{p \to \infty} \omega(p) / p = \infty$. Here the source filter is
`Filter.atTop` on the primes, obtained by pulling back `Filter.atTop` on $\mathbb{N}$ along the
coercion `Nat.Primes → ℕ`.
-/
def omegaSuperlinear (ω : Nat.Primes → ℤ) : Prop :=
  Filter.Tendsto (fun p : Nat.Primes ↦ (ω p : ℝ) / p)
    (Filter.comap (fun p : Nat.Primes ↦ (p : ℕ)) Filter.atTop) Filter.atTop

/--
Eisenstein's theorem (1852): an algebraic power series over $\mathbb{Q}[z]$ has bounded
denominators, i.e., there exists $N$ such that all coefficients lie in $\mathbb{Z}[1/N]$.
-/
@[category research solved, AMS 12 13]
theorem lam_litt.variants.eisenstein (f : PowerSeries ℚ) (hAlg : IsAlgebraic (Polynomial ℚ) f) :
    ∃ N : ℕ, IsCoeffIntegralAdjointInvNat f N := by
  sorry

/-- Every element of $\mathbb{Z}[1/N]$ has denominator coprime to any prime $p$ not in the
prime factor set of $N$ (vacuously, the case $N = 0$ gives $\mathbb{Z}[1/N] = \mathbb{Z}$). -/
@[category API, AMS 11]
private lemma den_coprime_of_mem_adjoinInvNat {N p : ℕ} (hp : p.Prime)
    (hpN : p ∉ N.primeFactors) {q : ℚ} (hq : q ∈ ℤAdjoinInvNat N) :
    Nat.Coprime q.den p := by
  induction hq using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx; subst hx
    rcases eq_or_ne N 0 with rfl | hN
    · simp
    · rw [one_div, Rat.inv_natCast_den_of_pos (Nat.pos_of_ne_zero hN)]
      exact (hp.coprime_iff_not_dvd.mpr fun h => hpN <| Nat.mem_primeFactors.mpr ⟨hp, h, hN⟩).symm
  | algebraMap _ => simp
  | add _ _ _ _ ihx ihy => exact (ihx.mul_left ihy).coprime_dvd_left (Rat.add_den_dvd _ _)
  | mul _ _ _ _ ihx ihy => exact (ihx.mul_left ihy).coprime_dvd_left (Rat.mul_den_dvd _ _)

/--
Textbook implication: integrality (2) trivially implies ω(p)-integrality (3).
-/
@[category textbook, AMS 12]
theorem lam_litt.variants.integrality_implies_omega_integrality
    (f : PowerSeries ℚ) (N : ℕ) (hN : IsCoeffIntegralAdjointInvNat f N) :
    ∃ ω : Nat.Primes → ℤ, omegaSuperlinear ω ∧ omegaIntegral ω (PowerSeries.coeff · f) := by
  -- Take ω(p) = -1 if p divides N, else p^2.
  refine ⟨fun p => if (p : ℕ) ∈ N.primeFactors then (-1 : ℤ) else (p : ℤ)^2, ?_, ?_⟩
  · refine ((tendsto_natCast_atTop_atTop (R := ℝ)).comp Filter.tendsto_comap).congr' ?_
    filter_upwards [(Filter.eventually_gt_atTop N).comap ((↑) : Nat.Primes → ℕ)] with p hpN_lt
    have hpN : (p : ℕ) ∉ N.primeFactors := fun hmem => Nat.not_lt.mpr (Nat.le_of_mem_primeFactors hmem) hpN_lt
    simp [hpN, sq, p.2.ne_zero]
  · intro p j hj
    by_cases hpmem : (p : ℕ) ∈ N.primeFactors
    · simp only [hpmem, if_true] at hj; omega
    · exact den_coprime_of_mem_adjoinInvNat p.2 hpmem (hN j)

/--
3) implies 2): if the coefficients of $f$ satisfy the $\omega$-integrality condition for some superlinear $\omega$,
then there exists $N$ such that for all $n$, the $n$-th coefficient of $f$ is in $\mathbb{Z}[1/N]$.
-/
@[category research open, AMS 11 14]
theorem lam_litt.variants.omega_integrality_implies_algebraicity {n : ℕ} (f : PowerSeries ℚ)
    (g : MvRatFunc (Fin (n + 1)) ℚ) (hODE : IsSolutionOfAlgebraicODE n f g)
    (ω : Nat.Primes → ℤ) (hω : omegaSuperlinear ω ∧ omegaIntegral ω (PowerSeries.coeff · f)) :
    ∃ N : ℕ, IsCoeffIntegralAdjointInvNat f N := by
  sorry

/--
2) implies 1): if the coefficients of $f$ are in $\mathbb{Z}[1/N]$ for some $N$, then $f$ is algebraic over $\mathbb{Q}[z]$.
Also the version of conjecture of Litt's problem 1 on his website.
-/
@[category research open, AMS 11 14]
theorem lam_litt.variants.integrality_implies_algebraicity {n : ℕ} (f : PowerSeries ℚ)
    (g : MvRatFunc (Fin (n + 1)) ℚ) (hODE : IsSolutionOfAlgebraicODE n f g)
    (N : ℕ) (hN : IsCoeffIntegralAdjointInvNat f N) :
    IsAlgebraic (Polynomial ℚ) f := by
  sorry

end LamLitt
