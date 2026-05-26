/-
Copyright 2025 The Formal Conjectures Authors.

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

*Reference:* [arxiv/2501.13175](https://arxiv.org/abs/2501.13175)
**Algebraicity and integrality of solutions to differential equations**
by *Yeuk Hay Joshua Lam, Daniel Litt*
-/

open Real MvPolynomial

namespace LamLitt

/--
A power series $f$ is a solution of an algebraic ODE defined by the rational function
$g \in \mathbb{Q}(z, y_0, \dots, y_{n-1})$ if $f^{(n)}(z) = g(z, f(z), f'(z), \dots, f^{(n-1)}(z))$.
The variable indexed by `0 : Fin (n + 1)` corresponds to $z$, and the variable indexed by
`i.succ` corresponds to $y_i = f^{(i)}(z)$.
-/
def IsSolutionOfAlgebraicODE (n : ℕ) (f : PowerSeries ℚ) (g : MvRatFunc (Fin (n + 1)) ℚ) : Prop :=
  ∃ p q : MvPolynomial (Fin (n + 1)) ℚ,
    g = (algebraMap _ _ p) / (algebraMap _ _ q) ∧
    let pt : Fin (n + 1) → PowerSeries ℚ :=
      Fin.cases PowerSeries.X (fun i : Fin n ↦ PowerSeries.derivativeFun^[i.val] f)
    IsUnit (MvPolynomial.aeval pt q) ∧
    PowerSeries.derivativeFun^[n] f * MvPolynomial.aeval pt q = MvPolynomial.aeval pt p

def ℤAdjoinInvNat (N : ℕ) : Subalgebra ℤ ℚ := Algebra.adjoin ℤ {(1 / N : ℚ)}

/--
There exists $N$ such that for all $n$, the $n$-th coefficient of $f$ is in $\mathbb{Z}[1/N]$.
-/
def IsCoeffIntegralAdjointInvNat (f : PowerSeries ℚ) (N : ℕ) : Prop :=
  ∀ n : ℕ, PowerSeries.coeff n f ∈ ℤAdjoinInvNat N

/--
A rational function $g$ is defined at a point $x_0$ if $g$ can be written as $p / q$
where $p, q$ are polynomials and $q(x_0) \neq 0$.
-/
def IsDefined (n : ℕ) (g : MvRatFunc (Fin n) ℚ) (x₀ : Fin n → ℚ) : Prop :=
  ∃ p q : MvPolynomial (Fin n) ℚ, g = (algebraMap _ _ p) / (algebraMap _ _ q) ∧ q.eval x₀ ≠ 0

/--
For a function $\omega$ on the set of primes and a sequence $a_n$ of rational numbers,
the condition $\omega$-integrality means that for each prime $p$, the rational numbers
$a_0, a_1, \dots, a_{\omega(p)}$ are in $\mathbb{Z}_{(p)}$, i.e. their denominators
are not divisible by $p$.
-/
def omegaIntegral (ω : Nat.Primes → ℕ) (a : ℕ → ℚ) : Prop :=
  ∀ p : Nat.Primes, ∀ j ∈ Set.Icc 0 (ω p), Nat.Coprime (a j).den p

/--
The growth condition on $\omega$: the ratio $\omega(p) / p$ tends to infinity as the prime $p$
tends to infinity, i.e. $\lim_{p \to \infty} \omega(p) / p = \infty$. Here the source filter is
`Filter.atTop` on the primes, obtained by pulling back `Filter.atTop` on $\mathbb{N}$ along the
coercion `Nat.Primes → ℕ`.
-/
def omegaSuperlinear (ω : Nat.Primes → ℕ) : Prop :=
  Filter.Tendsto (fun p : Nat.Primes ↦ (ω p : ℝ) / p)
    (Filter.comap (fun p : Nat.Primes ↦ (p : ℕ)) Filter.atTop) Filter.atTop

/--
**Lam--Litt conjecture**: Let $g \in \mathbb{Q}(z, y_0, \dots, y_{n-1})$ be a rational function in
$n + 1$ variables. Let $f$ be a power series over $\mathbb{Q}$ such that
$f^{(n)}(z) = g(z, f(z), f'(z), \dots, f^{(n-1)}(z))$.
Also, assume that $g(0, f(0), f'(0), \dots, f^{(n-1)}(0))$ is defined.
Then the following are equivalent:

1) $f$ is algebraic over $\mathbb{Q}[z]$.
2) There exists $N$ such that for all $n$, the $n$-th coefficient of $f$ is in $\mathbb{Z}[1/N]$.
3) There exists an integer-valued function $\omega$ on the set of primes with
$\lim_{p \to \infty} \omega(p) / p = \infty$ such that, for each prime $p$,
the rational numbers $a_0, a_1, \dots, a_{\omega(p)}$ are in $\mathbb{Z}_{(p)}$.
-/
@[category research open, AMS 12]
theorem lam_litt {n : ℕ} (f : PowerSeries ℚ) (g : MvRatFunc (Fin (n + 1)) ℚ)
  (hODE : IsSolutionOfAlgebraicODE n f g) :
    List.TFAE [
      IsAlgebraic (Polynomial ℚ) f,
      (∃ N : ℕ, IsCoeffIntegralAdjointInvNat f N),
      (∃ ω : Nat.Primes → ℕ, omegaSuperlinear ω ∧ omegaIntegral ω (PowerSeries.coeff · f))
    ] := by
  sorry

end LamLitt
