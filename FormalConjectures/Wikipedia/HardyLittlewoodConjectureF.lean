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
# Conjecture F of Hardy and Littlewood

G. H. Hardy and J. E. Littlewood (1923) formulated Conjecture F giving an asymptotic law for primes
represented by an admissible integer quadratic $f(x) = a x^2 + b x + c$ ($a > 0$,
$\gcd(a, b, c) = 1$, non-square discriminant $b^2 - 4 a c$, and $a + b, c$ not both even).
Writing $\omega_f(p)$ for the root count of $f$ modulo $p$ and
$C(f) = \prod_p \frac{p - \omega_f(p)}{p - 1}$, Conjecture F predicts
$P(n) \sim \frac{C(f)}{\sqrt{a}} \frac{\sqrt{n}}{\log n}$ for primes $f(x) < n$, or equivalently
$\frac{C(f)}{2} \frac{N}{\log N}$ over $1 \le x \le N$ (the single-quadratic case of Bateman–Horn).

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Ulam_spiral#Hardy_and_Littlewood%27s_Conjecture_F)
- G. H. Hardy and J. E. Littlewood, *Some problems of 'Partitio numerorum'; III: On the expression
  of a number as a sum of primes*, Acta Mathematica **44** (1923), no. 1, 1–70.
-/

@[expose] public section

open Asymptotics Filter Topology

namespace HardyLittlewoodConjectureF

/-- Admissibility hypotheses for $f(x) = a x^2 + b x + c$: $a > 0$, coprime coefficients,
non-square discriminant $b^2 - 4 a c$, and $a + b, c$ not both even. -/
def IsAdmissibleQuadratic (a b c : ℤ) : Prop :=
  0 < a ∧
    Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs = 1 ∧
    (¬ ∃ d : ℤ, d ^ 2 = b ^ 2 - 4 * a * c) ∧
    ¬ (2 ∣ (a + b) ∧ 2 ∣ c)

/-- Root count $\omega_f(p)$ of $a r^2 + b r + c \equiv 0 \pmod{p}$ in $\{0, \dots, p - 1\}$. -/
def quadModRootCount (a b c : ℤ) (p : ℕ) : ℕ :=
  ((Finset.range p).filter fun r : ℕ =>
    (a * (r : ℤ) ^ 2 + b * (r : ℤ) + c) % (p : ℤ) = 0).card

/-- Ordered partial Euler product $\prod_{p < P} \frac{p - \omega_f(p)}{p - 1}$ via
`Nat.primesBelow`. -/
noncomputable def singularProductPartial (a b c : ℤ) (P : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesBelow P,
    ((p : ℝ) - (quadModRootCount a b c p : ℝ)) / ((p : ℝ) - 1)

/-- Count $P(n)$ of primes below $n$ expressible as $a x^2 + b x + c$ ($x \in \mathbb{N}$). -/
noncomputable def quadPrimesBelow (a b c : ℤ) (n : ℕ) : ℕ :=
  {q : ℕ | q.Prime ∧ q < n ∧ ∃ x : ℕ, a * (x : ℤ) ^ 2 + b * (x : ℤ) + c = (q : ℤ)}.ncard

/-- Count of integers $1 \le m \le N$ where $a m^2 + b m + c$ is a positive prime. -/
def quadPrimeCount (a b c : ℤ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter fun m : ℕ =>
    let val : ℤ := a * (m : ℤ) ^ 2 + b * (m : ℤ) + c
    0 < val ∧ val.natAbs.Prime).card

/-- Polynomial $m^2 + 1$ ($a = 1, b = 0, c = 1$) satisfies `IsAdmissibleQuadratic`. -/
@[category test, AMS 11]
theorem isAdmissibleQuadratic_landau : IsAdmissibleQuadratic 1 0 1 := by
  refine ⟨by omega, by decide, ?_, by omega⟩
  rintro ⟨d, hd⟩
  have h0 : 0 ≤ d ^ 2 := sq_nonneg d
  linarith

/-- Root count of $m^2 + 1$ modulo $2$ equals $1$. -/
@[category test, AMS 11]
theorem quadModRootCount_landau_two : quadModRootCount 1 0 1 2 = 1 := by
  decide

/-- Root count of $m^2 + 1$ modulo $3$ equals $0$. -/
@[category test, AMS 11]
theorem quadModRootCount_landau_three : quadModRootCount 1 0 1 3 = 0 := by
  decide

/-- Partial product for $m^2 + 1$ over primes $p < 4$ equals $\frac{2 - 1}{1} \cdot \frac{3 - 0}{2}
= \frac{3}{2}$. -/
@[category test, AMS 11]
theorem singularProductPartial_landau_four :
    singularProductPartial 1 0 1 4 = 3 / 2 := by
  unfold singularProductPartial
  have hset : Nat.primesBelow 4 = {2, 3} := by decide
  have hr2 : quadModRootCount 1 0 1 2 = 1 := by decide
  have hr3 : quadModRootCount 1 0 1 3 = 0 := by decide
  rw [hset, Finset.prod_pair (by decide), hr2, hr3]
  norm_num

/-- Among $1 \le m \le 4$, $m^2 + 1$ yields primes at $m = 1, 2, 4$ ($2, 5, 17$). -/
@[category test, AMS 11]
theorem quadPrimeCount_landau_four : quadPrimeCount 1 0 1 4 = 3 := by
  decide

/--
**Conjecture F** (Hardy–Littlewood, 1923): for every admissible integer quadratic
$f(x) = a x^2 + b x + c$, `singularProductPartial a b c P` converges to a constant $C > 0$, and
`quadPrimesBelow a b c n` (counting primes $f(x) < n$ with $x \in \mathbb{N}$) grows asymptotically
as $\frac{C}{\sqrt{a}} \frac{\sqrt{n}}{\log n}$ as $n \to \infty$.
-/
@[category research open, AMS 11]
theorem hardy_littlewood_conjecture_f (a b c : ℤ) (hf : IsAdmissibleQuadratic a b c) :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (singularProductPartial a b c) atTop (𝓝 C) ∧
      (fun n : ℕ => (quadPrimesBelow a b c n : ℝ)) ~[atTop]
        (fun n : ℕ => C / Real.sqrt (a : ℝ) * Real.sqrt (n : ℝ) / Real.log (n : ℝ)) := by
  sorry

/--
Index-counting formulation of Conjecture F: for every admissible integer quadratic
$f(m) = a m^2 + b m + c$, `quadPrimeCount a b c N` is asymptotic to $\frac{C}{2} \frac{N}{\log N}$
as $N \to \infty$, where $C = \lim_{P \to \infty}$ `singularProductPartial a b c P`.
-/
@[category research open, AMS 11]
theorem hardy_littlewood_conjecture_f.variants.index_count
    (a b c : ℤ) (hf : IsAdmissibleQuadratic a b c) :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (singularProductPartial a b c) atTop (𝓝 C) ∧
      (fun N : ℕ => (quadPrimeCount a b c N : ℝ)) ~[atTop]
        (fun N : ℕ => (C / 2) * (N : ℝ) / Real.log (N : ℝ)) := by
  sorry

end HardyLittlewoodConjectureF
