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
# The Mertens Conjecture and the Mertens Function

The *Mertens function* $M(n) = \sum_{k=1}^n \mu(k)$ sums the Möbius function $\mu$
(`ArithmeticFunction.moebius`) over $1 \le k \le n$. Following an 1885 letter of Stieltjes to
Hermite, Mertens [Me1897] conjectured that $|M(n)| < \sqrt{n}$ for all $n \ge 2$. Odlyzko and
te Riele [OtR85] disproved this bound in 1985 via lattice basis reduction on explicit formulas,
showing $\limsup_{n \to \infty} M(n) / \sqrt{n} > 1.06$ and
$\liminf_{n \to \infty} M(n) / \sqrt{n} < -1.009$. Stieltjes also claimed in 1885 without proof
that $M(n) / \sqrt{n}$ is bounded ($M(n) = O(n^{1/2})$), whereas heuristics such as Gonek's
$(\log \log \log n)^{5/4}$ prediction suggest that $|M(n)| / \sqrt{n}$ is unbounded; whether
$M(n) = O(n^{1/2})$ holds remains open.

*References:*
- [Wikipedia: Mertens conjecture](https://en.wikipedia.org/wiki/Mertens_conjecture)
- [Me1897] F. Mertens, *Über eine zahlentheoretische Funktion*, Sitzungsber. Kaiserl. Akad. Wiss.
  Wien, Math.-Naturwiss. Kl., Abt. IIa **106** (1897), 761–830.
- [OtR85] A. M. Odlyzko and H. J. J. te Riele, *Disproof of the Mertens conjecture*, J. Reine
  Angew. Math. **357** (1985), 138–160. https://doi.org/10.1515/crll.1985.357.138
-/

@[expose] public section

namespace MertensConjecture

open Filter
open scoped Asymptotics

/-- The Mertens function $M(n) = \sum_{k=1}^n \mu(k)$. -/
def mertensFunction (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.moebius k

/-- At $n = 0$, the empty sum gives $M(0) = 0$. -/
@[category test, AMS 11]
theorem mertensFunction_zero : mertensFunction 0 = 0 := by
  decide

/-- At $n = 1$, $M(1) = \mu(1) = 1$, so strict inequality $|M(1)| < \sqrt{1}$ fails. -/
@[category test, AMS 11]
theorem mertensFunction_one : mertensFunction 1 = 1 := by
  simp [mertensFunction]

/-- At $n = 2$, $M(2) = \mu(1) + \mu(2) = 0$. -/
@[category test, AMS 11]
theorem mertensFunction_two : mertensFunction 2 = 0 := by
  rw [mertensFunction, show Finset.Icc 1 2 = {1, 2} by decide]
  have h1 : ArithmeticFunction.moebius 1 = 1 := ArithmeticFunction.moebius_apply_one
  have h2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  simp [h1, h2]

/-- At $n = 3$, $M(3) = -1$. -/
@[category test, AMS 11]
theorem mertensFunction_three : mertensFunction 3 = -1 := by
  rw [mertensFunction, show Finset.Icc 1 3 = {1, 2, 3} by decide]
  have h1 : ArithmeticFunction.moebius 1 = 1 := ArithmeticFunction.moebius_apply_one
  have h2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have h3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_three
  simp [h1, h2, h3]

/-- Step recurrence $M(n + 1) = M(n) + \mu(n + 1)$. -/
@[category API, AMS 11]
theorem mertensFunction_succ (n : ℕ) :
    mertensFunction (n + 1) = mertensFunction n + ArithmeticFunction.moebius (n + 1) := by
  unfold mertensFunction
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- At $n = 4$, $\mu(4) = 0$ since $4 = 2^2$ is not squarefree, giving $M(4) = M(3) = -1$. -/
@[category test, AMS 11]
theorem mertensFunction_four : mertensFunction 4 = -1 := by
  have h4 : ArithmeticFunction.moebius 4 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  rw [show (4 : ℕ) = 3 + 1 from rfl, mertensFunction_succ, mertensFunction_three, h4, add_zero]

/--
**Mertens' Conjecture** [Me1897], disproved by Odlyzko and te Riele [OtR85]: it is false that
$|M(n)| < \sqrt{n}$ holds for every integer $n \ge 2$.
-/
@[category research solved, AMS 11]
theorem mertens_conjecture :
    ¬ ∀ n : ℕ, 2 ≤ n → |(mertensFunction n : ℝ)| < Real.sqrt (n : ℝ) := by
  sorry

/--
**Odlyzko–te Riele Upper Limsup Bound** [OtR85]: $\limsup_{n \to \infty} M(n) / \sqrt{n} > 1.06$,
so there exists $c > 1.06$ such that $M(n) > c \sqrt{n}$ for infinitely many $n$.
-/
@[category research solved, AMS 11]
theorem mertens_conjecture.variants.odlyzko_te_riele_upper :
    ∃ c : ℝ, 1.06 < c ∧
      ∃ᶠ n : ℕ in atTop, c * Real.sqrt (n : ℝ) < (mertensFunction n : ℝ) := by
  sorry

/--
**Odlyzko–te Riele Lower Liminf Bound** [OtR85]:
$\liminf_{n \to \infty} M(n) / \sqrt{n} < -1.009$, so there exists $c < -1.009$ such that
$M(n) < c \sqrt{n}$ for infinitely many $n$.
-/
@[category research solved, AMS 11]
theorem mertens_conjecture.variants.odlyzko_te_riele_lower :
    ∃ c : ℝ, c < -1.009 ∧
      ∃ᶠ n : ℕ in atTop, (mertensFunction n : ℝ) < c * Real.sqrt (n : ℝ) := by
  sorry

/--
**Stieltjes's Boundedness Hypothesis**: Is $M(n) = O(n^{1/2})$ as $n \to \infty$? Stieltjes
claimed in 1885 that $M(n) / \sqrt{n}$ is bounded without publishing a proof, whereas Gonek's
heuristic predicts growth of order $(\log \log \log n)^{5/4}$ and hence unboundedness.
-/
@[category research open, question, AMS 11]
theorem stieltjes_mertens_bounded :
    (fun n : ℕ ↦ (mertensFunction n : ℝ)) =O[atTop] (fun n : ℕ ↦ Real.sqrt (n : ℝ)) := by
  sorry

end MertensConjecture
