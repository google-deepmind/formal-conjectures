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
# Tokareva's conjectures on bent functions

*References:*
- [arxiv/2610.32239](https://arxiv.org/abs/2610.32239)
  **A counterexample to Tokareva's conjecture on sums of two bent functions**
  by *Yansong Feng, Hao Jiang, Guancheng Li, Tianyi Li, Lili Tang*, where these are
  Conjecture 1.1 and Conjecture 4.5.
- [To11] Tokareva, N., *On the number of bent functions from iterative constructions: lower
  bounds and hypotheses*, Adv. Math. Commun. 5 (2011), 609--621.
  [doi:10.3934/amc.2011.5.609](https://doi.org/10.3934/amc.2011.5.609)
- [To16] Tokareva, N. N., *On the set of derivatives of a Boolean bent function*, Prikl. Diskr.
  Mat. Prilozh. 9 (2016), 35 (in Russian).
  [doi:10.17223/2226308X/9/14](https://doi.org/10.17223/2226308X/9/14)
- [KKV26] Kepes, M. R., Kercsó-Molnár, A., Viczián, A., *A family of symmetric counterexamples to
  the bent sum decomposition conjecture*, [arXiv:2611.06744](https://arxiv.org/abs/2611.06744)
  (2026).
- [Po23] Potapov, V. N., *Existence of balanced functions that are not derivative of bent
  functions*, [arXiv:2309.04244](https://arxiv.org/abs/2309.04244) (2023).
- [Go26] Goldstick, D. I., *Lean 4 Formalization of Counterexamples to Tokareva's Conjectures on
  Bent Functions* (2026). [doi:10.5281/zenodo.24615636](https://doi.org/10.5281/zenodo.24615636),
  [PALOMAR-2026-11-28-000015](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-28-000015)

A Boolean function on $\mathbb{F}_2^n$ is a map `(Fin n → ZMod 2) → ZMod 2`. Its Walsh–Hadamard
transform is $W_f(\omega) = \sum_x (-1)^{f(x) + \langle x, \omega \rangle}$, and $f$ is *bent*
when $|W_f(\omega)| = 2^{n/2}$ for every $\omega$. Its algebraic degree is at most $d$ when it is
the evaluation of a polynomial over $\mathbb{F}_2$ of total degree at most $d$, which is
equivalent to the degree of its algebraic normal form.

Both conjectures are false [arxiv/2610.32239]. The paper's counterexamples, with the family in
every even dimension $n \ge 8$, are proved in Lean 4 in [Go26].
-/

@[expose] public section

open MvPolynomial

namespace Arxiv.«2610.32239»

/-- Boolean functions on $\mathbb{F}_2^n$. -/
abbrev BoolFun (n : ℕ) := (Fin n → ZMod 2) → ZMod 2

/-- The sign $(-1)^a$ of $a \in \mathbb{F}_2$, as an integer. -/
def sgn (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

/-- The standard inner product $\langle x, \omega \rangle = \sum_i x_i \omega_i$ on
$\mathbb{F}_2^n$. -/
def dot {n : ℕ} (x ω : Fin n → ZMod 2) : ZMod 2 := ∑ i, x i * ω i

/-- The Walsh–Hadamard transform $W_f(\omega) = \sum_x (-1)^{f(x) + \langle x, \omega \rangle}$. -/
def walsh {n : ℕ} (f : BoolFun n) (ω : Fin n → ZMod 2) : ℤ := ∑ x, sgn (f x + dot x ω)

/-- $f$ is bent: every Walsh coefficient has absolute value $2^{n/2}$. -/
def IsBent {n : ℕ} (f : BoolFun n) : Prop := ∀ ω, |walsh f ω| = 2 ^ (n / 2)

/-- $f$ has algebraic degree at most $d$: it is the evaluation of a polynomial over
$\mathbb{F}_2$ of total degree at most $d$. -/
def HasDegreeLE {n : ℕ} (f : BoolFun n) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) (ZMod 2), p.totalDegree ≤ d ∧ ∀ x, eval x p = f x

/-- $f$ is a sum of two bent functions. -/
def IsBentSum {n : ℕ} (f : BoolFun n) : Prop :=
  ∃ g h : BoolFun n, IsBent g ∧ IsBent h ∧ f = g + h

/-- $f$ is balanced: it takes the value $1$ on exactly half of $\mathbb{F}_2^n$. -/
def IsBalanced {n : ℕ} (f : BoolFun n) : Prop :=
  2 * (Finset.univ.filter fun x => f x = 1).card = 2 ^ n

/-- $a$ is a period of $f$: $f(x + a) = f(x)$ for every $x$. -/
def IsPeriod {n : ℕ} (f : BoolFun n) (a : Fin n → ZMod 2) : Prop := ∀ x, f (x + a) = f x

/-- $f$ is a derivative $g(x) + g(x + a)$ of a bent function $g$, in some direction $a$. -/
def IsBentDerivative {n : ℕ} (f : BoolFun n) : Prop :=
  ∃ g : BoolFun n, IsBent g ∧ ∃ a : Fin n → ZMod 2, ∀ x, f x = g x + g (x + a)

/-- The counterexample $x_1x_2(x_3x_4 + x_5x_6 + x_7x_8)$ on $\mathbb{F}_2^8$, with the variables
indexed from `0`. -/
def f8 : BoolFun 8 := fun x => x 0 * x 1 * (x 2 * x 3 + x 4 * x 5 + x 6 * x 7)

/-- The counterexample $x_2 + f_8(x_3, \dots, x_{10})$ on $\mathbb{F}_2^{10}$, with the variables
indexed from `0`. -/
def h10 : BoolFun 10 := fun x => x 1 + f8 (Fin.tail (Fin.tail x))

/--
**Conjecture 1.1 (Tokareva).** For even $n$, every Boolean function on $\mathbb{F}_2^n$ of
algebraic degree at most $n/2$ is a sum of two bent functions.

This is false: $x_1x_2(x_3x_4 + x_5x_6 + x_7x_8)$ on $\mathbb{F}_2^8$ has degree $4$ but is not a
sum of two bent functions [arxiv/2610.32239, Theorem 4.2].
-/
@[category research solved, question, AMS 6 94, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-28-000015"]
theorem tokareva_conjecture :
    ¬ ∀ n : ℕ, Even n → ∀ f : BoolFun n, HasDegreeLE f (n / 2) → IsBentSum f := by
  sorry

/--
The counterexample of [arxiv/2610.32239]: $x_1x_2(x_3x_4 + x_5x_6 + x_7x_8)$ is not a sum of two
bent functions on $\mathbb{F}_2^8$.
-/
@[category research solved, AMS 6 94, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-28-000015"]
theorem tokareva_conjecture.variants.f8 : ¬ IsBentSum f8 := by
  sorry

/--
**Theorem 4.2 of [arxiv/2610.32239].** The conjecture fails in every even dimension $n \ge 8$:
$x_1 \cdots x_{m-2} \, q_3(x_{m-1}, \dots, x_{m+4})$ with $n = 2m$ and
$q_3 = z_1z_2 + z_3z_4 + z_5z_6$ has degree at most $n/2$ and is not a sum of two bent functions.
Kepes, Kercsó-Molnár and Viczián [KKV26] give another family for $n = 2^k \ge 8$. The conjecture
holds for $n \le 6$ [arxiv/2610.32239].
-/
@[category research solved, AMS 6 94, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-28-000015"]
theorem tokareva_conjecture.variants.even_ge_eight (n : ℕ) (hn : Even n) (h8 : 8 ≤ n) :
    ∃ f : BoolFun n, HasDegreeLE f (n / 2) ∧ ¬ IsBentSum f := by
  sorry

/--
**Conjecture 4.5 (Tokareva).** For even $n$, every balanced Boolean function on
$\mathbb{F}_2^n$ of algebraic degree at most $n/2 - 1$ with a nonzero period is a derivative
$g(x) + g(x + a)$ of a bent function $g$.

The three hypotheses are necessary: every derivative of a bent function in a nonzero direction
has them. Potapov [Po23] showed that the conjecture fails for large $n$ by a counting argument,
and Feng, Jiang, Li, Li and Tang give explicit counterexamples for every even $n \ge 10$
[arxiv/2610.32239, Theorem 4.7]: $x_2 + f_8(x_3, \dots, x_{10})$ on $\mathbb{F}_2^{10}$ is
balanced, has degree $4$ and the period $e_1$, but is not a derivative of a bent function. Some
sources state the conjecture without the period hypothesis; this counterexample refutes that
version too.
-/
@[category research solved, question, AMS 6 94, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-28-000015"]
theorem tokareva_derivative_conjecture :
    ¬ ∀ n : ℕ, Even n → ∀ f : BoolFun n, IsBalanced f → HasDegreeLE f (n / 2 - 1) →
      (∃ a, a ≠ 0 ∧ IsPeriod f a) → IsBentDerivative f := by
  sorry

/-- The counterexample $f_8$ satisfies the degree hypothesis of the conjecture for $n = 8$. -/
@[category test, AMS 6 94]
theorem f8_hasDegreeLE : HasDegreeLE f8 (8 / 2) := by
  refine ⟨X 0 * X 1 * (X 2 * X 3 + X 4 * X 5 + X 6 * X 7), ?_, fun x => by simp [f8]⟩
  have hX : ∀ i j : Fin 8, (X i * X j : MvPolynomial (Fin 8) (ZMod 2)).totalDegree ≤ 2 :=
    fun i j => (totalDegree_mul _ _).trans (by rw [totalDegree_X, totalDegree_X])
  calc _ ≤ (X 0 * X 1 : MvPolynomial (Fin 8) (ZMod 2)).totalDegree +
          (X 2 * X 3 + X 4 * X 5 + X 6 * X 7 : MvPolynomial (Fin 8) (ZMod 2)).totalDegree :=
        totalDegree_mul _ _
    _ ≤ 2 + 2 := add_le_add (hX 0 1) ((totalDegree_add _ _).trans
        (max_le ((totalDegree_add _ _).trans (max_le (hX 2 3) (hX 4 5))) (hX 6 7)))

/-- The derivative counterexample has the nonzero period $e_1$. -/
@[category test, AMS 6 94]
theorem h10_isPeriod : IsPeriod h10 (Pi.single 0 1) := by
  intro x
  have : Fin.tail (Fin.tail (x + Pi.single 0 1)) = Fin.tail (Fin.tail x) := by
    funext i
    simp [Fin.tail, Fin.succ_ne_zero]
  simp [h10, this]

end Arxiv.«2610.32239»
