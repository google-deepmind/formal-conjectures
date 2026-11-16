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
public import FormalConjectures.Wikipedia.ArtinPrimitiveRootsConjecture

/-!
# Ben Green's Open Problem 93

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.93)
- [BrVa19] Breuillard, E. and Varjú, P. P., *Irreducibility of random polynomials of large
  degree*. Acta Math. 223 (2019), 195--249. [arXiv:1810.13360](https://arxiv.org/abs/1810.13360)
- [BSKK23] Bary-Soroker, L., Koukoulopoulos, D. and Kozma, G., *Irreducibility of random
  polynomials: general measures*. Invent. Math. 233 (2023), 1041--1120.
  [arXiv:2007.14567](https://arxiv.org/abs/2007.14567)
- [Ko99] Konyagin, S. V., *On the number of irreducible polynomials with 0,1 coefficients*.
  Acta Arith. 88 (1999), 333--350.
-/

@[expose] public section

open Polynomial Filter
open scoped Topology

namespace Green93

/--
`monicPoly a` is the monic polynomial $X^n + a_{n-1} X^{n-1} + \cdots + a_1 X + a_0 \in
\mathbb{Z}[X]$ with lower coefficients `a j`, $0 \le j < n$.
-/
noncomputable def monicPoly {n : ℕ} (a : Fin n → ℕ) : ℤ[X] :=
  X ^ n + ∑ j : Fin n, C (a j : ℤ) * X ^ (j : ℕ)

open scoped Classical in
/--
`irreducibleProb M n` is the probability that the random monic polynomial
$$X^n + a_{n-1} X^{n-1} + \cdots + a_1 X + a_0$$
of degree $n$ is irreducible, where $a_0, \dots, a_{n-1}$ are chosen uniformly from
$\{0, 1, \dots, M\}$, conditioned on the constant term $a_0$ being nonzero. It is a quotient of
two finite counts over the coefficient vectors `a : Fin n → Fin (M + 1)`.

The polynomial is monic, so by Gauss's lemma it is irreducible in $\mathbb{Z}[X]$ if and only if it
is irreducible over $\mathbb{Q}$ (for $n \ge 1$). For $M = 1$ the constant term is $1$ and
`irreducibleProb 1 n` is the probability $p_n$ of [Gr24, Problem 93] that
$1 + a_1 x + \cdots + a_{n-1} x^{n-1} + x^n$ is irreducible for i.i.d. uniform
$a_i \in \{0, 1\}$.
-/
noncomputable def irreducibleProb (M n : ℕ) : ℝ :=
  ((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
      (monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
        Irreducible (monicPoly fun j ↦ (a j : ℕ))).card : ℝ) /
    (Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
      (monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).card

/-- `irreducibleProb M n` is nonnegative. -/
@[category API, AMS 11 12 60]
theorem irreducibleProb_nonneg (M n : ℕ) : 0 ≤ irreducibleProb M n := by
  unfold irreducibleProb
  positivity

/-- `irreducibleProb M n` is at most $1$, since it is a quotient of a count by a larger count. -/
@[category API, AMS 11 12 60]
theorem irreducibleProb_le_one (M n : ℕ) : irreducibleProb M n ≤ 1 := by
  unfold irreducibleProb
  apply div_le_one_of_le₀
  · refine Nat.cast_le.mpr (Finset.card_le_card ?_)
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha.1
  · positivity

/--
Is a random polynomial with coefficients in $\{0,1\}$ and nonzero constant term almost surely
irreducible?

More precisely, writing $p_n$ for the probability that
$1 + a_1 x + \cdots + a_{n-1} x^{n-1} + x^n$ is irreducible, where the $a_i$ are independent and
take the values $0$ and $1$ with equal probability, does $p_n \to 1$?

The probability $p_n$ is `irreducibleProb 1 n`. The conjecture is due to Odlyzko and Poonen
[BrVa19, Section 1].
-/
@[category research open, question, AMS 11 12 60]
theorem green_93 : Tendsto (fun n : ℕ ↦ irreducibleProb 1 n) atTop (𝓝 1) := by
  sorry

/--
Konyagin [Ko99] proved that $p_n \ge c / \log n$ for an absolute constant $c > 0$, as stated in
[BrVa19, Section 1]. We state it for all large $n$. It is superseded by
`green_93.variants.bskk_small`.
-/
@[category research solved, AMS 11 12 60]
theorem green_93.variants.konyagin :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c / Real.log (n : ℝ) ≤ irreducibleProb 1 n := by
  sorry

/--
Bary-Soroker, Koukoulopoulos and Kozma [BSKK23, Theorem 1(b)] proved that a random monic
polynomial of degree $n$ whose coefficients are uniform on $N$ consecutive integers in $[-H, H]$
with $2 \le N \le 34$, and with nonzero constant term, is irreducible with probability at least
$\delta$. Here $\delta > 0$ is an absolute constant, and $n$ must be at least an absolute constant
and at least $(\log H)^3$. We state it for the integers $\{0, 1, \dots, M\}$ with
$1 \le M \le 33$, so $N = M + 1$ and $H = M$. The condition on $(\log H)^3$ is absorbed into
$n_0$, because $M$ is bounded. The case $M = 1$ gives $p_n \ge \delta$ for large $n$ for the
polynomial of `green_93`.
-/
@[category research solved, AMS 11 12 60]
theorem green_93.variants.bskk_small :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ M n : ℕ, 1 ≤ M → M ≤ 33 → n₀ ≤ n →
      δ ≤ irreducibleProb M n := by
  sorry

/--
Bary-Soroker, Koukoulopoulos and Kozma [BSKK23, Theorem 1(a)] proved that a random monic
polynomial of degree $n$ whose coefficients are uniform on $N \ge 35$ consecutive integers in
$[-H, H]$, with nonzero constant term, is irreducible with probability at least $1 - n^{-c}$.
Here $c > 0$ is an absolute constant, and $n$ must be at least an absolute constant and at least
$(\log H)^3$. We state it for the integers
$\{0, 1, \dots, M\}$ with $M \ge 34$, so $N = M + 1 \ge 35$ and $H = M$. In particular
`irreducibleProb M n` $\to 1$ for each such $M$, which is the analogue of `green_93` for
coefficients in $\{0, \dots, M\}$.
-/
@[category research solved, AMS 11 12 60]
theorem green_93.variants.bskk_large :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ M n : ℕ, 34 ≤ M → n₀ ≤ n → (Real.log (M : ℝ)) ^ 3 ≤ n →
      1 - (n : ℝ) ^ (-c) ≤ irreducibleProb M n := by
  sorry

/--
The Riemann hypothesis holds for the Dedekind zeta function of every number field $\mathbb{Q}(a)$
generated by a root $a$ of a nonzero polynomial with all coefficients in $\{0, 1\}$.

Here a number field `K` is generated by `a` if `IntermediateField.adjoin ℚ {a} = ⊤`. The Riemann
hypothesis for `K` is `ArtinPrimitiveRootsConjecture.DedekindZetaRH K`, which uses the analytic
continuation of the Dedekind zeta function and not Mathlib's `NumberField.dedekindZeta`.
-/
def ZeroOneRootFieldsRH : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (f : ℤ[X]) (a : K),
    f ≠ 0 → (∀ i, f.coeff i = 0 ∨ f.coeff i = 1) → aeval a f = 0 →
      IntermediateField.adjoin ℚ {a} = ⊤ → ArtinPrimitiveRootsConjecture.DedekindZetaRH K

/--
**Breuillard and Varjú.** Assume the Riemann hypothesis for the Dedekind zeta functions of all
number fields $\mathbb{Q}(a)$ with $a$ a root of a polynomial with coefficients in $\{0, 1\}$
(`ZeroOneRootFieldsRH`). Then $p_n \to 1$ [BrVa19, Theorem 1].
-/
@[category research solved, AMS 11 12 60]
theorem green_93.variants.breuillard_varju :
    ZeroOneRootFieldsRH → Tendsto (fun n : ℕ ↦ irreducibleProb 1 n) atTop (𝓝 1) := by
  sorry

end Green93
