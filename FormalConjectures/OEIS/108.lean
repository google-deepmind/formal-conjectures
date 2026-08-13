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

<<<<<<< HEAD
<<<<<<< HEAD
import FormalConjecturesUtil

/-!
# Fractional parts of sums of reciprocals of Catalan numbers $C(n)$

Catalan numbers $C(n) = \frac{1}{n+1}\binom{2n}{n}$.

The sum $\sum_{i=j}^k \frac{1}{a(i)}$ of reciprocals of Catalan numbers.

*References:*
- [A000108](https://oeis.org/A000108)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
=======
import FormalConjectures.Util.ProblemImports
=======
import FormalConjecturesUtil
>>>>>>> 1f708f7d (Fix imports to FormalConjecturesUtil)

/-!
# Catalan numbers

Catalan numbers: $C(n) = \binom{2n}{n}/(n+1)$.

*References:*
- [A000108](https://oeis.org/A000108)
>>>>>>> abbc48a2 (Process the next 25 files.)
-/

namespace OeisA108

<<<<<<< HEAD
<<<<<<< HEAD

open Nat Real Finset

/--
Catalan numbers $C(n) = \frac{1}{n+1}\binom{2n}{n}$.
-/
def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) / (n + 1)

def aRat (n : ℕ) : ℚ := (a n : ℚ)⁻¹

/-- The sum $\sum_{i=j}^k \frac{1}{a(i)}$ of reciprocals of Catalan numbers. -/
def catalanReciprocalSum (j k : ℕ) : ℚ :=
  (Finset.Icc j k).sum aRat

/-- The index condition on $(j, k)$ from the conjecture: $0 < \min\{2,k\} \le j \le k$.
Since j and k are natural numbers, $0 < \min\{2,k\}$ is equivalent to $1 \le k$. -/
def IndexCond (j k : ℕ) : Prop :=
=======
open Nat Real Finset
=======
open Nat Real Finset Polynomial
>>>>>>> 81b10bb2 (Process the next 47 files.)

/-- The primary defining sequence `a`.
Catalan numbers: $C(n) = \binom{2n}{n}/(n+1)$. -/
def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) / (n + 1)

/-- Reciprocal of the n-th Catalan number as a rational number. -/
def aRat (n : ℕ) : ℚ := (a n : ℚ)⁻¹

/-- The sum $\sum_{i=j}^k \frac{1}{a(i)}$ of reciprocals of Catalan numbers. -/
def catalanReciprocalSum (j k : ℕ) : ℚ :=
  (Finset.Icc j k).sum aRat

/-- The index condition on $(j, k)$ from the conjecture: $0 < \min\{2,k\} \le j \le k$.
<<<<<<< HEAD
Since j and k are natural numbers, $0 < \min\{2,k\}$ is equivalent to $1 \le k$. -/
def oeis_108_index_cond (j k : ℕ) : Prop :=
>>>>>>> abbc48a2 (Process the next 25 files.)
=======
Since $j$ and $k$ are natural numbers, $0 < \min\{2,k\}$ is equivalent to $1 \le k$. -/
def Oeis108IndexCond (j k : ℕ) : Prop :=
>>>>>>> bda2dd95 (Update titles and follow style naming.)
  1 ≤ k ∧ min 2 k ≤ j ∧ j ≤ k

open Int (fract)

<<<<<<< HEAD
/-- The fractional part of a rational number. -/
def fracPart (q : ℚ) : ℚ := fract q


@[category test, AMS 11]
lemma a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
lemma a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
lemma a_2 : a 2 = 2 := by rfl

@[category test, AMS 11]
lemma a_3 : a 3 = 5 := by rfl

@[category test, AMS 11]
lemma a_4 : a 4 = 14 := by rfl


/--
Conjecture: All the rational numbers $\sum_{i=j}^k \frac{1}{a(i)}$ with
$0 < \min\{2,k\} \le j \le k$ have pairwise distinct fractional parts.

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/108.wip.lean#L255"]
theorem catalanReciprocalSum_fracPart_inj : ∀ ⦃j₁ k₁ j₂ k₂ : ℕ⦄,
    IndexCond j₁ k₁ → IndexCond j₂ k₂ →
    (j₁, k₁) ≠ (j₂, k₂) →
    fracPart (catalanReciprocalSum j₁ k₁) ≠ fracPart (catalanReciprocalSum j₂ k₂) := by
    sorry
=======
/-- The fractional part of a rational number, viewed as a real number. Must be noncomputable
due to dependence on the real floor function. -/
noncomputable def fracPart (q : ℚ) : ℝ := fract (q : ℝ)

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 14 := by decide

/--
A000108 Conjecture: All the rational numbers $\sum_{i=j}^k \frac{1}{a(i)}$ with
$0 < \min\{2,k\} \le j \le k$ have pairwise distinct fractional parts. - _Zhi-Wei Sun_, Sep 24 2015
-/
@[category research open, AMS 11]
theorem conjecture1 :
  ∀ ⦃j₁ k₁ j₂ k₂ : ℕ⦄,
     Oeis108IndexCond j₁ k₁ →
     Oeis108IndexCond j₂ k₂ →
     (j₁, k₁) ≠ (j₂, k₂) →
     fracPart (catalanReciprocalSum j₁ k₁) ≠ fracPart (catalanReciprocalSum j₂ k₂)
  := by sorry
>>>>>>> abbc48a2 (Process the next 25 files.)

/--
The polynomial $\sum_{k=0}^n a(k) x^k$, where $a(k)$ are the Catalan numbers.
The coefficients $a(k) \in \mathbb{N}$ are coerced to $\mathbb{Q}$.
-/
noncomputable def catalanPolynomial (n : ℕ) : ℚ[X] :=
  (Finset.range (n + 1)).sum (fun k => C (a k : ℚ) * X^k)

/--
OEIS A000108 Conjecture: For any positive integer n, the polynomial
$\sum_{k=0}^n a(k)x^k$ is irreducible over the field of rational numbers.
-/
@[category research open, AMS 11 12]
theorem conjecture2 (n : ℕ) (h : n > 0) :
    Irreducible (catalanPolynomial n) := by
  sorry

end OeisA108
