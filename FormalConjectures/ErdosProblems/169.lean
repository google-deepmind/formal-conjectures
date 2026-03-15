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
# Erdős Problem 169

Let $f(k)$ denote the supremum of $\sum_{n \in A} 1/n$ over all sets $A$ of positive
integers containing no $k$-term arithmetic progression. Is
$\lim_{k \to \infty} f(k) / \log W(k) = \infty$, where $W(k)$ is the $k$-th van der
Waerden number?

Berlekamp [Be68] proved $f(k) \geq (\log 2 / 2) k$. Gerver [Ge77] improved this to
$f(k) \geq (1 - o(1)) k \log k$. It is trivial that $f(k) / \log W(k) \geq 1/2$, but
improving this constant is open.

Gerver also proved that Problem 3 (if $\sum 1/n$ diverges then $A$ contains arbitrarily
long APs) is equivalent to $f(k)$ being finite for all $k$.

## References

- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
  number theory*. Monographies de L'Enseignement Mathematique (1980).
- [Be68] Berlekamp, E. R., *A construction for partitions which avoid long arithmetic
  progressions*. Canad. Math. Bull. (1968), 409-414.
- [Ge77] Gerver, J. L., *The sum of the reciprocals of a set of integers with no
  arithmetic progression of k terms*. Proc. Amer. Math. Soc. (1977), 211-214.
- [Wr84] Wróblewski, J., *A nonaveraging set of integers with a large sum of
  reciprocals*. Math. Comp. (1984), 261-262.
- [Wa25] Walker, A., *Integer sets of large harmonic sum which avoid long arithmetic
  progressions*. arXiv:2203.06045 (2025).

*Reference:* [erdosproblems.com/169](https://www.erdosproblems.com/169)
-/

open Finset BigOperators Real

namespace Erdos169

/-- A finset of natural numbers is $k$-AP-free if it contains no arithmetic
progression of length $k$ with positive common difference. -/
def IsAPFree (k : ℕ) (A : Finset ℕ) : Prop :=
  ¬∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ A

/-- The van der Waerden property: every $2$-coloring of $\{0, \ldots, N-1\}$ contains
a monochromatic $k$-term arithmetic progression. The coloring is defined on all of `ℕ`,
but only values in `{0, …, N-1}` matter since all AP terms satisfy `a + i * d < N`. -/
def VDWProperty (k N : ℕ) : Prop :=
  ∀ f : ℕ → Bool, ∃ a d : ℕ, 0 < d ∧ a + (k - 1) * d < N ∧
    ∀ i : ℕ, i < k → f (a + i * d) = f a

/-- Van der Waerden's theorem guarantees the existence of $W(k)$ for all $k$. -/
@[category graduate, AMS 5]
lemma vdw_exists (k : ℕ) : ∃ N, VDWProperty k N := by sorry

open Classical in
/-- The van der Waerden number $W(k)$: the smallest $N$ such that any $2$-coloring
of $\{0, \ldots, N-1\}$ contains a monochromatic $k$-term AP. -/
noncomputable def vanDerWaerdenNumber (k : ℕ) : ℕ :=
  Nat.find (vdw_exists k)

/--
Erdős Problem 169:
Let $k \geq 3$ and $f(k)$ be the supremum of $\sum_{n \in A} 1/n$ over all sets $A$ of
positive integers containing no $k$-term arithmetic progression.

Is $\lim_{k \to \infty} f(k) / \log W(k) = \infty$, where $W(k)$ is the van der Waerden
number?

This is formalized as: for every constant $C > 0$, for all sufficiently large $k$,
there exists a finite AP-free set $A$ of positive integers whose reciprocal sum
exceeds $C \cdot \log W(k)$.
-/
@[category research open, AMS 5 11]
theorem erdos_169 : answer(sorry) ↔
    ∀ C : ℝ, 0 < C → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ A : Finset ℕ, (∀ n ∈ A, 0 < n) ∧ IsAPFree k A ∧
        C * Real.log (↑(vanDerWaerdenNumber k) : ℝ) <
          ∑ n ∈ A, (1 : ℝ) / (↑n : ℝ) := by
  sorry

/--
Gerver's lower bound [Ge77]: $f(k) \geq (1 - o(1)) k \log k$.

Formalized as: for every $\varepsilon > 0$, for all sufficiently large $k$, there exists a
finite AP-free set of positive integers whose reciprocal sum exceeds $(1 - \varepsilon) k \log k$.
-/
@[category graduate, AMS 5 11]
theorem erdos_169_gerver_lower_bound :
    ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ A : Finset ℕ, (∀ n ∈ A, 0 < n) ∧ IsAPFree k A ∧
        (1 - ε) * (↑k : ℝ) * Real.log (↑k : ℝ) <
          ∑ n ∈ A, (1 : ℝ) / (↑n : ℝ) := by
  sorry

/--
Equivalence with Erdős Problem 3 (Gerver [Ge77]):
$f(k)$ is finite for all $k$ if and only if every set $A \subseteq \mathbb{N}^+$ with
$\sum_{n \in A} 1/n = \infty$ contains arbitrarily long arithmetic progressions.
-/
@[category graduate, AMS 5 11]
theorem erdos_169_equiv_problem3 :
    (∀ k : ℕ, ∃ B : ℝ, ∀ A : Finset ℕ, (∀ n ∈ A, 0 < n) → IsAPFree k A →
      ∑ n ∈ A, (1 : ℝ) / (↑n : ℝ) ≤ B) ↔
    (∀ A : Set ℕ, (∀ n ∈ A, 0 < n) →
      (¬ Summable fun a : A ↦ (1 : ℝ) / (↑(a : ℕ) : ℝ)) →
      ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ A) := by
  sorry

end Erdos169
