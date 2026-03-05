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

*Reference:* [erdosproblems.com/169](https://www.erdosproblems.com/169)
-/

open Finset BigOperators Real

namespace Erdos169

/-- A finset of natural numbers is $k$-AP-free if it contains no arithmetic
progression of length $k$ with positive common difference. -/
def IsAPFree (k : ℕ) (A : Finset ℕ) : Prop :=
  ¬∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ A

/-- The van der Waerden property: every $2$-coloring of $\{0, \ldots, N-1\}$ contains
a monochromatic $k$-term arithmetic progression. -/
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

end Erdos169
