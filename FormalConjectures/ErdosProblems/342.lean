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
# Erdős Problem 342

*Reference:* [erdosproblems.com/342](https://www.erdosproblems.com/342)

Questions about properties of the Ulam sequence (1, 2, 3, 4, 6, 8, 11, 13, ...): whether
infinitely many pairs $a$, $a + 2$ occur, whether the differences are eventually periodic, and
whether the upper density of the sequence is zero.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).
-/

open Filter

namespace Erdos342

open scoped Classical

/-- Count the number of representations of $m$ as $a_i + a_j$ with $i < j < n$. -/
def ulamRepCount (a : ℕ → ℕ) (n m : ℕ) : ℕ :=
  Finset.card (Finset.filter
    (fun p : Fin n × Fin n => p.1.val < p.2.val ∧ a p.1.val + a p.2.val = m)
    Finset.univ)

/-- The Ulam sequence: $a(0) = 1$, $a(1) = 2$, and for each $n \geq 2$, $a(n)$ is the
least integer greater than $a(n-1)$ that has exactly one representation as
$a_i + a_j$ with $i < j < n$. (OEIS A002858) -/
def IsUlamSequence (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ a 1 = 2 ∧
  ∀ n, 2 ≤ n →
    a (n - 1) < a n ∧
    ulamRepCount a n (a n) = 1 ∧
    ∀ m, a (n - 1) < m → m < a n → ulamRepCount a n m ≠ 1

/-- The upper density of $A \subseteq \mathbb{N}$:
$d^*(A) = \limsup_{N \to \infty} |A \cap \{0, 1, \ldots, N-1\}| / N$ -/
noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  limsup (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    atTop

/--
Erdős Problem 342, Part 1 [ErGr80, p.53]:

A problem of Ulam. With $a_1 = 1$ and $a_2 = 2$, let $a_{n+1}$ for $n \geq 2$ be the least
integer $> a_n$ which can be expressed uniquely as $a_i + a_j$ for $i < j \leq n$.
The sequence is $1, 2, 3, 4, 6, 8, 11, 13, 16, 18, 26, 28, \ldots$

Do infinitely many pairs $a$, $a + 2$ occur in the sequence?
-/
@[category research open, AMS 5 11]
theorem erdos_342 : answer(sorry) ↔
    ∀ a : ℕ → ℕ, IsUlamSequence a →
      Set.Infinite {n : ℕ | ∃ m, a m = a n + 2} := by
  sorry

/--
Erdős Problem 342, Part 2 [ErGr80, p.53]:

Does the Ulam sequence eventually have periodic differences?
That is, do there exist $N$ and $p > 0$ such that
$a(n + p + 1) - a(n + p) = a(n + 1) - a(n)$ for all $n \geq N$?
-/
@[category research open, AMS 5 11]
theorem erdos_342.variants.periodic : answer(sorry) ↔
    ∀ a : ℕ → ℕ, IsUlamSequence a →
      ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n →
        a (n + p + 1) - a (n + p) = a (n + 1) - a n := by
  sorry

/--
Erdős Problem 342, Part 3 [ErGr80, p.53]:

Is the (upper) density of the Ulam sequence equal to $0$?
-/
@[category research open, AMS 5 11]
theorem erdos_342.variants.density : answer(sorry) ↔
    ∀ a : ℕ → ℕ, IsUlamSequence a →
      upperDensity (Set.range a) = 0 := by
  sorry

end Erdos342
