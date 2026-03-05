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
# Erdős Problem 983

*Reference:* [erdosproblems.com/983](https://www.erdosproblems.com/983)

Let $n \geq 2$ and $\pi(n) < k \leq n$. Let $f(k,n)$ be the smallest integer $r$ such that
in any $A \subseteq \{1,\ldots,n\}$ of size $|A| = k$ there exist primes $p_1,\ldots,p_r$ such
that more than $r$ elements $a \in A$ are only divisible by primes from $\{p_1,\ldots,p_r\}$.

[Er70b] Erdős, P. and Straus, E.G.
-/

open Classical

namespace Erdos983

/-- The prime counting function $\pi(n)$: the number of primes $\leq n$. -/
def primeCounting (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter Nat.Prime).card

/-- A natural number $a$ is smooth with respect to a set of primes $P$ if every
prime factor of $a$ belongs to $P$. -/
def IsSmoothWrt (a : ℕ) (P : Finset ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ a → p ∈ P

/-- $f(k,n)$ is the smallest integer $r$ such that in any $A \subseteq \{1,\ldots,n\}$ of size
$|A| = k$, there exist $r$ primes $p_1,\ldots,p_r$ such that more than $r$ elements of $A$ are
only divisible by primes from $\{p_1,\ldots,p_r\}$. -/
noncomputable def smoothCoveringNumber (k n : ℕ) : ℕ :=
  sInf {r : ℕ | ∀ A : Finset ℕ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) → A.card = k →
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) ∧ P.card = r ∧
      ∃ B : Finset ℕ, B ⊆ A ∧ B.card > r ∧ ∀ b ∈ B, IsSmoothWrt b P}

/--
Erdős Problem 983 [Er70b]:

Is it true that $2\pi(\sqrt{n}) - f(\pi(n)+1, n) \to \infty$ as $n \to \infty$?

Formulated as: for every $M$, there exists $N_0$ such that for all $n \geq N_0$,
$f(\pi(n)+1, n) + M \leq 2\pi(\lfloor\sqrt{n}\rfloor)$.
-/
@[category research open, AMS 5 11]
theorem erdos_983 :
    answer(sorry) ↔
    ∀ M : ℕ, ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      smoothCoveringNumber (primeCounting n + 1) n + M ≤ 2 * primeCounting (Nat.sqrt n) := by
  sorry

end Erdos983
