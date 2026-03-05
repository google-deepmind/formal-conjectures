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
# Erdős Problem 675

*Reference:* [erdosproblems.com/675](https://www.erdosproblems.com/675)

We say that $A \subset \mathbb{N}$ has the translation property if, for every $n$, there exists
some integer $t_n \geq 1$ such that, for all $1 \leq a \leq n$,
$a \in A$ if and only if $a + t_n \in A$.

Three questions:
1. Does the set of sums of two squares have the translation property?
2. If we partition all primes into $P \sqcup Q$, such that each set contains $\gg x/\log x$
   many primes $\leq x$ for all large $x$, then can the set of integers only divisible
   by primes from $P$ have the translation property?
3. If $A$ is the set of squarefree numbers then how fast does the minimal such $t_n$
   grow? Is it true that $t_n > \exp(n^c)$ for some constant $c > 0$?

Elementary sieve theory implies the set of squarefree numbers has the
translation property.

[Er79] Erdős, P., _Some unconventional problems in number theory_ (1979).
-/

open Real Classical

namespace Erdos675

/-- A set $A \subseteq \mathbb{N}$ has the translation property if for every $n$, there exists
    $t \geq 1$ such that for all $1 \leq a \leq n$, $a \in A \leftrightarrow a + t \in A$. -/
def HasTranslationProperty (A : Set ℕ) : Prop :=
  ∀ n : ℕ, ∃ t : ℕ, t ≥ 1 ∧ ∀ a : ℕ, 1 ≤ a → a ≤ n → (a ∈ A ↔ a + t ∈ A)

/-- A natural number is a sum of two squares. -/
def IsSumOfTwoSquares (n : ℕ) : Prop :=
  ∃ a b : ℕ, n = a ^ 2 + b ^ 2

/-- The set of natural numbers that are sums of two squares. -/
def sumOfTwoSquaresSet : Set ℕ := {n | IsSumOfTwoSquares n}

/-- The set of squarefree natural numbers. -/
def squarefreeSet : Set ℕ := {n | Squarefree n}

/-- The minimal translation witness for a set $A$ at level $n$:
    the smallest $t \geq 1$ such that for all $1 \leq a \leq n$,
    $a \in A \leftrightarrow a + t \in A$. -/
noncomputable def minimalTranslation (A : Set ℕ) (n : ℕ) : ℕ :=
  sInf {t : ℕ | t ≥ 1 ∧ ∀ a : ℕ, 1 ≤ a → a ≤ n → (a ∈ A ↔ a + t ∈ A)}

/-- Given a set of primes $P$, the set of natural numbers $\geq 1$ all of whose
    prime factors lie in $P$. -/
def smoothNumbers (P : Set ℕ) : Set ℕ :=
  {n | n ≥ 1 ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∈ P}

/--
Erdős Problem 675 [Er79]:

Does the set of sums of two squares have the translation property?
-/
@[category research open, AMS 11]
theorem erdos_675 :
    answer(sorry) ↔ HasTranslationProperty sumOfTwoSquaresSet := by
  sorry

/--
Erdős Problem 675, Part 2 [Er79]:

If we partition all primes into $P \sqcup Q$, such that each set contains $\gg x/\log x$
many primes $\leq x$ for all large $x$, then can the set of integers only divisible
by primes from $P$ have the translation property?
-/
@[category research open, AMS 11]
theorem erdos_675.variants.smoothNumbers :
    answer(sorry) ↔
    ∃ (P : Set ℕ),
    (∃ c₁ : ℝ, c₁ > 0 ∧ ∃ N₁ : ℕ, ∀ x : ℕ, x ≥ N₁ →
      c₁ * (x : ℝ) / Real.log (x : ℝ) ≤
        (((Finset.range (x + 1)).filter (fun q => Nat.Prime q ∧ q ∈ P)).card : ℝ)) ∧
    (∃ c₂ : ℝ, c₂ > 0 ∧ ∃ N₂ : ℕ, ∀ x : ℕ, x ≥ N₂ →
      c₂ * (x : ℝ) / Real.log (x : ℝ) ≤
        (((Finset.range (x + 1)).filter (fun q => Nat.Prime q ∧ q ∉ P)).card : ℝ)) ∧
    HasTranslationProperty (smoothNumbers P) := by
  sorry

/--
Erdős Problem 675, Part 3 [Er79]:

If $A$ is the set of squarefree numbers, then the minimal translation $t_n$
grows faster than $\exp(n^c)$ for some constant $c > 0$. That is, there exists
$c > 0$ and $N_0$ such that for all $n \geq N_0$, $t_n > \exp(n^c)$.
-/
@[category research open, AMS 11]
theorem erdos_675.variants.squarefreeGrowth :
    answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (minimalTranslation squarefreeSet n : ℝ) > Real.exp ((n : ℝ) ^ c) := by
  sorry

end Erdos675
