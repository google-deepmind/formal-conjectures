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
# Erdős Problem 31

*Reference:* [erdosproblems.com/31](https://www.erdosproblems.com/31)

Given any infinite set $A \subset \mathbb{N}$, there exists a set $B$ of natural density zero
such that $A + B$ contains all except finitely many natural numbers. Proved by Lorentz [Lo54].

[Lo54] Lorentz, G. G., _On a problem of additive number theory_. Proc. Amer. Math. Soc. 5 (1954), 838–840.
-/

open scoped Classical

namespace Erdos31

/-- The sumset $A + B$: the set of all $a + b$ with $a \in A$, $b \in B$. -/
def sumset (A B : Set ℕ) : Set ℕ := {n : ℕ | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

/-- A set $B \subseteq \mathbb{N}$ has natural density zero if
    $|B \cap \{0, \ldots, N-1\}| / N \to 0$ as $N \to \infty$. -/
def HasNaturalDensityZero (B : Set ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (((Finset.range N).filter (· ∈ B)).card : ℝ) / (N : ℝ) < ε

/--
**Erdős Problem 31** (Erdős–Straus, proved by Lorentz [Lo54]):

Given any infinite set $A \subset \mathbb{N}$, there exists a set $B \subseteq \mathbb{N}$
of natural density $0$ such that $A + B$ contains all except finitely many natural numbers.
-/
@[category research solved, AMS 11]
theorem erdos_31 (A : Set ℕ) (hA : A.Infinite) :
    ∃ B : Set ℕ, HasNaturalDensityZero B ∧
      Set.Finite {n : ℕ | n ∉ sumset A B} := by
  sorry

end Erdos31
