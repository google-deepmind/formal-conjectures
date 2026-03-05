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
# Erdős Problem 871

*Reference:* [erdosproblems.com/871](https://www.erdosproblems.com/871)

If $A$ is an additive basis of order $2$ whose representation function tends to infinity,
can $A$ always be partitioned into two disjoint additive bases of order $2$?

[ErNa88] Erdős, P. and Nathanson, M.B., *Partitions of bases into disjoint unions of bases*,
J. Number Theory (1988).

[ErNa89] Erdős, P. and Nathanson, M.B., *Sets of natural numbers with no minimal asymptotic
bases*, Proc. Amer. Math. Soc. (1989).
-/

open Classical Filter

open scoped Topology

namespace Erdos871

/-- The sumset $A + A = \{a + b : a, b \in A\}$. -/
def sumset (A : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ a ∈ A, ∃ b ∈ A, n = a + b}

/-- $A \subseteq \mathbb{N}$ is an additive basis of order $2$ if every sufficiently large
natural number can be written as the sum of two elements of $A$. -/
def IsAdditiveBasis2 (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, n ∈ sumset A

/-- The representation function $r_A(n) = |\{a \in \{0, \ldots, n\} : a \in A \land n - a \in A\}|$,
i.e., the number of ways to write $n$ as a sum of two elements of $A$. -/
noncomputable def repCount (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ (n - a) ∈ A)).card

/--
Erdős Problem 871 (DISPROVED) [ErNa88]:

Let $A \subseteq \mathbb{N}$ be an additive basis of order $2$, and suppose
$1_A * 1_A(n) \to \infty$ as $n \to \infty$ (i.e., the number of representations
of $n$ as a sum of two elements of $A$ tends to infinity). Can $A$ be partitioned
into two disjoint additive bases of order $2$?

Erdős and Nathanson proved this is true if $1_A * 1_A(n) > c \log n$ for some
$c > (\log(4/3))^{-1}$. They also proved [ErNa89] that for every $t$ there exists
a basis $A$ of order $2$ with $1_A * 1_A(n) \geq t$ for all large $n$ that cannot
be partitioned into two disjoint additive bases.

Disproved by Larsen using Claude Opus 4.5 — only a small modification of
the argument of [ErNa89] is required.
-/
@[category research solved, AMS 11]
theorem erdos_871 : answer(False) ↔
    ∀ A : Set ℕ, IsAdditiveBasis2 A ∧
      Tendsto (fun n => (repCount A n : ℝ)) atTop atTop →
      ∃ A₁ A₂ : Set ℕ,
        A₁ ∪ A₂ = A ∧ Disjoint A₁ A₂ ∧
        IsAdditiveBasis2 A₁ ∧ IsAdditiveBasis2 A₂ := by
  sorry

end Erdos871
